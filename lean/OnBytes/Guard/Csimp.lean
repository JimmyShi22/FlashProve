-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import OnBytes.Guard.Basic
/-!
# Guard command 1: every rule for the compiler is a proved theorem

No proof checker sees compiled code. A rule for the compiler (Lean calls it a csimp lemma) is an
equation @f = @g that is marked csimp; in everything that is compiled after it, the compiler uses
the code of g wherever f is called. A wrong rule makes a compiled program differ from the definition
that the theorems are about. Lean accepts as a rule any declaration whose type is such an equation:
also one whose proof is sorry or rests on a declared axiom, and also a definition that is no
theorem.

#guard_csimp list floor goes through every rule that the environment has on record at that place:
those in force, and those marked scoped, whether or not their namespace is open. It fails, so that
the file does not compile, unless each rule
* is a theorem that depends on no axiom but propext, Classical.choice and Quot.sound, or
* is a rule of Lean's core or of a package, is not a theorem, has a recursor on its left side, the
  pair of that recursor and the module that declares the rule is in list, the function on its right
  side is declared in the same module, and it is the only such rule for that recursor. Allow.lean
  has the list for Mathlib (36 rules). These are trusted, not checked. The guard file of
  verify-on-bytes (Program.lean) passes the empty list, so there no rule is let through.
It also fails if fewer than floor rules of this library are on record, which guards against a check
of nothing. The guard file passes 0, because this library has no rule: there the printed count of
all rules (51 with Lean 4.29.1) is the only sign that the record was read. It prints the counts,
this library's rules (which constant is compiled as which, by which theorem), the recursors whose
rules are let through, the recursors in list that have no rule here, and the constants that have
more than one rule (the later one is in force, and Lean says nothing).

What it does not reach.
* A rule marked local in an imported file: it acted on that file's code and is not on record
  afterwards. Only a search of the source text finds it.
* A rule that is added after the command, or in a module that the file with the command does not
  import. Put the command in a file that imports all that the program imports.
* Whether the compiler applies a rule rightly, and whether the program that is run was built from
  these sources.
* "Is a theorem" means that the kernel checked it when its file was built. For Lean's core and the
  packages that rests on their compiled files as they were built or fetched.
* Code that stands in for a definition without any equation (implemented_by, extern, partial):
  Cone.lean.

These are programs that run while the library is built; nothing here is compiled into a verifier.
-/
set_option autoImplicit false

namespace OnBytes.Guard

open Lean Elab Command

/-- The rules on record, as a pair. First, the entries that are marked scoped, whether or not their
namespace is open. Second, the names of the declarations of all rules: those in force, and those
marked scoped. -/
def csimpRules (env : Environment) : Array Compiler.CSimp.Entry × Array Name :=
  let st := Compiler.CSimp.ext.getState env
  let sc : Array Compiler.CSimp.Entry :=
    (Compiler.CSimp.ext.ext.getState env).scopedEntries.map.fold
      (fun acc _ es => es.foldl (fun a e => a.push e) acc) #[]
  let names : NameSet := st.thmNames.fold (fun s n => s.insert n) {}
  let names := sc.foldl (fun s e => s.insert e.thmName) names
  (sc, names.toArray)

/-- The constant on the left side of a rule's equation. -/
def leftOf (ci : ConstantInfo) : Option Name :=
  match ci.type.eq? with
  | some (_, .const f _, _) => some f
  | _ => none

/-- The constant on the right side of a rule's equation. -/
def rightOf (ci : ConstantInfo) : Option Name :=
  match ci.type.eq? with
  | some (_, _, .const g _) => some g
  | _ => none

/-- The check. unproved lists the recursors for which one rule of Lean's core or of a package is let
through although it is not a theorem, each with the module that declares the rule; ownFloor is the
least number of rules from this library that must be on record. -/
def checkCsimp (unproved : List (Name × Name)) (ownFloor : Nat) : CommandElabM Unit := do
  let env ← getEnv
  let (sc, names) := csimpRules env
  let mut proved : Array Name := #[]
  let mut trusted : Array Name := #[]
  let mut refused : Array MessageData := #[]
  for n in names do
    match env.find? n with
    | none => refused := refused.push m!"{n}: on record as a rule, but no such constant exists"
    | some (.thmInfo _) => proved := proved.push n
    | some ci =>
      let left := (leftOf ci).getD .anonymous
      let forRecursor := match env.find? left with
        | some (.recInfo _) => true
        | _ => false
      if originOf env n == .own then
        refused := refused.push m!"{n}: a rule of this library that is not a theorem, so its \
          equation may have no proof"
      else if !forRecursor then
        refused := refused.push m!"{n}: not a theorem, and its left side is no recursor"
      else if !unproved.contains (left, moduleOf env n) then
        refused := refused.push m!"{n}: not a theorem, and the pair ({left}, {moduleOf env n}) is \
          not on the list of recursors \
          whose rule is let through unproved"
      else if moduleOf env ((rightOf ci).getD .anonymous) != moduleOf env n then
        refused := refused.push m!"{n}: not a theorem, and its right side is declared in another \
          module than the rule"
      else if trusted.contains left then
        refused := refused.push m!"{n}: a second rule that is not a theorem for {left}"
      else trusted := trusted.push left
  -- the axioms below the theorems: all together first, one by one only if something foreign shows
  let (_, s) := ((proved.forM CollectAxioms.collect).run env).run {}
  let foreign := s.axioms.filter fun a => !stdAxioms.contains a
  unless foreign.isEmpty do
    for n in proved do
      let bad := (← liftCoreM (collectAxioms n)).filter fun a => !stdAxioms.contains a
      unless bad.isEmpty do refused := refused.push m!"{n}: depends on {bad}"
  let own := proved.filter fun n => originOf env n == .own
  if own.size < ownFloor then
    refused := refused.push m!"only {own.size} rules of this library are on record, {ownFloor} or \
      more were expected"
  let mut absent : Array Name := #[]
  for (n, _) in unproved do
    unless trusted.contains n do
      absent := absent.push n
  -- two rules for one constant: the later one wins, silently
  let mut lefts : NameMap (List Name) := {}
  for n in names do
    if let some f := (env.find? n).bind leftOf then
      lefts := lefts.insert f (n :: (lefts.find? f).getD [])
  let mut twice : Array MessageData := #[]
  for (f, rs) in lefts do
    if rs.length > 1 then twice := twice.push m!"  {f}: {rs}"
  let ownLines := own.qsort Name.lt |>.toList.map fun n =>
    let ci := env.find? n
    m!"  {(ci.bind leftOf).getD .anonymous} is compiled as {(ci.bind rightOf).getD .anonymous}, \
      by {n}"
  let report := m!"rules for the compiler (csimp) on record: {names.size}, of them marked scoped: \
    {sc.size}\n\
    theorems: {proved.size}, of them from Lean's core \
    {(proved.filter fun n => originOf env n == .core).size}, from the packages \
    {(proved.filter fun n => originOf env n == .packages).size}, from this library {own.size}\n\
    THIS LIBRARY'S RULES:\n{MessageData.joinSep ownLines "\n"}\n\
    Let through unproved (rules of the packages for these recursors; not theorems; trusted, \
    not checked): {trusted.size}\n\
    {lines trusted}\n\
    On the list of recursors but without a rule here (their modules are not imported): \
    {absent.size}\n{lines absent}\n\
    Constants with more than one rule (the one declared last is in force): {twice.size}\n\
    {MessageData.joinSep twice.toList "\n"}"
  if refused.isEmpty then
    logInfo m!"{report}\nHELD: every rule on record that is a theorem depends on propext, \
      Classical.choice, Quot.sound alone, \
      and every other rule is named above"
  else
    logInfo report
    throwError "the guard on rules for the compiler (csimp) \
      refuses:\n{MessageData.joinSep refused.toList "\n"}"

/-- #guard_csimp list floor: fails unless every rule for the compiler on record is a theorem that
depends on no axiom other than propext, Classical.choice and Quot.sound. The exception: a rule of
Lean's core or of a package for a recursor named in list, under the conditions in the head of this
file. list is a term of type List (Lean.Name × Lean.Name): the recursor and the module that declares
the rule. The command also fails if fewer than floor rules of this library are on record. -/
macro "#guard_csimp " l:term:max n:term:max : command => `(run_cmd OnBytes.Guard.checkCsimp $l $n)

end OnBytes.Guard
