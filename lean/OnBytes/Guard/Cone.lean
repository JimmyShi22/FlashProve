-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import OnBytes.Guard.Basic
/-!
# Guard command 2: what stands in for a definition without an equation

For some constants the compiled code is not made from the definition that the kernel checked, and no
equation ties the two:
* implemented_by g: the compiler calls g in its place;
* extern: the compiler calls a C function;
* opaque: the constant has a value, but the kernel never unfolds it, so no theorem can use the
  value. A function written with the keyword partial reaches the kernel as an opaque constant, and
  so does a constant that is set by initialize;
* unsafe, or of the kernel's safety class partial: no theorem can speak of it;
* an axiom.
Lean's core uses extern and implemented_by for numbers, arrays, byte arrays and strings, so no
program is free of them. What can be had is the list, and the promise that this library adds nothing
to it.

#guard_cone roots allowed starts from the constants in roots (in the guard file: main) and walks
all constants that they use. The constants that the walk reaches are the cone of the roots. It
prints every constant of the cone that is of one of the kinds above, in three groups: Lean core /
Std, Mathlib and packages, this library. It fails, so that the file does not compile, if the third
group holds a constant that allowed does not name. A module that is neither Lean's nor one of the
nine packages' counts as this library's.

How it walks. From a definition, and from an opaque constant, it goes on to every constant in the
value as the kernel has it. It does not enter types, nor theorems (proofs are erased). If a rule for
the compiler replaces the constant, it also goes on to the right side of the rule; if the constant
is implemented_by g, it goes on to g. It does not enter the value of a constant that is extern or
implemented_by, because that value is not compiled.

What that means. The walk follows the kernel's terms and not the compiler's output, so it lists too
much rather than too little: parts that the compiler erases are walked too, and a recursion goes
through the type's recursor, which the compiler does not use for a function that it compiled from
its equations.

What it does not reach.
* What the C code behind an extern calls in its turn: the environment does not show it. What a
  function written with the keyword partial calls: Lean keeps that code under the name
  f._unsafe_rec, and the walk does not follow it. In this library such a constant is rejected unless
  allowed names it; in Lean's core and the packages it is a leaf of the list.
* A rule for the compiler marked local in an imported file (see Csimp.lean).
* Lean's compiler and runtime, the C compiler, and whether the program that is run was built from
  these sources.
* main itself, if a caller names other roots than main: then read main by eye.

These are programs that run while the library is built.
-/
set_option autoImplicit false

namespace OnBytes.Guard

open Lean Elab Command

/-- One constant of the cone whose compiled code is not made from its definition, or that has no
definition. -/
structure Finding where
  name : Name
  /-- why it is listed -/
  why : List String

/-- Why c is listed, if it is. -/
def whyListed (env : Environment) (c : Name) (ci : ConstantInfo) : List String :=
  (match Compiler.getImplementedBy? env c with
    | some g => [s!"implemented_by {g}"]
    | none => []) ++
  (if isExtern env c then ["extern"] else []) ++
  (match ci with
    | .opaqueInfo _ => ["opaque"]
    | .axiomInfo _ => ["axiom"]
    | _ => []) ++
  (if ci.isUnsafe then ["unsafe"] else []) ++
  (if ci.isPartial then ["partial"] else [])

/-- The constants to go on with from c. -/
def nextOf (env : Environment) (c : Name) (ci : ConstantInfo) : Array Name :=
  let replaced : Array Name :=
    (match Compiler.getImplementedBy? env c with | some g => #[g] | none => #[]) ++
    (match (Compiler.CSimp.ext.getState env).map.find? c with
      | some e => #[e.toDeclName]
      | none => #[])
  let body : Array Name :=
    if (Compiler.getImplementedBy? env c).isSome || isExtern env c then #[]
    else match ci with
      | .defnInfo v => v.value.getUsedConstants
      | .opaqueInfo v => v.value.getUsedConstants
      | _ => #[]
  replaced ++ body

/-- Walk the cone of the roots. The result is the findings and the number of constants seen. -/
def walk (env : Environment) (roots : List Name) : Except String (Array Finding × Nat) := do
  let mut seen : NameSet := roots.foldl (fun s n => s.insert n) {}
  let mut stack : Array Name := roots.toArray
  let mut out : Array Finding := #[]
  let mut count := 0
  -- a constant goes on the stack once (a root as often as roots names it), so an environment of
  -- fewer than 10^8 constants does not meet the bound; if constants are left when it is met, the
  -- walk fails below. The loop replaces a while loop
  for _ in [0:100000000] do
    match stack.back? with
    | none => break
    | some c =>
      stack := stack.pop
      count := count + 1
      match env.find? c with
      | none => throw s!"{c} does not exist"
      | some ci =>
        let why := whyListed env c ci
        unless why.isEmpty do out := out.push ⟨c, why⟩
        for n in nextOf env c ci do
          unless seen.contains n do
            seen := seen.insert n
            stack := stack.push n
  unless stack.isEmpty do throw "the walk did not end"
  return (out, count)

/-- The check. roots: in the guard file, main; allowOwn are the constants of this library that may
be listed. -/
def checkCone (roots : List Name) (allowOwn : List Name) : CommandElabM Unit := do
  let env ← getEnv
  if roots.isEmpty then throwError "the guard on the cone was given no function to start from"
  match walk env roots with
  | .error e => throwError "the guard on the cone: {e}"
  | .ok (found, count) =>
    let show1 := fun (fs : Array Finding) =>
      MessageData.joinSep ((fs.qsort fun a b => Name.lt a.name b.name).toList.map fun f => m!"  \
        {f.name}: {", ".intercalate f.why}") "\n"
    let core := found.filter fun f => originOf env f.name == .core
    let pkgs := found.filter fun f => originOf env f.name == .packages
    let own := found.filter fun f => originOf env f.name == .own
    let refused := own.filter fun f => !allowOwn.contains f.name
    logInfo m!"the cone of {roots}: {count} constants; listed are those that carry implemented_by \
      or extern, or are opaque, \
      an axiom, unsafe or partial\n\
      LEAN CORE / STD: {core.size}\n{show1 core}\n\
      MATHLIB AND PACKAGES: {pkgs.size}\n{show1 pkgs}\n\
      THIS LIBRARY: {own.size}, of them allowed by name: {own.size - refused.size}\n{show1 own}"
    for n in allowOwn do
      unless own.any fun f => f.name == n do logInfo m!"note: {n} is allowed by name but is not \
        listed in this cone"
    unless refused.isEmpty do
      throwError "the guard on the cone refuses these constants of this library:\n{show1 refused}"

/-- #guard_cone roots allowed: both are terms of type List Lean.Name. -/
macro "#guard_cone " r:term:max a:term:max : command => `(run_cmd OnBytes.Guard.checkCone $r $a)

end OnBytes.Guard
