-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/KeepsWalk.lean: tools, no theorem. For a constant f whose type ends in a block
or in a routine over blocks (Blk, SubM, LinkM, or StateT written out):
 - keeps_stmt% f is the statement "for all arguments, KeepsM (f arguments)"; for each argument that
   is itself such a routine, or a function into one, the statement takes the hypothesis that it is
   KeepsM at all its arguments;
 - keeps_had f checks that the statement stands already, by instances alone;
 - keeps_walk f states it as an instance (named walked_ and f's name in one word) and proves it by
   unfolding f and the tactic keepsM; keeps_walk_fn does so for a routine that is written as a
   function of its state; keeps_walk_rec by the induction that follows f's own recursion, and
   keepsM;
 - keeps_find M1 M2 .. lists, for the modules whose names begin with one of the given names (tests
   apart), the constants of that kind in an order in which each comes after those that it calls,
   tries the four commands on each in that order, and prints which went through (H, W, F, R) or that
   none did (S), and a table by module. What it adds to the environment ends with its own file: what
   counts is a file that holds the lines (OnBytes/Tie/Pv/Keeps/KeepsModel.lean).
-/
import OnBytes.Tie.Pv.Keeps.KeepsLift
import Lean

open Lean Meta Elab Term Command

namespace OnBytes.L5

/-- `isStackFn` with a bound on the number of layers that are looked through. At the bound 0 the
answer is false. For a constant's own type no statement is then made: keeps_stmt% fails, and
keeps_find passes the constant over. For an argument's type the statement is made without the
hypothesis on that argument. -/
def isStackFnAt : Nat → Expr → MetaM Bool
  | 0, _ => pure false
  | k + 1, m => do
    let m ← whnfR m
    let args := m.getAppArgs
    if m.getAppFn.isConstOf ``StateT && args.size == 2 then
      if args[0]!.isConstOf ``OnBytes.Ctx then pure true else isStackFnAt k args[1]!
    else pure false

/-- True if m is Blk written out, or StateT over such a monad, through at most sixteen layers. -/
def isStackFn (m : Expr) : MetaM Bool := isStackFnAt 16 m

/-- True if t is such a monad applied to a type. -/
def isStackApp (t : Expr) : MetaM Bool := do
  let t ← whnfR t
  let args := t.getAppArgs
  if t.getAppFn.isConstOf ``StateT && args.size == 3 then
    isStackFn (mkApp2 t.getAppFn args[0]! args[1]!)
  else pure false

/-- The statement for the constant n; nothing if its type does not end in such a monad. -/
def keepsStatement (n : Name) : MetaM (Option Expr) := do
  let ci ← getConstInfo n
  unless ci.levelParams.isEmpty do return none
  withReducible <| forallTelescopeReducing ci.type fun xs body => do
    unless ← isStackApp body do return none
    let mut hts : Array Expr := #[]
    for x in xs do
      let h? ← forallTelescopeReducing (← inferType x) fun ys b => do
        if ← isStackApp b then
          pure (some (← mkForallFVars ys (← mkAppM ``KeepsM #[mkAppN x ys])))
        else pure none
      if let some h := h? then hts := hts.push h
    let concl ← mkAppM ``KeepsM #[mkAppN (mkConst n) xs]
    let decls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      hts.mapIdx fun i t => ((`hk).appendIndexAfter i, BinderInfo.instImplicit, fun _ => pure t)
    withLocalDecls decls fun hs => do pure (some (← mkForallFVars (xs ++ hs) concl))

elab "keeps_stmt% " id:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  match ← keepsStatement n with
  | some e => pure e
  | none => throwError "{n}: the type does not end in a block or a routine over blocks"

/-- The name of the instance for the constant n: one word, so that it opens no namespace. -/
def walkedName (n : Name) : Name := Name.mkSimple ("walked_" ++ n.toString.replace "." "_")

/-- The fact stands already. -/
macro "keeps_had " id:ident : command =>
  `(example : keeps_stmt% $id := by intros; infer_instance)

/-- By unfolding. -/
macro "keeps_walk " id:ident : command =>
  `(instance $(mkIdent (walkedName id.getId)):ident : keeps_stmt% $id := by
      intros; unfold $id; keepsM; done)

/-- For a routine that is written as a function of its state. -/
macro "keeps_walk_fn " id:ident : command =>
  `(instance $(mkIdent (walkedName id.getId)):ident : keeps_stmt% $id := by
      intros; unfold $id; apply KeepsM.fn; keepsM; done)

/-- By the induction that follows the routine's own recursion. -/
macro "keeps_walk_rec " id:ident : command =>
  `(instance $(mkIdent (walkedName id.getId)):ident : keeps_stmt% $id := by
      intros; fun_induction $id:ident <;> keepsM <;> done)

/-- Runs a command; true if it logged no error. Unless keep, the environment is put back. -/
def tryCommand (stx : Syntax) (keep : Bool) : CommandElabM (Bool × String) := do
  let saved ← get
  modify fun st => { st with messages := {} }
  let threw ← try elabCommand stx; pure false catch _ => pure true
  let st ← get
  if threw then
    set saved
    pure (false, "an exception")
  else if st.messages.hasErrors then
    let errs := st.messages.toList.filter (·.severity == .error)
    let txt ← match errs.head? with
      | some e => e.data.toString
      | none => pure ""
    set saved
    pure (false, txt)
  else
    if keep then modify fun st => { st with messages := saved.messages } else set saved
    pure (true, "")

def moduleOf' (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => env.header.mainModule

def bodyOf (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- `order` with a bound on the depth of the walk from a name to the names that it uses. At the
bound 0 the name is left as it is, neither marked nor listed. -/
def orderAt (env : Environment) (cand : NameSet) :
    Nat → Name → NameSet × Array Name → NameSet × Array Name
  | 0, _, s => s
  | k + 1, n, s =>
    if s.1.contains n then s
    else
      let s := (s.1.insert n, s.2)
      let used := ((env.find? n).bind bodyOf).map (·.getUsedConstants) |>.getD #[]
      -- through the auxiliary definitions that Lean makes under a name
      let s := used.foldl (fun s m =>
        if cand.contains m || n.isPrefixOf m then orderAt env cand k m s else s) s
      if cand.contains n then (s.1, s.2.push n) else s

/-- n after all candidates that it names, down to a depth of 100000. It serves the list of
`keeps_find` alone. That command calls it for every candidate, so a candidate that lay deeper is
still listed, but after the one at the bound that names it. -/
def order (env : Environment) (cand : NameSet) (n : Name)
    (s : NameSet × Array Name) : NameSet × Array Name :=
  orderAt env cand 100000 n s

elab "keeps_find " pre:ident* : command => do
  let env ← getEnv
  let pres := pre.map (·.getId)
  let mut cand : NameSet := {}
  let mut fields : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal || (bodyOf ci).isNone then continue
    let md := moduleOf' env n
    unless pres.any (·.isPrefixOf md) do continue
    if (md.components.getLast!.toString).startsWith "Test" then continue
    if (← liftCoreM (findDeclarationRanges? n)).isNone then continue
    if (← liftTermElabM (keepsStatement n)).isNone then continue
    if env.isProjectionFn n then fields := fields.push n else cand := cand.insert n
  let sorted := (cand.toList.toArray.qsort fun a b =>
    (moduleOf' env a).toString < (moduleOf' env b).toString ||
      (moduleOf' env a == moduleOf' env b && a.toString < b.toString))
  let ordered := (sorted.foldl (fun s n => order env cand n s) (({} : NameSet), #[])).2
  let mut lines : Array String := #[]
  let mut stuck : Array (Name × String) := #[]
  let mut had : Nat := 0
  for n in ordered do
    let id := mkIdent n
    if (← tryCommand (← `(keeps_had $id)) false).1 then
      had := had + 1
      lines := lines.push s!"H:{n}"
    else if (← tryCommand (← `(keeps_walk $id)) true).1 then
      lines := lines.push s!"W:{n}"
    else if (← tryCommand (← `(keeps_walk_fn $id)) true).1 then
      lines := lines.push s!"F:{n}"
    else
      let r ← tryCommand (← `(keeps_walk_rec $id)) true
      if r.1 then lines := lines.push s!"R:{n}"
      else
        let r1 ← tryCommand (← `(keeps_walk $id)) false
        stuck := stuck.push (n, r1.2)
        lines := lines.push s!"S:{n}"
  logInfo m!"candidates {ordered.size}; had {had}; stuck {stuck.size}; fields of structures (not tried) {fields}"
  for (n, e) in stuck do
    logInfo m!"STUCK {n}:\n{(e.take 300)}"
  -- the list, some names to a line: H had, W by unfolding, F as a function of the state, R by
  -- induction, S stuck
  let mut row := ""
  for l in lines do
    if row.length + l.length > 300 then
      logInfo m!"LIST {row}"
      row := ""
    row := row ++ " " ++ l
  logInfo m!"LIST {row}"
  -- by module
  let mut table : Std.HashMap Name (Array String) := {}
  for (n, l) in ordered.zip lines do
    let md := moduleOf' env n
    table := table.insert md ((table.getD md #[]).push (String.singleton l.front))
  for (md, x) in table.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    let c (k : String) := (x.filter (· == k)).size
    logInfo m!"MODULE {md}: {x.size} routines: had {c "H"}, unfold {c "W"}, state {c "F"}, induction {c "R"}, stuck {c "S"}"

end OnBytes.L5
