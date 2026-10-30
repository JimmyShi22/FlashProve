-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Laws/LawAuto.lean: a command that walks whole modules of the program:
walk_modules M1 M2 ...

For each definition of these modules whose type ends in `Blk`, or in one or two layers of state over
`Blk` (SubM, PlaceM, LinkM: OnBytes/TypedOracleCompiler/Laws/LawState.lean), in the order of the text, it states
  ∀ G d (the definition's arguments), Same or SameS or SameL (Alike G d) (the definition at these)
and tries, in this order: an instance that stands already ("had"); "unfold; walkAll" ("unfold"); an
induction along the definition's own recursion (fun_induction), each case by walkAll ("induction").
What is proved is added as a theorem auto.<name> and as an instance, so that later definitions find
it. What is not proved is printed with the first goal that is left ("STUCK"), and nothing is added
for it.

Why. The program has some hundreds of routines, and each proof is the same two lines.

Against a false green. The tactics run without error recovery and without "error to sorry"; a term
that holds a sorry or a hole is refused before it is added; what is added goes through Lean's kernel
(addDecl) under a name in OnBytes.TwoLaws, so a print of the axioms of a theorem that uses it covers
it. What this does not guard. A proof that leans on an axiom, or on a theorem that itself rests on a
sorry, is not refused (the test reads the term alone): only such a print would show it. The hook
walk_more is open: any later file can add any tactic to walkAll by macro_rules. The command prints
names and ways, and for a STUCK routine the first goal that is left or the error; it never prints a
statement that it adds. STUCK, WALKPASSED and a walk of no module are lines of a message: they fail
no build.

An argument that is itself a block, or a function into blocks, gets the like statement as a
hypothesis (an instance argument): the law of such a routine is conditional.

What is passed over is printed: each definition of the walked modules whose type names Blk, StateT,
SubM, LinkM or PlaceM anywhere and for which nothing is stated gets a line WALKPASSED with the
cause: private; without a body that Lean shows; a record's field; no place in the text; a type that
does not end in a block, or universe parameters. Their number stands in the sum line. Passed over
without a line: every definition for which nothing is stated and whose type names none of these
five; the compiler's own helpers (matchers; names with a part that begins with _; casesOn, recOn,
noConfusion, brecOn, below, ctorIdx, ctorElim and the like beside a record or an inductive type);
whatever is neither a definition nor a constant without a body that Lean shows (theorems, axioms,
inductive types, their constructors and recursors); a module that is not imported; and a module
beneath a name given, not itself given, whose last name begins with Test or ends in Laws.

Two builds can be compared by a sum: a second message lists every routine by name, sorted, one short
line each (WALKLINE name how), then the lines WALKPASSED.

Not claimed. Nothing on a routine that runs a block out of a record's field: it is STUCK here.

-/
import OnBytes.TypedOracleCompiler.Laws.LawTail
import OnBytes.TypedOracleCompiler.Laws.LawState
import Lean

namespace OnBytes.TwoLaws

open Lean Meta Elab Tactic Command

/-- A hook: steps that later files add to the tactic walkAll (by macro_rules). At first: none. -/
syntax "walk_more" : tactic
macro_rules | `(tactic| walk_more) => `(tactic| fail "no further step")

/-- A loop whose body no instance reaches (it holds a match or an if): the rule for the loop is
applied, and the body is left as a goal. -/
macro "walk_loop" : tactic =>
  `(tactic| first
      | with_reducible apply Same.forIn_list'
      | with_reducible apply Same.forIn_array'
      | with_reducible apply Same.forIn_range'
      | with_reducible apply Same.foldlM_list'
      | with_reducible apply Same.foldlM_array'
      | with_reducible apply Same.forM_list'
      | with_reducible apply Same.forM_array'
      | with_reducible apply Same.mapM_list'
      | with_reducible apply Same.mapM_array'
      | with_reducible apply SameS.forIn_list'
      | with_reducible apply SameS.forIn_array'
      | with_reducible apply SameS.forIn_range'
      | with_reducible apply SameS.foldlM_list'
      | with_reducible apply SameS.foldlM_array'
      | with_reducible apply SameS.forM_list'
      | with_reducible apply SameS.forM_array'
      | with_reducible apply SameS.mapM_list'
      | with_reducible apply SameS.mapM_array'
      | with_reducible apply SameL.forIn_list'
      | with_reducible apply SameL.forIn_array'
      | with_reducible apply SameL.forIn_range'
      | with_reducible apply SameL.foldlM_list'
      | with_reducible apply SameL.foldlM_array'
      | with_reducible apply SameL.forM_list'
      | with_reducible apply SameL.forM_array'
      | with_reducible apply SameL.mapM_list'
      | with_reducible apply SameL.mapM_array')

/-- The tactic walkB (OnBytes/TypedOracleCompiler/Laws/LawTail.lean) with the hook walk_more before the steps on a
bind, the binds of the two layers of state, the loops, and at the very end a step down a layer of
state (for a routine that is written as a function of the state). -/
macro "walkAll" : tactic =>
  `(tactic| repeat' first
      | infer_instance
      | intro _
      | walk_more
      | (with_reducible refine same_of_close _ _ _ (fun _ _ _ _ _ => ?_); try dsimp only
         refine Carries.of_same ?_)
      | (with_reducible refine same_of_theBook (fun _ _ hB => ?_); simp only [linAlone_alike hB]
         refine Carries.of_same ?_)
      | with_reducible apply Same.bind
      | with_reducible apply SameS.bind
      | with_reducible apply SameL.bind
      | walk_loop
      | exact SameS.out _
      | exact SameL.out _
      | split
      | dsimp only
      | refine SameL.mk fun _ => ?_
      | refine SameS.mk fun _ => ?_)

/-- True for what Lean itself makes beside a structure or an inductive type. -/
def ownOffspring (c : Name) : Bool :=
  match c with
  | .str _ s => ["casesOn", "recOn", "rec", "noConfusion", "noConfusionType", "brecOn", "binductionOn",
      "below", "ibelow", "ctorIdx", "toCtorIdx", "ctorElim", "ctorElimType"].contains s
  | _ => false

/-- True if the type names Blk, StateT, or one of the program's three names for layers of state over
Blk. -/
def namesBlock (e : Expr) : Bool :=
  (e.find? fun x => x.isConstOf ``Blk || x.isConstOf ``StateT ||
    x.isConstOf `OnBytes.Model.SubM || x.isConstOf `OnBytes.Model.LinkM ||
    x.isConstOf `OnBytes.Attention.PlaceM).isSome

/-- `layersOf` with a bound on the number of layers that are looked through. -/
def layersFuel : Nat → Expr → MetaM (Option Nat)
  | 0, _ => pure none
  | n + 1, body => do
    let b ← whnfR body
    match b.getAppFnArgs with
    | (``StateT, #[s, m, a]) =>
      if s.isConstOf ``Ctx then pure (some 0)
      else
        match ← layersFuel n (mkApp m a) with
        | some k => pure (some (k + 1))
        | none => pure none
    | _ => pure none

/-- How many layers of state lie over Blk in the type: 0 for Blk α, 1 for StateT σ Blk α (SubM,
PlaceM), 2 for StateT σ (StateT τ Blk) α (LinkM). Nothing for another type, and for more than three
layers. -/
def layersOf (body : Expr) : MetaM (Option Nat) := layersFuel 4 body

/-- The statement for a definition whose type ends in Blk. -/
def stmtOf (c : Name) : MetaM (Option Expr) := do
  let info ← getConstInfo c
  unless info.levelParams.isEmpty do return none
  forallTelescope info.type fun xs body => do
    let some k ← layersOf body | return none
    let cls := if k == 0 then ``Same else if k == 1 then ``SameS else ``SameL
    if k > 2 then return none
    let ba := mkConst ``ByteArray
    let gT ← mkArrow ba (← mkArrow ba (← mkArrow ba (← mkArrow ba (mkSort levelZero))))
    withLocalDecl `G .implicit gT fun G =>
      withLocalDecl `d .implicit (mkConst ``Bool) fun d => do
        let R ← mkAppM ``Alike #[G, d]
        let s ← mkAppM cls #[R, mkAppN (mkConst c) xs]
        -- an argument that is itself a block, or a function into blocks, gets a hypothesis
        let mut hyps : Array Expr := #[]
        for x in xs do
          let h ← forallTelescope (← inferType x) fun ys b => do
            match ← layersOf b with
            | some j =>
              if j > 2 then pure none
              else
                let cj := if j == 0 then ``Same else if j == 1 then ``SameS else ``SameL
                pure (some (← mkForallFVars ys (← mkAppM cj #[R, mkAppN x ys])))
            | none => pure none
          if let some h := h then hyps := hyps.push h
        let body ← hyps.foldrM (fun h acc => pure (mkForall `inst .instImplicit h acc)) s
        return some (← mkForallFVars (#[G, d] ++ xs) body)

/-- Runs a tactic on the statement. The proof, or the first goal that is left. Each attempt has its
own count of heartbeats; a timeout or too deep a recursion counts as a failure of the attempt. -/
def attempt (stmt : Expr) (tac : TSyntax `tactic) : TermElabM (Except String Expr) := do
  let s ← saveState
  tryCatchRuntimeEx
    (withCurrHeartbeats do
      let m ← mkFreshExprMVar stmt
      let gs ← Term.withoutErrToSorry (Tactic.run m.mvarId! (Tactic.withoutRecover (evalTactic tac)))
      match gs with
      | [] =>
        Term.synthesizeSyntheticMVarsNoPostponing
        let p ← instantiateMVars m
        if p.hasSorry || p.hasExprMVar then
          s.restore
          return .error "the term holds a sorry or a hole"
        return .ok p
      | g :: _ =>
        let f ← g.withContext do
          let t ← instantiateMVars (← g.getType)
          pure (((← ppExpr t).pretty 200).replace "\n" " ")
        s.restore
        return .error s!"{gs.length} goals left; the first: {f.take 400}")
    (fun e => do
      let msg ← e.toMessageData.toString
      s.restore
      return .error s!"error: {msg.take 300}")

syntax (name := walkModules) "walk_modules " ident+ : command

/-- walk_modules M1 M2 ...: the modules named, and every imported module of which a name given is a
proper prefix, but for those whose last name begins with Test or ends in Laws; in the order of the
imports, each in the order of its text. -/
@[command_elab walkModules] def elabWalkModules : CommandElab := fun stx => do
  let given := stx[1].getArgs.map (·.getId)
  let env ← getEnv
  let mods := env.header.moduleNames.filter fun mn =>
    given.contains mn ||
      (given.any (fun g => g.isPrefixOf mn) &&
        !(mn.getString!.startsWith "Test") && !(mn.getString!.endsWith "Laws"))
  let mut todo : Array (Nat × Nat × Name) := #[]
  let mut passed : Array String := #[]
  for (c, i) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mn := env.header.moduleNames[idx.toNat]!
    let some k := mods.idxOf? mn | continue
    unless (i matches .defnInfo _) || (i matches .opaqueInfo _) do continue
    -- the compiler's own helpers (matchers, unfolding helpers and the like) are no definitions of
    -- the text
    let user := (privateToUserName? c).getD c
    if user.isInternal || Lean.Meta.isMatcherCore env c || ownOffspring c then continue
    let names := namesBlock i.type
    if (privateToUserName? c).isSome then
      if names then passed := passed.push s!"{c}\tprivate"
      continue
    if i matches .opaqueInfo _ then
      if names then passed := passed.push s!"{c}\twithout a body that Lean shows"
      continue
    if env.isProjectionFn c then
      if names then passed := passed.push s!"{c}\ta record's field"
      continue
    let some r ← findDeclarationRanges? c
      | do
        if names then passed := passed.push s!"{c}\tno place in the text"
        continue
    todo := todo.push (k, r.range.pos.line, c)
  let sorted := todo.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
  let mut had := 0
  let mut byUnfold := 0
  let mut byInd := 0
  let mut stuck := 0
  let mut lines : Array String := #[]
  let mut short : Array String := #[]
  for (_, _, c) in sorted do
    let some stmt ← liftTermElabM (stmtOf c)
      | do
        if namesBlock (← getConstInfo c).type then
          passed := passed.push s!"{c}\tits type names a block but does not end in one (or has universe parameters)"
        continue
    let id := mkIdent c
    let t0 ← `(tactic| (intros; infer_instance))
    let t1 ← `(tactic| (intros; unfold $id; walkAll))
    let t2 ← `(tactic| (intros; fun_induction $id:ident <;> walkAll))
    let mut how := ""
    let mut proof : Option Expr := none
    let mut why := ""
    match ← liftTermElabM (attempt stmt t0) with
    | .ok _ => how := "had"
    | .error _ =>
      match ← liftTermElabM (attempt stmt t1) with
      | .ok p => how := "unfold"; proof := some p
      | .error e1 =>
        match ← liftTermElabM (attempt stmt t2) with
        | .ok p => how := "induction"; proof := some p
        | .error e2 => how := "STUCK"; why := s!" [unfold: {e1}] [induction: {e2}]"
    if how == "had" then had := had + 1
    if how == "unfold" then byUnfold := byUnfold + 1
    if how == "induction" then byInd := byInd + 1
    if how == "STUCK" then stuck := stuck + 1
    if let some p := proof then
      let n := `OnBytes.TwoLaws.auto ++ c
      liftCoreM <| addDecl (.thmDecl { name := n, levelParams := [], type := stmt, value := p })
      liftTermElabM <| addInstance n .global 1000
    lines := lines.push s!"{how}\t{c}{why}"
    short := short.push s!"WALKLINE\t{c}\t{how}"
  logInfo m!"WALK of {given} ({mods.size} modules): had {had}, unfold {byUnfold}, induction {byInd}, STUCK {stuck}, PASSED OVER {passed.size}\n{"\n".intercalate lines.toList}"
  -- the same by name, sorted, one short line each: two builds can be compared by a sum over these
  -- lines
  let sortedShort := short.qsort (· < ·)
  let sortedPassed := (passed.map fun s => "WALKPASSED\t" ++ s).qsort (· < ·)
  logInfo m!"LIST of the walk of {given}, by name:\n{"\n".intercalate (sortedShort ++ sortedPassed).toList}"

end OnBytes.TwoLaws
