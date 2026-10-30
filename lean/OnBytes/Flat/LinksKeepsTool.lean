-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksKeepsTool.lean: a tactic and a command that show `Over.K` of a routine by walking
through its text.

`Over.K x` (OnBytes/Flat/LinksKeepsBase.lean) says that x leaves the two flags of a run as they are.
A routine of the model's checks is put together from others by a few means: one after another, a
returned value, a choice, a match, a loop, a lift from the layer below, a local definition. For each
of these a law of that file passes the property on. The walk applies them until it meets a named
routine. For a named routine f it looks for a theorem of the name `OnBytes.Flat.KeepsOf` ++ f (or,
as in OnBytes/Iop/DrySizes.lean, f's name with `keeps_` before its last part).
If there is none, the command states that theorem, proves it by the same walk through f's own text,
and adds it; the tactic goes on through f's text in place.

Every theorem that the command adds is a theorem like any other: Lean's kernel checks its proof.
The code of this file is trusted for nothing.

Main definitions: the tactic `keeps`; the command `keeps_bank f`, which adds the theorem for f and
for every named routine that f's text reaches.
The statement that the command makes for `f : (x₁ : A₁) → … → m β` is
`∀ x₁ …, (one hypothesis for each xᵢ that is itself a routine or a function to routines: Over.K of
it at all arguments) → Over.K (f x₁ …)`.
What the walk does not do: a routine that calls itself, and a block written as a function of the
context. For these a theorem of the said name is written by hand. Where the walk cannot go on it
raises an error, and nothing is added. The walk's own depth is bounded by a number (`depth`).

For proofs only; no module of the program imports this file.


-/
import OnBytes.Flat.LinksKeepsBase
import Lean

set_option autoImplicit false

namespace OnBytes.Flat.KeepsTool

open Lean Meta Elab

/-- The name of the theorem on the routine f. -/
def lemmaName (f : Name) : Name := `OnBytes.Flat.KeepsOf ++ f

/-- The name that OnBytes/Iop/DrySizes.lean gives its theorem on the block f. -/
def olderName : Name → Name
  | .str p s => .str p ("keeps_" ++ s)
  | n => n

/-- Whether a definition's compiled value calls a recursor: the routine calls itself. -/
def looksRecursive (v : Expr) : Bool :=
  (v.find? fun e =>
    match e with
    | .const (.str _ s) _ => s == "brecOn" || s == "rec" || s == "fix" || s == "recOn"
    | _ => false).isSome

/-- Raises an error at a place where the walk cannot go on. inside: the routine whose text is walked
through. -/
def stuck {α : Type} (g : MVarId) (inside : Name) (why : String) : MetaM α := do
  let t ← instantiateMVars (← g.getType)
  let s := toString (← g.withContext (ppExpr t))
  throwError "the walk cannot go on: [{inside}] {why}: {s.take 300}"

/-- The laws to try for a head symbol. -/
def lawsFor : Name → List Name
  | ``Bind.bind => [``k_bind]
  | ``Pure.pure => [``k_pure]
  | ``Functor.map => [``k_map]
  | ``ite => [``k_ite]
  | ``dite => [``k_dite]
  | ``ForIn.forIn => [``k_forIn_list, ``k_forIn_array, ``k_forIn_range]
  | ``List.foldlM => [``k_foldlM_list]
  | ``Array.foldlM => [``k_foldlM_array]
  | ``List.forM => [``k_forM_list]
  | ``List.mapM => [``k_mapM_list]
  | ``Array.mapM => [``k_mapM_array]
  | ``StateT.lift => [``k_lift]
  | ``MonadLift.monadLift => [``k_monadLift]
  | ``MonadLiftT.monadLift => [``k_liftT_refl, ``k_liftT_step]
  | ``MonadState.get => [``k_get]
  | ``MonadState.set => [``k_set]
  | ``modify => [``k_modify]
  | ``MonadState.modifyGet => [``k_modifyGet]
  | ``StateT.run => [``k_run]
  | _ => []

/-- Tries to apply one of the constants. -/
def applyFirst (g : MVarId) : List Name → MetaM (Option (List MVarId))
  | [] => pure none
  | n :: ns => do
    let r ← observing? (do g.apply (← mkConstWithFreshMVarLevels n))
    match r with
    | some gs => pure (some gs)
    | none => applyFirst g ns

/-- Tries to apply a hypothesis that ends in `Over.K`. -/
def applyLocal (g : MVarId) : MetaM (Option (List MVarId)) := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if (t.getForallBody.isAppOf ``Over.K) then
      if let some gs ← observing? (g.apply d.toExpr) then return some gs
  return none

/-- The statement on the routine f; none if f does not end in a monad above `Blk`. -/
def statementOf (f : Name) : MetaM (Option Expr) := do
  let info ← getConstInfo f
  let us := info.levelParams.map mkLevelParam
  forallTelescope info.type fun xs _ => do
    let some k ← observing? (mkAppM ``Over.K #[mkAppN (mkConst f us) xs]) | return none
    let mut hyps : Array Expr := #[]
    for x in xs do
      let tx ← inferType x
      let h ← forallTelescope tx fun ys _ => do
        match ← observing? (mkAppM ``Over.K #[mkAppN x ys]) with
        | some kx => some <$> mkForallFVars ys kx
        | none => pure none
      if let some h := h then hyps := hyps.push h
    let body := hyps.foldr (fun h b => mkForall `h .default h b) k
    some <$> mkForallFVars xs body

/-- What the walk is asked for: to close a goal (create: whether theorems on named routines are
added; inside: the routine whose text is walked through, for the errors), or to add the theorem on
a named routine. -/
inductive Job where
  | goal (create : Bool) (inside : Name) (g : MVarId)
  | thm (f : Name)

/-- **The walk.** The first argument bounds the depth of the walk: each step takes one off, and at 0
an error is raised that names the routine. For a goal: closes it or raises an error. For a named
routine f: adds the theorem on f, if it can be stated and f has a text that does not call itself;
returns whether the theorem is there. -/
def walk : Nat → Job → MetaM Bool
  | 0, .goal _ inside _ => throwError "the walk is out of fuel inside {inside}"
  | 0, .thm f => throwError "the walk is out of fuel at {f}"
  | fuel + 1, .goal create inside g => g.withContext do
    let t := (← instantiateMVars (← g.getType)).cleanupAnnotations
    if t.isForall then
      let (_, g') ← g.intros
      return ← walk fuel (.goal create inside g')
    unless t.isAppOfArity ``Over.K 5 do
      return ← stuck g inside "not a goal of the walk"
    let e := t.appArg!.cleanupAnnotations
    let again (e' : Expr) : MetaM Bool := do
      let g' ← g.replaceTargetDefEq (mkApp t.appFn! e')
      walk fuel (.goal create inside g')
    let all (gs : List MVarId) : MetaM Bool := do
      for g' in gs do
        discard (walk fuel (.goal create inside g'))
      return true
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .letE _ _ v b _ => again (mkAppN (b.instantiate1 v) args).headBeta
    | .mdata _ b => again (mkAppN b args).headBeta
    | .lam .. =>
      if args.isEmpty then
        match ← applyFirst g [``k_fun] with
        | some gs => all gs
        | none => stuck g inside "a function of the context"
      else again e.headBeta
    | .const n us =>
      if let some gs ← applyLocal g then
        return ← all gs
      if let some gs ← applyFirst g (lawsFor n) then
        return ← all gs
      if (← getEnv).contains (olderName n) then
        if let some gs ← applyFirst g [olderName n] then
          return ← all gs
      if (← getEnv).contains (lemmaName n) then
        match ← applyFirst g [lemmaName n] with
        | some gs => return ← all gs
        | none => return ← stuck g inside s!"the theorem on {n} does not apply"
      if (← isMatcher n) then
        match ← observing? (splitTarget? g) with
        | some (some gs) => return ← all gs
        | _ => return ← stuck g inside "a match that does not split"
      if (← getEnv).isProjectionFn n then
        match ← unfoldDefinition? e with
        | some e' =>
          let e'' ← whnfCore e'
          if e''.getAppFn.isProj then return ← stuck g inside "a field of a record"
          else return ← again e''
        | none => return ← stuck g inside "a field of a record"
      if create then
        if ← walk fuel (.thm n) then
          match ← applyFirst g [lemmaName n] with
          | some gs => return ← all gs
          | none => pure ()
      let info ← getConstInfo n
      match info with
      | .defnInfo d =>
        if looksRecursive d.value then stuck g inside s!"{n} calls itself"
        else again ((d.value.instantiateLevelParams d.levelParams us).beta args)
      | _ => stuck g inside s!"{n} has no text"
    | _ =>
      if let some gs ← applyLocal g then
        return ← all gs
      stuck g inside "no named routine at the head"
  | fuel + 1, .thm f => do
    if (← getEnv).contains (lemmaName f) then return true
    let .defnInfo d ← getConstInfo f | return false
    if looksRecursive d.value then return false
    let some stmt ← statementOf f | return false
    let mv ← mkFreshExprMVar (some stmt)
    let (_, g) ← mv.mvarId!.intros
    g.withContext do
      let t ← instantiateMVars (← g.getType)
      let e := t.appArg!
      let us := d.levelParams.map mkLevelParam
      let e' := (d.value.instantiateLevelParams d.levelParams us).beta e.getAppArgs
      let g' ← g.replaceTargetDefEq (mkApp t.appFn! e')
      discard (walk fuel (.goal true f g'))
    let pf ← instantiateMVars mv
    addDecl (.thmDecl
      { name := lemmaName f, levelParams := d.levelParams, type := stmt, value := pf })
    return true

/-- The depth that the tactic and the command allow. -/
def depth : Nat := 1000000

/-- `keeps`: closes a goal `Over.K x` by the walk, with the hypotheses at hand. Adds no theorem. -/
elab "keeps" : tactic => do
  let g ← Tactic.getMainGoal
  discard (walk depth (.goal false `here g))
  Tactic.replaceMainGoal []

/-- `keeps_bank f`: adds the theorem on f and on every named routine that f's text reaches. -/
elab "keeps_bank " f:ident : command => do
  let n ← Command.liftCoreM (realizeGlobalConstNoOverloadWithInfo f)
  Command.liftTermElabM do
    unless ← walk depth (.thm n) do throwError "no theorem on {n}"

end OnBytes.Flat.KeepsTool
