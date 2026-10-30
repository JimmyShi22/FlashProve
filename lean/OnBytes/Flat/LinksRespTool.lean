-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksRespTool.lean: a tactic and a command that show `Resp.K` of a routine by walking
through its text.

`Resp.K x` (OnBytes/Flat/LinksRespBase.lean) says that x gives the same from two states of a
sub-proof's check that are alike. The walk is that of OnBytes/Flat/LinksKeepsTool.lean, with the
laws of that property in the place of the laws of `Over.K`: see there for how it goes. Two things
differ. At a block the property is `Over.K`, and the goal is handed to the other walk. For a named
routine f the theorem is looked for, and added, under the name `OnBytes.Flat.RespOf` ++ f.

Every theorem that the command adds is a theorem like any other: Lean's kernel checks its proof. The
code of this file is trusted for nothing.

Main definitions: the tactic `resp`; the command `resp_bank f`. What the walk does not do: a routine
that calls itself; a routine written as a function of the state, so `SubM.change`, `SubM.take` and
`SubM.ask` at a step on the state: whether such a routine has the property hangs on the step. For
these a theorem of the said name is written by hand (OnBytes/Flat/LinksRespHand.lean). Where the
walk cannot go on it raises an error, and nothing is added.

For proofs only; no module of the program imports this file.


-/
import OnBytes.Flat.LinksRespBase
import Lean

set_option autoImplicit false

namespace OnBytes.Flat.RespTool

open Lean Meta Elab

/-- The name of the theorem on the routine f. -/
def lemmaName (f : Name) : Name := `OnBytes.Flat.RespOf ++ f

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
  | ``Bind.bind => [``r_bind]
  | ``Pure.pure => [``r_pure]
  | ``Functor.map => [``r_map]
  | ``ite => [``r_ite]
  | ``dite => [``r_dite]
  | ``ForIn.forIn => [``r_forIn_list, ``r_forIn_array, ``r_forIn_range]
  | ``List.foldlM => [``r_foldlM_list]
  | ``Array.foldlM => [``r_foldlM_array]
  | ``List.forM => [``r_forM_list]
  | ``List.mapM => [``r_mapM_list]
  | ``Array.mapM => [``r_mapM_array]
  | ``StateT.lift => [``r_lift_sub, ``r_lift]
  | ``MonadLift.monadLift => [``r_monadLift_sub, ``r_monadLift]
  | ``MonadLiftT.monadLift => [``r_liftT_refl, ``r_liftT_step]
  | ``MonadState.get => [``r_get]
  | ``MonadState.set => [``r_set]
  | ``modify => [``r_modify]
  | ``MonadState.modifyGet => [``r_modifyGet]
  | ``StateT.run => [``r_run]
  | _ => []

/-- Tries to apply one of the constants. -/
def applyFirst (g : MVarId) : List Name → MetaM (Option (List MVarId))
  | [] => pure none
  | n :: ns => do
    let r ← observing? (do g.apply (← mkConstWithFreshMVarLevels n))
    match r with
    | some gs => pure (some gs)
    | none => applyFirst g ns

/-- Tries to apply a hypothesis that ends in `Resp.K`. -/
def applyLocal (g : MVarId) : MetaM (Option (List MVarId)) := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if (t.getForallBody.isAppOf ``Resp.K) then
      if let some gs ← observing? (g.apply d.toExpr) then return some gs
  return none

/-- The statement on the routine f; none if f does not end in a monad above `Blk`. -/
def statementOf (f : Name) : MetaM (Option Expr) := do
  let info ← getConstInfo f
  let us := info.levelParams.map mkLevelParam
  forallTelescope info.type fun xs _ => do
    let some k ← observing? (mkAppM ``Resp.K #[mkAppN (mkConst f us) xs]) | return none
    let mut hyps : Array Expr := #[]
    for x in xs do
      let tx ← inferType x
      let h ← forallTelescope tx fun ys _ => do
        match ← observing? (mkAppM ``Resp.K #[mkAppN x ys]) with
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
    unless t.isAppOfArity ``Resp.K 5 do
      return ← stuck g inside "not a goal of the walk"
    let e := t.appArg!.cleanupAnnotations
    let again (e' : Expr) : MetaM Bool := do
      let g' ← g.replaceTargetDefEq (mkApp t.appFn! e')
      walk fuel (.goal create inside g')
    let all (gs : List MVarId) : MetaM Bool := do
      for g' in gs do
        discard (walk fuel (.goal create inside g'))
      return true
    -- A block does not see the state: the property is `Over.K`, and the other walk shows it.
    if ← isDefEq (t.getArg! 0) (mkConst ``OnBytes.Blk) then
      if let some gs ← applyLocal g then
        return ← all gs
      let g' ← g.replaceTargetDefEq (← mkAppM ``Over.K #[t.appArg!])
      return ← KeepsTool.walk fuel (.goal false inside g')
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .letE _ _ v b _ => again (mkAppN (b.instantiate1 v) args).headBeta
    | .mdata _ b => again (mkAppN b args).headBeta
    | .lam .. =>
      if args.isEmpty then
        match ← applyFirst g [``r_fun] with
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

/-- `resp`: closes a goal `Resp.K x` by the walk, with the hypotheses at hand. Adds no theorem. -/
elab "resp" : tactic => do
  let g ← Tactic.getMainGoal
  discard (walk depth (.goal false `here g))
  Tactic.replaceMainGoal []

/-- `resp_bank f`: adds the theorem on f and on every named routine that f's text reaches. -/
elab "resp_bank " f:ident : command => do
  let n ← Command.liftCoreM (realizeGlobalConstNoOverloadWithInfo f)
  Command.liftTermElabM do
    unless ← walk depth (.thm n) do throwError "no theorem on {n}"

end OnBytes.Flat.RespTool
