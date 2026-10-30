-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndWalkTail.lean: the routines of the list of arrays and of the smallness test
(OnBytes/Model/Trees.lean, OnBytes/Model/Tail.lean) keep whatever the basic steps keep; with the
laws for routines that also call the chain.

Theorems with their proofs, one for each routine, each by a walk through the routine's text (`walk`,
OnBytes/Tie/Pv/Tail/EndWalk.lean). R: any relation with `Prim R`. «x keeps R»: wherever the routine
x returns, R holds from the state before to the state after (`Pres R x`, `PresL R x`).

Main names: `pres_` or `presL_` and the routine's name; `pushRuns_frame`, `t2FillL_shapes`: two
basic steps; `presL_pure`, `presL_bind`, `presL_sub`, `presL_loop` and `walkL`: the walk for
`LinkM`.

Limits: those of OnBytes/Tie/Pv/Tail/EndWalk.lean.


-/
import OnBytes.Tie.Pv.Tail.EndWalkLook
import OnBytes.Tie.Pv.Tail.EndAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Walk
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail

variable {R : Fork → Fork → Prop}

/-! ## Two basic steps of OnBytes/Model/Trees.lean -/

/-- One run added to the column weights of a virtual row. -/
theorem pushRun_frame (F : Fork) (k : E) (a b : Array HTree) (r : Run2)
    (h : pushRun k a r = some b) : FrameKept { F with trees := a } { F with trees := b } := by
  unfold pushRun at h
  split at h
  · obtain rfl := Option.some.inj h
    exact onRow_frame { F with trees := a } r.tree r.row _
  · simp at h

/-- The runs of a claim, one after the other. -/
theorem pushRunsL_frame (F : Fork) (k : E) : ∀ (l : List Run2) (a b : Array HTree),
    l.foldlM (pushRun k) a = some b → FrameKept { F with trees := a } { F with trees := b }
  | [], a, b, h => by
    obtain rfl : a = b := by simpa using h
    exact FrameKept.refl _
  | r :: l, a, b, h => by
    rw [List.foldlM_cons] at h
    cases hq : pushRun k a r with
    | none => simp [hq] at h
    | some a1 =>
      rw [hq] at h
      exact (pushRun_frame F k a a1 r hq).trans (pushRunsL_frame F k l a1 b (by simpa using h))

/-- Adding the runs of a claim to the one equation. -/
theorem pushRuns_frame {F G : Fork} {k : E} {runs : Array Run2} (h : F.pushRuns k runs = some G) :
    FrameKept F G := by
  unfold Fork.pushRuns at h
  simp only [] at h
  cases hq : runs.foldlM (pushRun k) F.trees with
  | none => simp [hq] at h
  | some b =>
    simp only [hq, Option.map_some, Option.some.injEq] at h
    subst h
    rw [← Array.foldlM_toList] at hq
    exact pushRunsL_frame F k _ _ _ hq

/-- Adding the runs of a claim, as a routine. -/
instance pres_pushRuns [Prim R] (k : E) (runs : Array Run2) :
    Pres R (SubM.change (·.pushRuns k runs)) :=
  pres_change _ fun _ _ h => Prim.ofFrame (pushRuns_frame h)

/-- `t2Lin` keeps R. -/
instance pres_t2Lin [Prim R] (a : Aff) (runs : Array Run2) : Pres R (t2Lin a runs) := by
  unfold t2Lin
  walk

/-- Changing one array by a function that keeps its kind and sizes keeps the shapes. -/
theorem modify_shapes (F : Fork) (a : Array HTree) (t : Nat) (f : HTree → HTree)
    (hf : ∀ X, ((f X).kind, (f X).R, (f X).K, (f X).rows.size) = (X.kind, X.R, X.K, X.rows.size)) :
    ShapesKept { F with trees := a } { F with trees := a.modify t f } := by
  refine ⟨by simp, fun t' => ?_⟩
  unfold Port.shapeAt
  show (((a.modify t f).getD t' {}).kind, ((a.modify t f).getD t' {}).R,
    ((a.modify t f).getD t' {}).K, ((a.modify t f).getD t' {}).rows.size) = _
  rw [Port.getD_modify]
  by_cases hc : t = t' ∧ t' < a.size
  · rw [if_pos hc]
    exact hf _
  · rw [if_neg hc]

/-- Giving every virtual row of every listed array its column weights keeps the shapes. -/
theorem t2FillL_shapes (F : Fork) (T : Tail2) : ShapesKept F (t2FillL F T) := by
  unfold t2FillL
  simp only []
  generalize List.range T.nt.size = l
  have key : ∀ (l : List Nat) (a : Array HTree), ShapesKept { F with trees := a }
      { F with trees := l.foldl (fun trees ti => trees.modify ti fun X =>
        { X with rows := X.rows.map fun r =>
            if r.L.size != X.K then { r with L := Array.replicate X.K zeroE } else r }) a } := by
    intro l
    induction l with
    | nil => exact fun a => ShapesKept.refl _
    | cons t l ih =>
      intro a
      rw [List.foldl_cons]
      exact (modify_shapes F a t _ (fun X => by simp)).trans (ih _)
  exact key l F.trees

/-- Giving the listed arrays' virtual rows their column weights, as a routine. -/
instance pres_t2FillL [PrimS R] (T : Tail2) : Pres R (SubM.change fun F => some (t2FillL F T)) :=
  pres_change _ fun F _ h => by
    obtain rfl := Option.some.inj h
    exact PrimS.ofShapes (t2FillL_shapes F T)

/-- Resetting the marks of the claims' weights. -/
instance pres_kapMap [Prim R] : Pres R (SubM.change fun F =>
    some { F with kapMapF := Array.replicate F.planClaimsF false }) :=
  pres_change _ fun F _ h => by
    obtain rfl := Option.some.inj h
    exact Prim.ofFrame (FrameKept.of_same rfl rfl)

/-- The step of the start of a run. -/
instance pres_start [PrimS R] (ns : Nat) : Pres R (SubM.change fun F => some (F.fillL.slots ns)) :=
  pres_change _ fun F _ h => by
    obtain rfl := Option.some.inj h
    exact PrimS.ofShapes ((fillL_shapes F).trans (slots_shapes _ _))

/-- `HTailF2.coefficientsF` keeps R. -/
instance pres_coefficientsF [Prim R] (tl : HTailF2) : Pres R tl.coefficientsF :=
  ⟨fun F c _ G c' h => Prim.ofFrame (coefficientsF_frame tl F G c c' h)⟩

/-! ## The smallness test's routines -/

open OnBytes.Model.HTailF2 in
/-- `HTailF2.drawMatrixF` keeps R. -/
instance pres_Model_HTailF2_drawMatrixF [Prim R] (tl : HTailF2) :
    Pres R (OnBytes.Model.HTailF2.drawMatrixF tl) := by
  unfold OnBytes.Model.HTailF2.drawMatrixF
  walk

open OnBytes.Model.HTailF2 in
/-- `HTailF2.linJoin9` keeps R. -/
instance pres_Model_HTailF2_linJoin9 [Prim R] (tl : HTailF2) :
    Pres R (OnBytes.Model.HTailF2.linJoin9 tl) := by
  unfold OnBytes.Model.HTailF2.linJoin9
  walk

open OnBytes.Model.HTailF2 in
/-- `HTailF2.linBits9` keeps R. -/
instance pres_Model_HTailF2_linBits9 [Prim R] (tl : HTailF2) :
    Pres R (OnBytes.Model.HTailF2.linBits9 tl) := by
  unfold OnBytes.Model.HTailF2.linBits9
  walk

open OnBytes.Model.HTailF2 in
/-- `HTailF2.linTie` keeps R. -/
instance pres_Model_HTailF2_linTie [Prim R] (tl : HTailF2) (mu : Nat) :
    Pres R (OnBytes.Model.HTailF2.linTie tl mu) := by
  unfold OnBytes.Model.HTailF2.linTie
  walk

open OnBytes.Model.HTailF2 in
/-- `HTailF2.linRead` keeps R. -/
instance pres_Model_HTailF2_linRead [Prim R] (tl : HTailF2) (Fn : HFun) (sg laid : Nat) (sums : E) :
    Pres R (OnBytes.Model.HTailF2.linRead tl Fn sg laid sums) := by
  unfold OnBytes.Model.HTailF2.linRead
  walk

open OnBytes.Model.HTailF2 in
/-- `HTailF2.weightsF` keeps R. -/
instance pres_Model_HTailF2_weightsF [Prim R] (tl : HTailF2) :
    Pres R (OnBytes.Model.HTailF2.weightsF tl) := by
  unfold OnBytes.Model.HTailF2.weightsF
  walk

open OnBytes.Model.HTailF2 in
/-- `HTailF2.objectsF` keeps R. -/
instance pres_Model_HTailF2_objectsF [Prim R] (tl : HTailF2) (funs : Array HFun) :
    Pres R (OnBytes.Model.HTailF2.objectsF tl funs) := by
  unfold OnBytes.Model.HTailF2.objectsF
  walk

open OnBytes.Model.HTailF2 in
/-- `HTailF2.selfTestF` keeps R. -/
instance pres_Model_HTailF2_selfTestF [Prim R] (tl : HTailF2) (nU : Array Nat) :
    Pres R (OnBytes.Model.HTailF2.selfTestF tl nU) := by
  unfold OnBytes.Model.HTailF2.selfTestF
  walk

open OnBytes.Model.HTailF2 in
/-- `HTailF2.selfTest` keeps R. -/
instance pres_Model_HTailF2_selfTest [Prim R] (tl : HTailF2) (nU : Array Nat) :
    Pres R (OnBytes.Model.HTailF2.selfTest tl nU) := by
  unfold OnBytes.Model.HTailF2.selfTest
  walk

open OnBytes.Model.HTailF2 in
/-- `HTailF2.coefficients` keeps R. -/
instance pres_Model_HTailF2_coefficients [Prim R] (tl : HTailF2) :
    Pres R (OnBytes.Model.HTailF2.coefficients tl) := by
  unfold OnBytes.Model.HTailF2.coefficients
  walk

open OnBytes.Model.HTailF2 in
/-- `HTailF2.tileSelfTestF` keeps R. -/
instance pres_Model_HTailF2_tileSelfTestF [Prim R] (tl : HTailF2) :
    Pres R (OnBytes.Model.HTailF2.tileSelfTestF tl) := by
  unfold OnBytes.Model.HTailF2.tileSelfTestF
  walk

open OnBytes.Model.HTailF2 in
/-- `HTailF2.rkSelfTest` keeps R. -/
instance pres_Model_HTailF2_rkSelfTest [Prim R] (tl : HTailF2) :
    Pres R (OnBytes.Model.HTailF2.rkSelfTest tl) := by
  unfold OnBytes.Model.HTailF2.rkSelfTest
  walk

/-! ## Routines that also call the chain -/

instance presL_pure [Prim R] {α : Type} (a : α) : PresL R (pure a : LinkM α) :=
  ⟨fun L F c x L' G c' h => by
    obtain ⟨-, -, rfl, -⟩ := (pureL_ok _ _ _ _ _ _ _ _).1 h
    exact Prim.refl _⟩

/-- «x, then f». -/
theorem presL_bind [Prim R] {α β : Type} {x : LinkM α} {f : α → LinkM β} (hx : PresL R x)
    (hf : ∀ a, PresL R (f a)) : PresL R (x >>= f) :=
  ⟨fun L F c b L' G c' h => by
    obtain ⟨a, L1, F1, c1, h1, h2⟩ := (bindL_ok _ _ _ _ _ _).1 h
    exact Prim.trans (hx.out L F c a L1 F1 c1 h1) ((hf a).out L1 F1 c1 b L' G c' h2)⟩

/-- A lifted routine of the sub-proof. -/
instance presL_sub {α : Type} (x : SubM α) [hx : Pres R x] : PresL R (LinkM.sub x) :=
  ⟨fun _ F c a _ G c' h => hx.out F c a G c' ((subL_ok _ _ _ _ _ _ _ _).1 h).1⟩

/-- Reading the link's own state. -/
instance presL_get [Prim R] : PresL R (get : LinkM LinkCtx) :=
  ⟨fun L F c a L' G c' h => by
    have h' : (pure (L, L) : SubM (LinkCtx × LinkCtx)) F c = .ok (((a, L'), G), c') := h
    obtain ⟨-, rfl, -⟩ := (Port.pure_ok _ _ _ _ _ _).1 h'
    exact Prim.refl _⟩

/-- Setting the link's own state. -/
instance presL_set [Prim R] (L0 : LinkCtx) : PresL R (set L0 : LinkM PUnit) :=
  ⟨fun L F c a L' G c' h => by
    have h' : (pure (PUnit.unit, L0) : SubM (PUnit × LinkCtx)) F c = .ok (((a, L'), G), c') := h
    obtain ⟨-, rfl, -⟩ := (Port.pure_ok _ _ _ _ _ _).1 h'
    exact Prim.refl _⟩

/-- Changing the link's own state. -/
instance presL_modify [Prim R] (f : LinkCtx → LinkCtx) : PresL R (modify f : LinkM PUnit) :=
  ⟨fun L F c a L' G c' h => by
    have h' : (pure (PUnit.unit, f L) : SubM (PUnit × LinkCtx)) F c = .ok (((a, L'), G), c') := h
    obtain ⟨-, rfl, -⟩ := (Port.pure_ok _ _ _ _ _ _).1 h'
    exact Prim.refl _⟩

/-- A loop over a list. -/
theorem presL_loop [Prim R] {α β : Type} (f : α → β → LinkM (ForInStep β))
    (hf : ∀ a b, PresL R (f a b)) : ∀ (l : List α) (b : β), PresL R (forIn l b f)
  | [], b => by
    rw [List.forIn_nil]
    exact presL_pure b
  | a :: l, b => by
    rw [List.forIn_cons]
    refine presL_bind (hf a b) fun r => ?_
    cases r with
    | done b1 => exact presL_pure b1
    | yield b1 => exact presL_loop f hf l b1

/-- `LinkM.must` keeps R. -/
instance presL_must [Prim R] (b : Bool) : PresL R (LinkM.must b) := presL_sub _

/-- `LinkM.mustAs` keeps R. -/
instance presL_mustAs [Prim R] (name : String) (b : Bool) : PresL R (LinkM.mustAs name b) :=
  presL_sub _

/-- `LinkM.testAs` keeps R. -/
instance presL_testAs [Prim R] (name : String) (b : Bool) : PresL R (LinkM.testAs name b) :=
  presL_sub _

/-- `LinkM.fork` keeps R. -/
instance presL_fork [Prim R] : PresL R LinkM.fork := presL_sub _

/-- A call of the chain leaves the sub-proof's state. -/
instance presL_call [Prim R] (f : ChainCheck → Blk ChainCheck) : PresL R (LinkM.call f) :=
  ⟨fun L F c a L' G c' h => by
    have hp : Pres R (do
        SubM.must (L.link == L.check.link)
        let check ← (liftM (f L.check) : SubM ChainCheck)
        pure ((), { L with check := check }) : SubM (Unit × LinkCtx)) := by
      walk
    exact hp.out F c _ G c' h⟩

/-- One step of a walk through the text of a routine that also calls the chain. -/
macro "walkL_step" : tactic => `(tactic| first
  | exact inferInstance
  | refine presL_bind ?_ ?_ | refine presL_loop _ ?_ _ _
  | intro _ | split | dsimp only)

/-- A walk through the text of a routine that also calls the chain. -/
macro "walkL" : tactic => `(tactic| repeat' walkL_step)

/-- `rootInH` keeps R. -/
instance presL_Model_rootInH [Prim R] (trees : List Nat) :
    PresL R (OnBytes.Model.rootInH trees) := by
  unfold OnBytes.Model.rootInH
  walkL

/-- `t2Batch` keeps R. -/
instance presL_Model_t2Batch [PrimS R] (used : Nat) :
    PresL R (OnBytes.Model.t2Batch used) := by
  unfold OnBytes.Model.t2Batch
  walkL

/-- `HTailF2.fixedBeforeTheMatrixF` keeps R. -/
instance presL_Model_HTailF2_fixedBeforeTheMatrixF [Prim R] (tl : HTailF2) :
    PresL R (OnBytes.Model.HTailF2.fixedBeforeTheMatrixF tl) := by
  unfold OnBytes.Model.HTailF2.fixedBeforeTheMatrixF
  walkL

/-- `HTailF2.transcriptF` keeps R. -/
instance presL_Model_HTailF2_transcriptF [Prim R] (tl : HTailF2) :
    PresL R (OnBytes.Model.HTailF2.transcriptF tl) := by
  unfold OnBytes.Model.HTailF2.transcriptF
  walkL

/-- `Attention.Seam.start` keeps R. -/
instance presL_Attention_Seam_start [PrimS R] (s : Attention.Seam) (ns : Nat) :
    PresL R (OnBytes.Attention.Seam.start s ns) := by
  unfold OnBytes.Attention.Seam.start
  walkL

end OnBytes.Tie.Pv.Tail.Walk

#print axioms OnBytes.Tie.Pv.Tail.Walk.pushRuns_frame
#print axioms OnBytes.Tie.Pv.Tail.Walk.t2FillL_shapes
#print axioms OnBytes.Tie.Pv.Tail.Walk.pres_Model_HTailF2_objectsF
#print axioms OnBytes.Tie.Pv.Tail.Walk.presL_Model_rootInH
#print axioms OnBytes.Tie.Pv.Tail.Walk.presL_Model_t2Batch
#print axioms OnBytes.Tie.Pv.Tail.Walk.presL_Model_HTailF2_transcriptF
#print axioms OnBytes.Tie.Pv.Tail.Walk.presL_Attention_Seam_start
