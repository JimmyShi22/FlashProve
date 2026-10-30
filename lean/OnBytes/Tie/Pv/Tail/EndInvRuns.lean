-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndInvRuns.lean: the premises on the state and on the record that the theorems
on what objectsF adds ask (`objectsF_spread_from`, OnBytes/Tie/Pv/Tail/EndInv.lean;
`objectsF_forms_from`, EndFormsFrom.lean), at one run of the check of an attention sub-proof and of
a layer group's sub-proof, said of the run's own states.

Theorems with their proofs. The run is given taken apart, as the records `AttRan`
(OnBytes/Tie/Pv/Keeps/KeepsChainA2.lean) and `LayRan` (OnBytes/Tie/Pv/Keeps/LayerRan.lean) have it.
The relation `Inv` of EndInv.lean (one coefficient for each slot; the plan's number of claims; the
batching element) holds across each basic step, so the walks of OnBytes/Tie/Pv/Tail/EndStepsAll.lean
carry it from the state that the start sets up to the state that objectsF takes, but for the two
steps between that set the plan's number of claims and draw the batching element (`first_state`,
EndFirst.lean).

Main names: the instance `Steps Inv`;
  `runS`, `runSL`: from a run of a routine that keeps a relation, the relation between its two
    states;
  `attRan_state`: at attention, of the state F7 that objectsF takes: one coefficient for each slot;
    the plan's number of claims is P.nLin; the batching element is that of the state behind the
    draw.
  `attRan_fits`: the record tlA with which objectsF is called has shapes that fit its matrices.
  `layRan_state`, `layRan_fits`: the same at a layer group, of F22 and tlA; `planG_fits`: at the
    plan's record.

Limits: `attRan_fits` and `layRan_fits` ask the plan's run. Nothing on `RawRows`
(OnBytes/Tie/Pv/Tail/EndViews.lean, EndLayRows.lean). Nothing at the head. The plan is taken as the
value that the planning routine returns. The plan with which the verifier runs differs from it: at
attention the routine attentionOwners fills one record of the list plFor in the plan's record (the
number of the sub-proof that owns the matrix, and the array's place: borderMeans); at the head the
weights are taken off all virtual rows of the state.


-/
import OnBytes.Tie.Pv.Keeps.KeepsChainA2
import OnBytes.Tie.Pv.Keeps.LayerRan
import OnBytes.Tie.Pv.Tail.EndAtt
import OnBytes.Tie.Pv.Tail.EndFirst
import OnBytes.Tie.Pv.Tail.EndInv
import OnBytes.Tie.Pv.Tail.EndStepsAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port OnBytes.Tie.Pv.Tail.StepsW OnBytes.L5
  OnBytes.L5.LayerRan OnBytes.L5.LayerCut

/-- `Inv` holds across each basic step. -/
instance : Steps Inv where
  refl := Inv.refl
  trans := Inv.trans
  took := fun _ _ hs => ⟨hs, rfl, rfl⟩
  hide := hide_inv
  hideRun := hideRun_inv
  lin := fun {F G f} h hs => by
    obtain ⟨_, _, e3, _, e5, _⟩ :=
      Fork.lin_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ F G f hs h
    exact ⟨e5, lin_plan F G f hs h, e3⟩
  owe := fun _ _ hs => ⟨hs, rfl, rfl⟩
  paid := fun _ _ hs => ⟨hs, rfl, rfl⟩
  rootTaken := fun _ _ _ hs => ⟨hs, rfl, rfl⟩

/-- From a run of a routine that keeps a relation, the relation between its two states. -/
theorem runS {R : Fork → Fork → Prop} {α : Type} {x : SubM α} (hx : Stp R x) {F G : Fork}
    {c c' : Ctx} {a : α} (h : x F c = .ok ((a, G), c')) : R F G := hx.out _ _ _ _ _ h

/-- The same for a routine that also calls the chain. -/
theorem runSL {R : Fork → Fork → Prop} {α : Type} {x : LinkM α} (hx : StpL R x) {L L' : LinkCtx}
    {F G : Fork} {c c' : Ctx} {a : α} (h : x L F c = .ok (((a, L'), G), c')) : R F G :=
  hx.out _ _ _ _ _ _ _ h

/-! ## Attention -/

section
variable {P : Attention.Plan} {L L' : LinkCtx} {F' : Fork} {c c' : Ctx} {tl0 : HTailF2}
  {f : Attention.First} {t : Attention.Tables} {tl1 tlA tl : HTailF2} {laid : Nat}
  {L1 L2 L3 L4 : LinkCtx} {F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 : Fork}
  {c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 : Ctx}

/-- The state that objectsF takes. -/
theorem attRan_state {F : Fork}
    (X : AttRan P L F c L' F' c' tl0 f t tl1 tlA tl laid L1 L2 L3 L4 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10
      F11 F12 F13 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14) :
    F7.LS.size = F7.ns ∧ F7.planClaimsF = P.nLin ∧ F7.theta = F6.theta := by
  obtain ⟨-, e1⟩ := start_ok P.seam P.ns L L1 F F1 c c1 tl0 X.start
  have s1 : F1.LS.size = F1.ns := by
    rw [e1]
    exact slots_sized _ _
  have s2 := (runS (R := Inv) inferInstance X.hear s1).1
  have s3 := (runSL (R := Inv) (x := rootInH [P.iU3]) inferInstance X.root s2).1
  have s4 := (runSL (R := Inv) (x := tl1.transcriptF) inferInstance X.transcript s3).1
  obtain ⟨k, e, -⟩ := first_state P.nLin _ _ _ F4 F5 F6 _ _ _ _ _ X.setPlan X.batch
  obtain ⟨a, b, d⟩ := runS (R := Inv) inferInstance X.claims (k s4)
  exact ⟨a, b.trans e, d⟩

/-- The record with which objectsF is called has shapes that fit its matrices. -/
theorem attRan_fits {F : Fork} (s0 : Attention.Seam) (nU3 hb hbLine : Nat)
    (hplan : s0.plan nU3 hb hbLine = .ok P.seam)
    (X : AttRan P L F c L' F' c' tl0 f t tl1 tlA tl laid L1 L2 L3 L4 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10
      F11 F12 F13 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14) : Port.Fits tlA := by
  obtain ⟨T, hadd⟩ := plan_ok s0 P.seam nU3 hb hbLine hplan
  have f0 : Port.Fits P.seam.tl := (addTreesF_fits _ _ _ _ _ _ _ _ _ _ hadd).1
  obtain ⟨e0, -⟩ := start_ok P.seam P.ns L L1 F F1 c c1 tl0 X.start
  have f1 : Port.Fits tl0 := f0.of_same (by rw [e0]) (by rw [e0]) (by rw [e0])
  have e2 := closeFuns_spec tl0 tl1 _ X.closed
  have f2 : Port.Fits tl1 := f1.of_same (by rw [e2]) (by rw [e2]) (by rw [e2])
  exact fits_transcriptF tl1 tlA _ _ _ _ _ _ X.transcript f2

end

/-! ## A layer group -/

/-- Recording which array of an earlier sub-proof is meant keeps that the shapes fit. -/
theorem borderMeans_fits {tl tl' : HTailF2} {iF ownerNo index : Nat}
    (h : tl.borderMeans iF ownerNo index = .ok tl') (hf : Port.Fits tl) : Port.Fits tl' := by
  unfold HTailF2.borderMeans at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain rfl := Except.ok.inj h
      exact hf.of_same rfl rfl rfl

/-- The plan's record of a layer group's sub-proof has shapes that fit its matrices. -/
theorem planG_fits (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : Port.Fits hp.tl := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨tl0, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨⟨tla, Fa, Ta⟩, hadd, h⟩ := (excBind_ok _ _ _).1 h
  have f0 : Port.Fits tla := (addTreesF_fits _ _ _ _ _ _ _ _ _ _ hadd).1
  obtain ⟨Tp, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  dsimp only at h
  cases O with
  | none =>
    dsimp only at h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨y, hy, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain rfl := Except.ok.inj hy
    obtain rfl := Except.ok.inj h
    exact f0.of_same rfl rfl rfl
  | some O =>
    dsimp only at h
    split at h
    · obtain ⟨y, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨tlB, hbm, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨y2, hy, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain rfl := Except.ok.inj hy
      obtain rfl := Except.ok.inj h
      exact borderMeans_fits hbm (f0.of_same rfl rfl rfl)
    · exact absurd h (throw_bind_ne _ _ _)

section
variable {P : Layer.Pub} {hp : Layer.HPlan2} {g : Nat} {L L' : LinkCtx} {F' : Fork} {c c' : Ctx}
  {iU3 : Nat} {fo : Forest.Heard} {o : Layer.Own} {F0 F1 F2 F3 : Fork} {L3 : LinkCtx}
  {c1 c2 c3 : Ctx} {tl1 tlA tl : HTailF2} {laid : Nat} {L4 L6 : LinkCtx}
  {F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 : Fork}
  {F21 F22 F23 F24 F25 F26 F27 F28 F29 F30 F31 F32 F33 F34 : Fork}
  {c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 : Ctx}
  {c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 : Ctx}

/-- The state that objectsF takes. -/
theorem layRan_state {F : Fork}
    (X : LayRan P hp g L F c L' F' c' iU3 fo o F0 F1 F2 F3 L3 c1 c2 c3 tl1 tlA tl laid L4 L6 F4 F5
      F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24 F25 F26 F27 F28 F29
      F30 F31 F32 F33 F34 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22
      c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34) :
    F22.LS.size = F22.ns ∧ F22.planClaimsF = hp.nLin ∧ F22.theta = F6.theta := by
  have s0 : F0.LS.size = F0.ns := by
    rw [X.cut.start]
    exact slots_sized _ _
  have s1 := (runS (R := Inv) inferInstance X.cut.pad s0).1
  have s2 := (runS (R := Inv) inferInstance X.cut.own s1).1
  have s3 := (runSL (R := Inv) (x := rootInH [iU3]) inferInstance X.cut.root s2).1
  have s4 := (runSL (R := Inv) (x := tl1.transcriptF) inferInstance X.transcript s3).1
  obtain ⟨k, e, -⟩ := first_state hp.nLin _ _ _ F4 F5 F6 _ _ _ _ _ X.setPlan X.batch
  have k7 : Inv F6 F7 := runS (by stp) X.noteTheta
  have k8 : Inv F7 F8 := runS (by stp) X.objects
  have k9 : Inv F8 F9 := runS (by stp) X.note1
  have k10 : Inv F9 F10 := runS (by stp) X.norms
  have k11 : Inv F10 F11 := runS (by stp) X.note2
  have k12 : Inv F11 F12 := runS (by stp) X.rowBatch
  have k13 : Inv F12 F13 := runS (by stp) X.ledger
  have k14 : Inv F13 F14 := runS (by stp) X.note3
  have k15 : Inv F14 F15 := runS (by stp) X.terms
  have k16 : Inv F15 F16 := runS (by stp) X.note4
  have k17 : Inv F16 F17 := runS (by stp) X.gated
  have k18 : Inv F17 F18 := runS (by stp) X.note5
  have k19 : Inv F18 F19 := runS (by stp) X.oneHot
  have k20 : Inv F19 F20 := runS (by stp) X.planes
  have k21 : Inv F20 F21 := by
    rcases X.emb with ⟨-, h⟩ | ⟨-, e, -⟩
    · exact runS inferInstance h
    · rw [e]
      exact Inv.refl _
  have k22 : Inv F21 F22 := runS inferInstance X.note6
  obtain ⟨a, b, d⟩ :=
    (((((((((((((((k7.trans k8).trans k9).trans k10).trans k11).trans k12).trans k13).trans
    k14).trans k15).trans k16).trans k17).trans k18).trans k19).trans k20).trans k21).trans k22)
      (k s4)
  exact ⟨a, b.trans e, d⟩

/-- The record with which objectsF is called has shapes that fit its matrices. -/
theorem layRan_fits {F : Fork} (O : Option Layer.HPlan2) (hplan : Layer.planG P g O = .ok hp)
    (X : LayRan P hp g L F c L' F' c' iU3 fo o F0 F1 F2 F3 L3 c1 c2 c3 tl1 tlA tl laid L4 L6 F4 F5
      F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24 F25 F26 F27 F28 F29
      F30 F31 F32 F33 F34 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22
      c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34) : Port.Fits tlA := by
  have f0 := planG_fits P g O hp hplan
  have e2 := closeFuns_spec hp.tl tl1 _ X.closed
  have f2 : Port.Fits tl1 := f0.of_same (by rw [e2]) (by rw [e2]) (by rw [e2])
  exact fits_transcriptF tl1 tlA _ _ _ _ _ _ X.transcript f2

end

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.attRan_state
#print axioms OnBytes.Tie.Pv.Tail.attRan_fits
#print axioms OnBytes.Tie.Pv.Tail.layRan_state
#print axioms OnBytes.Tie.Pv.Tail.layRan_fits
