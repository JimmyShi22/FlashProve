-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndAtt.lean: the premise `RawRows` of the theorems on what objectsF adds
(OnBytes/Tie/Pv/Tail/EndAll.lean, EndSpread.lean), at the check of an attention sub-proof
(`Attention.run`, OnBytes/Model/Attention.lean).

Theorems with their proofs. The premises are the runs of the calls of `Attention.run` that bear on
the smallness test's state, each as the routine applied to its states and the context, and the run
of the plan that made the list of arrays (`Attention.Seam.plan`, OnBytes/Model/AttentionPlan.lean).

Main names:
  `getF_ok`: reading the sub-proof's state.
  `selfTestF_same`, `noFreeSlot_same`: two tests leave the sub-proof's state.
  `start_ok`: the start of a run: the plan's record with two fields reset; the state gets its column
    weights and its slots.
  `plan_ok`: the plan's record and state are those that addTreesF returns.
  `fillL_shapes`: giving every virtual row its column weights keeps the shapes.
  `rawRows_attention`: `RawRows` as the theorems on objectsF ask it.

Limits: one premise on the steps of the check stays: from the state behind the start to the state
that objectsF returns the arrays' shapes are kept (`ShapesKept`, OnBytes/Tie/Pv/Tail/EndKeep.lean):
the messages, the draw of the batching element and the sub-proof's own claims lie between and are
not followed here. The run must begin at the plan's state, and it must be a run on a view, not a dry
run: in a dry run the test of the weights is idle. The world reads the four kinds of virtual row as
sums of the arrays' entries (`ReadsRaw`, OnBytes/Tie/Pv/Tail/EndRaw.lean).


-/
import OnBytes.Model.Attention
import OnBytes.Tie.Pv.Psc.PscRun
import OnBytes.Tie.Pv.Tail.EndRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port Finset

/-- Reading the sub-proof's state. -/
theorem getF_ok (F G a : Fork) (c c' : Ctx) :
    (get : SubM Fork) F c = .ok ((a, G), c') ↔ a = F ∧ G = F ∧ c' = c := by
  show (Except.ok ((F, F), c) : Except Failure ((Fork × Fork) × Ctx)) = _ ↔ _
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- The test that no column that is meant to be read has the weight 0 leaves the state. -/
theorem selfTestF_same (tl : HTailF2) (nU : Array Nat) (F G : Fork) (c c' : Ctx)
    (h : tl.selfTestF nU F c = .ok (((), G), c')) : G = F := by
  unfold HTailF2.selfTestF at h
  rw [bind_ok] at h
  obtain ⟨_, F1, c1, h1, h⟩ := h
  obtain ⟨-, rfl, rfl⟩ := (ask_ok _ _ _ _ _ _).1 h1
  rw [bind_ok] at h
  obtain ⟨_, F2, c2, h2, h⟩ := h
  obtain ⟨-, e⟩ := (OnBytes.PscRun.must_ok _ _ _ _).1 h2
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e
  simp only [bind_ok, lift_ok] at h
  obtain ⟨_, _, _, ⟨_, rfl⟩, _, _, _, ⟨_, rfl⟩, _, rfl⟩ := h
  rfl

/-- The test that every slot of a message has a coefficient leaves the state. -/
theorem noFreeSlot_same (nMsg : Nat) (F G : Fork) (c c' : Ctx)
    (h : Attention.noFreeSlot nMsg F c = .ok (((), G), c')) : G = F := by
  unfold Attention.noFreeSlot at h
  simp only [bind_ok, getF_ok, lift_ok] at h
  obtain ⟨_, _, _, ⟨rfl, rfl, rfl⟩, _, rfl⟩ := h
  rfl

/-- Giving every virtual row its column weights keeps the shapes. -/
theorem fillL_shapes (F : Fork) : ShapesKept F F.fillL := by
  refine ⟨by simp [Fork.fillL], fun t => ?_⟩
  unfold shapeAt Fork.fillL
  by_cases ht : t < F.trees.size
  · simp [Array.getD, ht]
  · simp [Array.getD, ht]

/-- The start of a run. -/
theorem start_ok (s : Attention.Seam) (ns : Nat) (L L1 : LinkCtx) (F F1 : Fork) (c c1 : Ctx)
    (tl0 : HTailF2) (h : s.start ns L F c = .ok (((tl0, L1), F1), c1)) :
    tl0 = { s.tl with funClosed := false, foldDrawn := 0 } ∧ F1 = F.fillL.slots ns := by
  unfold Attention.Seam.start at h
  rw [bindL_ok] at h
  obtain ⟨_, L2, F2, c2, h1, h2⟩ := h
  obtain ⟨rfl, -, rfl, -⟩ := (pureL_ok _ _ _ _ _ _ _ _).1 h2
  obtain ⟨h1, -⟩ := (subL_ok _ _ _ _ _ _ _ _).1 h1
  refine ⟨rfl, ?_⟩
  obtain ⟨G, hG, e⟩ := (OnBytes.PscRun.change_ok _ _ _ _).1 h1
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
  exact (Option.some.inj hG).symm

/-- The plan's record and state are those that addTreesF returns. -/
theorem plan_ok (s0 s : Attention.Seam) (nU3 hb hbLine : Nat)
    (h : s0.plan nU3 hb hbLine = .ok s) :
    ∃ T, s0.tl.addTreesF {} {} #[0, 0, nU3] #[] hb hbLine = .ok (s.tl, s.Fp, T) := by
  unfold Attention.Seam.plan at h
  obtain ⟨⟨tl, Fp, T⟩, h1, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨Tp, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain rfl := Except.ok.inj h
  exact ⟨T, h1⟩

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- `RawRows` as the theorems on objectsF ask it, at the check of an attention sub-proof. -/
theorem rawRows_attention (s0 s : Attention.Seam) (nU3 hb hbLine ns nMsg : Nat) (nU : Array Nat)
    (funs : Array HFun) (tl0 tl1 tlA tl : HTailF2) (L L1 L2 L3 : LinkCtx)
    (F1 F3 F4 F7 F8 F9 F10 F11 F12 : Fork) (c c1 c4 c5 c8 c9 c10 c11 c12 c13 : Ctx) (W : World K)
    (A : Nat → Nat → Nat → K) (hplan : s0.plan nU3 hb hbLine = .ok s)
    (hstart : s.start ns L s.Fp c = .ok (((tl0, L1), F1), c1))
    (hclosed : tl0.closeFuns funs = some tl1)
    (htr : tl1.transcript L2 F3 c4 = .ok (((tlA, L3), F4), c5))
    (hobj : tlA.objectsF funs F7 c8 = .ok ((tl, F8), c9)) (hk : ShapesKept F1 F8)
    (hnf : Attention.noFreeSlot nMsg F8 c9 = .ok (((), F9), c10))
    (hself : tl.selfTestF nU F9 c10 = .ok (((), F10), c11))
    (hco : tl.coefficientsF F10 c11 = .ok (((), F11), c12)) (hd : c12.ch.dry = false)
    (htile : tl.tileSelfTestF F11 c12 = .ok (((), F12), c13))
    (hW : ReadsRaw ρ tl funs F11 W A) : RawRows W tlA F8 funs (ρ.val F8.theta) A := by
  obtain ⟨T, hadd⟩ := plan_ok s0 s nU3 hb hbLine hplan
  obtain ⟨e0, e1⟩ := start_ok s ns L L1 s.Fp F1 c c1 tl0 hstart
  have r0 : RecordKept s.tl tl0 := by
    rw [e0]
    exact ⟨rfl, rfl, rfl⟩
  have hrec : RecordKept s.tl tlA :=
    (r0.trans (closeFuns_record hclosed)).trans (transcriptF_record htr)
  have k1 : ShapesKept s.Fp F8 := by
    refine ((fillL_shapes s.Fp).trans ?_).trans hk
    rw [e1]
    exact slots_shapes _ _
  obtain rfl := noFreeSlot_same nMsg F8 F9 c9 c10 hnf
  obtain rfl := selfTestF_same tl nU F9 F10 c10 c11 hself
  exact rawRows_kept ρ s0.tl s.tl tlA tl funs {} s.Fp F7 F10 F10 F11 F12 {} T #[0, 0, nU3] #[] hb
    hbLine c8 c9 c11 c12 c12 c13 W A hadd hrec hobj k1 (FrameKept.refl _) hco hd htile hW

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.rawRows_attention
