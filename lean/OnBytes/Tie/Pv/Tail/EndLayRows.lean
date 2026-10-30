-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndLayRows.lean: the premise `RawRows` of the theorems on what objectsF adds
(OnBytes/Tie/Pv/Tail/EndAll.lean, EndSpread.lean), at one run of the check of a layer group's
sub-proof, said of the run's own states.

Theorems with their proofs. OnBytes/Tie/Pv/Tail/EndViews.lean has the same with the states under
«there are». Here the run is given taken apart, as the record `LayRan` of
OnBytes/Tie/Pv/Keeps/LayerRan.lean has it, and the statements name that record's states: F22 and F23
before and after objectsF, F32 and F33 before and after the row weights are set.

Main names:
  `runOf`: from a run of a routine that keeps a relation, the relation between its two states.
  `layRan_shapes`: the arrays' shapes are kept from the state at which the run began to F22.
  `layRan_frame`: shapes and batching element are kept from F23 to F32.
  `layRan_record`: the record's numbers of the arrays, blocks and lengths are kept from the plan's
    to tlA.
  `layRan_rawRows`: `RawRows W tlA F23 o.funs (ρ F23.theta) A` in every world that reads the four
    kinds of virtual row at F33 as sums of the arrays' entries.
  `layRan_rows`: `rowWeight ρ F33.trees iU3 r = unitRows r` for every r.

Limits: the run must begin at the plan's state. `ReadsRaw` (OnBytes/Tie/Pv/Tail/EndRaw.lean) is a
premise.


-/
import OnBytes.Tie.Pv.Keeps.LayerRan
import OnBytes.Tie.Pv.Tail.EndPlans
import OnBytes.Tie.Pv.Tail.EndUnitRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port OnBytes.Tie.Pv.Tail.Walk OnBytes.L5.LayerRan
  OnBytes.L5.LayerCut

/-- From a run of a routine that keeps a relation, the relation between its two states. -/
theorem runOf {R : Fork → Fork → Prop} {α : Type} {x : SubM α} (hx : Pres R x) {F G : Fork}
    {c c' : Ctx} {a : α} (h : x F c = .ok ((a, G), c')) : R F G := hx.out _ _ _ _ _ h

section
variable {P : Layer.Pub} {hp : Layer.HPlan2} {g : Nat} {L L' : LinkCtx} {F' : Fork} {c c' : Ctx}
  {iU3 : Nat} {fo : Forest.Heard} {o : Layer.Own} {F0 F1 F2 F3 : Fork} {L3 : LinkCtx}
  {c1 c2 c3 : Ctx} {tl1 tlA tl : HTailF2} {laid : Nat} {L4 L6 : LinkCtx}
  {F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 : Fork}
  {F21 F22 F23 F24 F25 F26 F27 F28 F29 F30 F31 F32 F33 F34 : Fork}
  {c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 : Ctx}
  {c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 : Ctx}

/-- The arrays' shapes are kept from the state at which the run began to the state before
objectsF. -/
theorem layRan_shapes {F : Fork}
    (X : LayRan P hp g L F c L' F' c' iU3 fo o F0 F1 F2 F3 L3 c1 c2 c3 tl1 tlA tl laid L4 L6 F4 F5
      F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24 F25 F26 F27 F28 F29
      F30 F31 F32 F33 F34 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22
      c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34) : ShapesKept F F22 := by
  have k0 : ShapesKept F F0 := by
    rw [X.cut.start]
    exact (fillL_shapes F).trans (slots_shapes _ _)
  have k1 : ShapesKept F0 F1 := runOf inferInstance X.cut.pad
  have k2 : ShapesKept F1 F2 := runOf inferInstance X.cut.own
  have k3 : ShapesKept F2 F3 :=
    (inferInstance : PresL ShapesKept (rootInH [iU3])).out _ _ _ _ _ _ _ X.cut.root
  have k4 : ShapesKept F3 F4 :=
    (inferInstance : PresL ShapesKept tl1.transcriptF).out _ _ _ _ _ _ _ X.transcript
  have k5 : ShapesKept F4 F5 := runOf inferInstance X.setPlan
  have k6 : ShapesKept F5 F6 :=
    (inferInstance : PresL ShapesKept (t2Batch F4.next)).out _ _ _ _ _ _ _ X.batch
  have k7 : ShapesKept F6 F7 := runOf (by walk2) X.noteTheta
  have k8 : ShapesKept F7 F8 := runOf (by walk2) X.objects
  have k9 : ShapesKept F8 F9 := runOf (by walk2) X.note1
  have k10 : ShapesKept F9 F10 := runOf (by walk2) X.norms
  have k11 : ShapesKept F10 F11 := runOf (by walk2) X.note2
  have k12 : ShapesKept F11 F12 := runOf (by walk2) X.rowBatch
  have k13 : ShapesKept F12 F13 := runOf (by walk2) X.ledger
  have k14 : ShapesKept F13 F14 := runOf (by walk2) X.note3
  have k15 : ShapesKept F14 F15 := runOf (by walk2) X.terms
  have k16 : ShapesKept F15 F16 := runOf (by walk2) X.note4
  have k17 : ShapesKept F16 F17 := runOf (by walk2) X.gated
  have k18 : ShapesKept F17 F18 := runOf (by walk2) X.note5
  have k19 : ShapesKept F18 F19 := runOf (by walk2) X.oneHot
  have k20 : ShapesKept F19 F20 := runOf (by walk2) X.planes
  have k21 : ShapesKept F20 F21 := by
    rcases X.emb with ⟨-, h⟩ | ⟨-, e, -⟩
    · exact runOf inferInstance h
    · rw [e]
      exact ShapesKept.refl _
  have k22 : ShapesKept F21 F22 := runOf inferInstance X.note6
  exact
    ((((((((((((((((((((((k0.trans k1).trans k2).trans k3).trans k4).trans k5).trans k6).trans
    k7).trans k8).trans k9).trans k10).trans k11).trans k12).trans k13).trans k14).trans
    k15).trans k16).trans k17).trans k18).trans k19).trans k20).trans k21).trans k22)

/-- Shapes and batching element are kept from the state after objectsF to the state at which the row
weights are set. -/
theorem layRan_frame {F : Fork}
    (X : LayRan P hp g L F c L' F' c' iU3 fo o F0 F1 F2 F3 L3 c1 c2 c3 tl1 tlA tl laid L4 L6 F4 F5
      F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24 F25 F26 F27 F28 F29
      F30 F31 F32 F33 F34 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22
      c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34) : FrameKept F23 F32 := by
  have f0 : FrameKept F23 F24 := runOf (by walk2) X.note7
  have f1 : FrameKept F24 F25 := runOf (by walk2) X.linRow
  have f2 : FrameKept F25 F26 := runOf (by walk2) X.joinAdded
  have f3 : FrameKept F26 F27 := runOf (by walk2) X.linA
  have f4 : FrameKept F27 F28 := runOf (by walk2) X.linB
  have f5 : FrameKept F28 F29 := runOf (by walk2) X.mergeLin
  have f6 : FrameKept F29 F30 := runOf (by walk2) X.note8
  have f7 : FrameKept F30 F31 := runOf (by walk2) X.freeSlot
  have e := selfTestF_same tl hp.nU F31 F32 c31 c32 X.selfTest
  rw [e]
  exact
    (((((((f0.trans f1).trans f2).trans f3).trans f4).trans f5).trans f6).trans f7)

/-- The record's numbers of the arrays, blocks and lengths are kept from the plan's record to the
one with which objectsF is called. -/
theorem layRan_record {F : Fork}
    (X : LayRan P hp g L F c L' F' c' iU3 fo o F0 F1 F2 F3 L3 c1 c2 c3 tl1 tlA tl laid L4 L6 F4 F5
      F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24 F25 F26 F27 F28 F29
      F30 F31 F32 F33 F34 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22
      c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34) : RecordKept hp.tl tlA :=
  (closeFuns_record X.closed).trans (transcriptF_record X.transcript)

variable {K : Type} [Field K] (ρ : Reading K)

/-- `RawRows` as the theorems on objectsF ask it, at the record's own states. -/
theorem layRan_rawRows (O : Option Layer.HPlan2) (hplan : Layer.planG P g O = .ok hp)
    (X : LayRan P hp g L hp.Fp c L' F' c' iU3 fo o F0 F1 F2 F3 L3 c1 c2 c3 tl1 tlA tl laid L4 L6
      F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24 F25 F26 F27
      F28 F29 F30 F31 F32 F33 F34 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20
      c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34)
    (W : World K) (A : Nat → Nat → Nat → K) (hW : ReadsRaw ρ tl o.funs F33 W A) :
    RawRows W tlA F23 o.funs (ρ.val F23.theta) A := by
  obtain ⟨tl0, tla, Fa, Ta, nU, aTX, hb, hbLine, hadd, hrec, eF⟩ := planG_ok P g O hp hplan
  have k0 : ShapesKept Fa hp.Fp := by
    rw [eF]
    exact trimL_shapes Fa
  have a9 : ShapesKept F22 F23 := runOf inferInstance X.objectsF
  exact rawRows_kept ρ tl0 tla tlA tl o.funs {} Fa F22 F23 F32 F33 F34 {} Ta nU aTX hb hbLine
    c22 c23 c32 c33 c33 c34 W A hadd (hrec.trans (layRan_record X)) X.objectsF
    ((k0.trans (layRan_shapes X)).trans a9) (layRan_frame X) X.coefficients X.v33 X.rkSelfTest hW

/-- No virtual row of the vector of the tables has a weight in which the batching element occurs. -/
theorem layRan_rows (O : Option Layer.HPlan2) (hplan : Layer.planG P g O = .ok hp)
    (X : LayRan P hp g L hp.Fp c L' F' c' iU3 fo o F0 F1 F2 F3 L3 c1 c2 c3 tl1 tlA tl laid L4 L6
      F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24 F25 F26 F27
      F28 F29 F30 F31 F32 F33 F34 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20
      c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34) (r : Nat) :
    OnBytes.Road.Rows.rowWeight ρ F33.trees iU3 r = unitRows r := by
  obtain ⟨tl0, tla, Fa, Ta, nU, aTX, hb, hbLine, hadd, hrec, eF⟩ := planG_ok P g O hp hplan
  have k0 : ShapesKept Fa hp.Fp := by
    rw [eF]
    exact trimL_shapes Fa
  have a9 : ShapesKept F22 F23 := runOf inferInstance X.objectsF
  have k9 : ShapesKept Fa F33 :=
    (((k0.trans (layRan_shapes X)).trans a9).trans (layRan_frame X).shapes).trans
      (coefficientsF_frame tl F32 F33 c32 c33 X.coefficients).shapes
  obtain ⟨hUs, -, -, -⟩ := addTreesF_frame tl0 tla {} Fa {} Ta nU aTX hb hbLine hadd
  obtain ⟨-, r2, -⟩ := addTreesF_record tl0 tla {} Fa {} Ta nU aTX hb hbLine hadd
  have s := hUs 2 (by omega) iU3 (by rw [← r2, ← hrec.ix]; exact X.cut.reads)
  have rT : RecordKept hp.tl tl :=
    (layRan_record X).trans (objectsF_record Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ X.objectsF)
  exact rowWeight_rows ρ tl 2 iU3 _ F32 F33 F34 c32 c33 c33 c34 (by omega)
    (by rw [rT.ix]; exact X.cut.reads) (s.kept k9) X.coefficients X.v33 X.rkSelfTest r

end

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.layRan_shapes
#print axioms OnBytes.Tie.Pv.Tail.layRan_frame
#print axioms OnBytes.Tie.Pv.Tail.layRan_rawRows
#print axioms OnBytes.Tie.Pv.Tail.layRan_rows
