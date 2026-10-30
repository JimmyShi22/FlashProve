-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndHeadRows.lean: at one run of the check of the head's sub-proof, said of the
run's own states: the premise `RawRows` of the theorems on what objectsF adds; the row weights of
the vector of the tables; and that the sub-proof's own claims name entries of that vector alone.

Theorems with their proofs. OnBytes/Tie/Pv/Tail/EndViews.lean and EndGoodHead.lean have the same
with the states under «there are». Here the run is given taken apart, as the record `HeadRan` of
OnBytes/Tie/Pv/Tail/EndHeadRan.lean has it: F22 and F23 are the states before and after objectsF,
F29 and F30 those before and after the row weights are set, F8 the state behind the draw of the
batching element, F28 the state behind the last claim.

Main names:
  `headRan_shapes`: the arrays' shapes are kept from the state at which the run began to F22.
  `headRan_frame`: shapes and batching element are kept from F23 to F29.
  `headRan_record`: the record's numbers of the arrays, blocks and lengths are kept from the plan's
    to tlA.
  `headRan_rawRows`: `RawRows W tlA F23 Rn.t.funs (ρ F23.theta) A` in every world that reads the
    four kinds of virtual row at F30 as sums of the arrays' entries.
  `headRan_rows`: `rowWeight ρ F30.trees iU3 r = unitRows r` for every r.
  `headRan_good`: the records Rn and wo hold forms with entries in array iU3 alone.
  `headRan_adds`: lists l1 and l3 of forms with `Adds F8 l1 F22` and `Adds F23 l3 F28`, every entry
    of every member in array iU3.

Limits: for `headRan_rawRows` and `headRan_rows` the run must begin at the plan's state. `ReadsRaw`
(OnBytes/Tie/Pv/Tail/EndRaw.lean) is a premise. The lists of forms are found behind the run. The
plan is taken as the value that the planning routine returns. The plan with which the verifier runs
differs from it: at attention the routine attentionOwners fills one record of the list plFor in the
plan's record (the number of the sub-proof that owns the matrix, and the array's place:
borderMeans); at the head the weights are taken off all virtual rows of the state.


-/
import OnBytes.Tie.Pv.Tail.EndGoodHead
import OnBytes.Tie.Pv.Tail.EndHeadRan
import OnBytes.Tie.Pv.Tail.EndLayRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port OnBytes.Tie.Pv.Tail.Walk

section
variable {hS : Head.Shape} {Lh : Head.HL} {b : Head.Border} {hp : Head.HPlanH2} {O : Head.Owner}
  {cov : Head.Covered} {wsLay : WsLay} {L L' : LinkCtx} {F' : Fork} {c c' : Ctx} {wo : WsForkOut}
  {iU3 : Nat} {x : Head.Heard} {t : Head.Tables} {Rn : Head.Run} {claim : WsClaim}
  {tl1 tlA tl : HTailF2} {laid : Nat} {L2 L4 L8 : LinkCtx}
 {F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24 F25
  F26 F27 F28 F29 F30 F31 : Fork}
 {c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26
  c27 c28 c29 c30 c31 : Ctx}

/-- The arrays' shapes are kept from the state at which the run began to the state before objectsF.
-/
theorem headRan_shapes {F : Fork}
   (X : HeadRan hS Lh b hp O cov wsLay L F c wo L' F' c' iU3 x t Rn claim tl1 tlA tl laid L2 L4 L8
      F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24
      F25 F26 F27 F28 F29 F30 F31 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18
      c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31) : ShapesKept F F22 := by
  have k0 : ShapesKept F F0 := by
    rw [X.start]
    exact (ShapesKept.of_trees (F := F) (G := ({ trees := F.trees } : Fork)) rfl).trans
      (fillL_shapes _)
  have k1 : ShapesKept F0 F1 := runOf inferInstance X.hear
  have k2 : ShapesKept F1 F2 :=
    (inferInstance : PresL ShapesKept (rootInH [iU3])).out _ _ _ _ _ _ _ X.root
  have k3 : ShapesKept F2 F3 := runOf inferInstance X.tables
  have k4 : ShapesKept F3 F4 :=
    (inferInstance : PresL ShapesKept tl1.transcriptF).out _ _ _ _ _ _ _ X.transcript
  have k5 : ShapesKept F4 F5 := runOf inferInstance X.weights
  have k6 : ShapesKept F5 F6 := runOf inferInstance X.merge
  have k7 : ShapesKept F6 F7 := runOf inferInstance X.setPlan
  have k8 : ShapesKept F7 F8 :=
    (inferInstance : PresL ShapesKept (t2Batch F6.next)).out _ _ _ _ _ _ _ X.batch
  have k9 : ShapesKept F8 F9 := runOf inferInstance X.objects
  have k10 : ShapesKept F9 F10 := runOf inferInstance X.note1
  have k11 : ShapesKept F10 F11 := runOf inferInstance X.squares
  have k12 : ShapesKept F11 F12 := runOf inferInstance X.note2
  have k13 : ShapesKept F12 F13 := runOf inferInstance X.ledger
  have k14 : ShapesKept F13 F14 := runOf inferInstance X.note3
  have k15 : ShapesKept F14 F15 := runOf inferInstance X.stream
  have k16 : ShapesKept F15 F16 := runOf inferInstance X.note4
  have k17 : ShapesKept F16 F17 := runOf inferInstance X.join
  have k18 : ShapesKept F17 F18 := runOf inferInstance X.note5
  have k19 : ShapesKept F18 F19 := runOf inferInstance X.policy
  have k20 : ShapesKept F19 F20 := runOf inferInstance X.note6
  have k21 : ShapesKept F20 F21 := runOf inferInstance X.planes
  have k22 : ShapesKept F21 F22 := runOf inferInstance X.note7
  exact
    ((((((((((((((((((((((k0.trans k1).trans k2).trans k3).trans k4).trans k5).trans k6).trans
    k7).trans k8).trans k9).trans k10).trans k11).trans k12).trans k13).trans k14).trans
    k15).trans k16).trans k17).trans k18).trans k19).trans k20).trans k21).trans k22)

/-- Shapes and batching element are kept from the state after objectsF to the state at which the row
weights are set. -/
theorem headRan_frame {F : Fork}
   (X : HeadRan hS Lh b hp O cov wsLay L F c wo L' F' c' iU3 x t Rn claim tl1 tlA tl laid L2 L4 L8
      F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24
      F25 F26 F27 F28 F29 F30 F31 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18
      c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31) : FrameKept F23 F29 := by
  have f0 : FrameKept F23 F24 := runOf inferInstance X.note8
  have f1 : FrameKept F24 F25 := runOf inferInstance X.logits
  have f2 : FrameKept F25 F26 := runOf inferInstance X.note9
  have f3 : FrameKept F26 F27 := runOf inferInstance X.mergeLin
  have f4 : FrameKept F27 F28 := runOf inferInstance X.note10
  have e := selfTestF_same tl Rn.hp.nU F28 F29 c28 c29 X.selfTest
  rw [e]
  exact
    ((((f0.trans f1).trans f2).trans f3).trans f4)

/-- The record's numbers of the arrays, blocks and lengths are kept from the plan's record to the
one with which objectsF is called. -/
theorem headRan_record {F : Fork}
   (X : HeadRan hS Lh b hp O cov wsLay L F c wo L' F' c' iU3 x t Rn claim tl1 tlA tl laid L2 L4 L8
      F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24
      F25 F26 F27 F28 F29 F30 F31 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18
      c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31) : RecordKept hp.tl tlA :=
  (closeFuns_record X.closed).trans (transcriptF_record X.transcript)

/-- The records that the claims are made from hold forms with entries in the vector of the tables
alone. -/
theorem headRan_good {F : Fork}
   (X : HeadRan hS Lh b hp O cov wsLay L F c wo L' F' c' iU3 x t Rn claim tl1 tlA tl laid L2 L4 L8
      F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24
      F25 F26 F27 F28 F29 F30 F31 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18
      c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31) :
    Forms.Good iU3 Rn ∧ Forms.Good iU3 wo := by
  have hx : Forms.Good iU3 x := Forms.head_hear_good hS Lh hp cov _ x F0 F1 c c1 X.hear
  refine ⟨⟨?_⟩, ⟨((inferInstance : Forms.PresQ iU3 (wsForkEnd wsLay #[claim] #[x.sV])).out
    F5 c5 wo F6 c6 X.merge).2⟩⟩
  rw [X.run]
  exact hx.out

/-- The sub-proof's own claims, before and after those of the smallness test: two walks, and every
entry in the vector of the tables. -/
theorem headRan_adds {F : Fork}
   (X : HeadRan hS Lh b hp O cov wsLay L F c wo L' F' c' iU3 x t Rn claim tl1 tlA tl laid L2 L4 L8
      F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24
      F25 F26 F27 F28 F29 F30 F31 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18
      c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31) :
    (∃ l1, OnBytes.Road.Rows.Adds F8 l1 F22 ∧ ∀ a ∈ l1, ∀ e ∈ a.ents.toList, e.tree = iU3) ∧
      ∃ l3, OnBytes.Road.Rows.Adds F23 l3 F28 ∧ ∀ a ∈ l3, ∀ e ∈ a.ents.toList, e.tree = iU3 := by
  obtain ⟨g1, g2⟩ := headRan_good X
  have ei : Rn.iU3 = iU3 := by rw [X.run]
  rw [← ei] at g1 g2
  have q : ∀ {α : Type} [Forms.HasGood α] {y : SubM α} (_ : Forms.PresQ Rn.iU3 y) {A B : Fork}
      {d d' : Ctx} {a : α}, y A d = .ok ((a, B), d') → Forms.AddsIn Rn.iU3 A B :=
    fun hy _ _ _ _ _ hr => (hy.out _ _ _ _ _ hr).1
  have k9 := q inferInstance X.objects
  have k10 := q inferInstance X.note1
  have k11 := q inferInstance X.squares
  have k12 := q inferInstance X.note2
  have k13 := q inferInstance X.ledger
  have k14 := q inferInstance X.note3
  have k15 := q inferInstance X.stream
  have k16 := q inferInstance X.note4
  have k17 := q inferInstance X.join
  have k18 := q inferInstance X.note5
  have k19 := q inferInstance X.policy
  have k20 := q inferInstance X.note6
  have k21 := q inferInstance X.planes
  have k22 := q inferInstance X.note7
  have k24 := q inferInstance X.note8
  have k25 := q inferInstance X.logits
  have k26 := q inferInstance X.note9
  have k27 := q inferInstance X.mergeLin
  have k28 := q inferInstance X.note10
  rw [ei] at k9 k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k20 k21 k22 k24 k25 k26 k27 k28
  exact ⟨
    (((((((((((((k9.trans k10).trans k11).trans k12).trans k13).trans k14).trans k15).trans
    k16).trans k17).trans k18).trans k19).trans k20).trans k21).trans k22),
    ((((k24.trans k25).trans k26).trans k27).trans k28)⟩

variable {K : Type} [Field K] (ρ : Reading K)

/-- `RawRows` as the theorems on objectsF ask it, at the record's own states. -/
theorem headRan_rawRows (g : Settings) (NGr lkW : Nat)
    (hplan : Head.planH2 g hS Lh b O NGr lkW = .ok hp)
   (X : HeadRan hS Lh b hp O cov wsLay L hp.Fp c wo L' F' c' iU3 x t Rn claim tl1 tlA tl laid L2
      L4 L8 F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23
      F24 F25 F26 F27 F28 F29 F30 F31 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17
      c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31)
    (W : World K) (A : Nat → Nat → Nat → K) (hW : ReadsRaw ρ tl Rn.t.funs F30 W A) :
    RawRows W tlA F23 Rn.t.funs (ρ.val F23.theta) A := by
  obtain ⟨tl0, tla, Ta, nU, aTX, hb, hbLine, hadd, hrec⟩ := planH2_ok g hS Lh b O NGr lkW hp hplan
  have a9 : ShapesKept F22 F23 := runOf inferInstance X.objectsF
  exact rawRows_kept ρ tl0 tla tlA tl Rn.t.funs {} hp.Fp F22 F23 F29 F30 F31 {} Ta nU aTX hb hbLine
    c22 c23 c29 c30 c30 c31 W A hadd (hrec.trans (headRan_record X)) X.objectsF
    ((headRan_shapes X).trans a9) (headRan_frame X) X.coefficients X.v30 X.rkSelfTest hW

/-- No virtual row of the vector of the tables has a weight in which the batching element occurs. -/
theorem headRan_rows (g : Settings) (NGr lkW : Nat)
    (hplan : Head.planH2 g hS Lh b O NGr lkW = .ok hp)
   (X : HeadRan hS Lh b hp O cov wsLay L hp.Fp c wo L' F' c' iU3 x t Rn claim tl1 tlA tl laid L2
      L4 L8 F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23
      F24 F25 F26 F27 F28 F29 F30 F31 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17
      c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31) (r : Nat) :
    OnBytes.Road.Rows.rowWeight ρ F30.trees iU3 r = unitRows r := by
  obtain ⟨tl0, tla, Ta, nU, aTX, hb, hbLine, hadd, hrec⟩ := planH2_ok g hS Lh b O NGr lkW hp hplan
  have a9 : ShapesKept F22 F23 := runOf inferInstance X.objectsF
  have k9 : ShapesKept hp.Fp F30 :=
    (((headRan_shapes X).trans a9).trans (headRan_frame X).shapes).trans
      (coefficientsF_frame tl F29 F30 c29 c30 X.coefficients).shapes
  obtain ⟨hUs, -, -, -⟩ := addTreesF_frame tl0 tla {} hp.Fp {} Ta nU aTX hb hbLine hadd
  obtain ⟨-, r2, -⟩ := addTreesF_record tl0 tla {} hp.Fp {} Ta nU aTX hb hbLine hadd
  have s := hUs 2 (by omega) iU3 (by rw [← r2, ← hrec.ix]; exact X.reads)
  have rT : RecordKept hp.tl tl :=
    (headRan_record X).trans (objectsF_record Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ X.objectsF)
  exact rowWeight_rows ρ tl 2 iU3 _ F29 F30 F31 c29 c30 c30 c31 (by omega)
    (by rw [rT.ix]; exact X.reads) (s.kept k9) X.coefficients X.v30 X.rkSelfTest r

end

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.headRan_adds
#print axioms OnBytes.Tie.Pv.Tail.headRan_rawRows
#print axioms OnBytes.Tie.Pv.Tail.headRan_rows
