-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidHeadCongr.lean: the head's record reads the entries of its list within the
matrices' shapes alone.

Hd.HeadOrdLB (Johnson/Road/HeadL5BL.lean) speaks of a list Mh of integer matrices on all numbers.
Its clauses read Mh through the head's cells (Hd.cellsH), at the names that the head with the cost
ledger reads; the places of these names lie within four ranges: the parts of hf, hd, hr and the copy
of the stream, inside the rows and columns that the layout gives: the four ranges of Hd.SmallH. So
two lists that agree there meet the same record. This is the head's twin of layerOrd_congr_core
(Johnson/Goal/Meaning/HidLayCongr.lean).

Main names:
  AgreeH h L b Mh Mh'   the two lists agree within the four ranges of Hd.SmallH.
  sameMain_cellsH   then their cells, cast into a ring, agree at the names that the head with the
    ledger reads (Policy.SameMain, Policy/Seg/HeadAsm.lean): by Hd.placeIn_inside.
  smallH_congr, headKeys_congr, headR0_congr   clause by clause.
  headOrd_congr   THE STATEMENT ABOVE.

What is not claimed. Anything on a run. The premises Hd.NumH and Hd.BorderH are the head's public
numbers at the full size. The program does not import this file.
-/
import Johnson.Goal.Meaning.HidLaws
import Johnson.Road.Lane5SplitH
import Policy.Seg.HeadAsm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model
open OnBytes OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Verify (borderOf)
open OnBytes.Model.Head (HL Border)

/-- The two lists agree within the four ranges of Hd.SmallH. -/
def AgreeH (h : Model.Head.Shape) (L : HL) (b : Border) (Mh Mh' : Mats ℤ) : Prop :=
  (∀ a < h.NHf, ∀ r < L.m, ∀ c < L.k, Mh a r c = Mh' a r c) ∧
  (∀ r < L.mD, ∀ c < L.kD, Mh h.NHf r c = Mh' h.NHf r c) ∧
  (∀ r < L.mR, ∀ c < L.kR, Mh (h.NHf + 1) r c = Mh' (h.NHf + 1) r c) ∧
  ∀ r < b.mxb, ∀ c < b.kxb, Mh (h.NHf + 3) r c = Mh' (h.NHf + 3) r c

theorem AgreeH.symm {h : Model.Head.Shape} {L : HL} {b : Border} {Mh Mh' : Mats ℤ}
    (A : AgreeH h L b Mh Mh') : AgreeH h L b Mh' Mh :=
  ⟨fun a ha r hr c hc => (A.1 a ha r hr c hc).symm, fun r hr c hc => (A.2.1 r hr c hc).symm,
    fun r hr c hc => (A.2.2.1 r hr c hc).symm, fun r hr c hc => (A.2.2.2 r hr c hc).symm⟩

section
variable {h : Model.Head.Shape} {L : HL} {b : Border} {Mh Mh' : Mats ℤ}

/-- The cells agree at the names that the head with the ledger reads. -/
theorem sameMain_cellsH (N : Hd.NumH h L) (Bd : Hd.BorderH b) (A : AgreeH h L b Mh Mh')
    (K : Type) [CommRing K] :
    Policy.SameMain ((Hd.cellsH h L b Mh).cast K) ((Hd.cellsH h L b Mh').cast K) := by
  refine ⟨fun φ hφ i hi => ?_, fun φ hφ i hi => ?_, fun φ hφ i hi => ?_, fun φ hφ i hi => ?_⟩
  · have hin := (Hd.placeIn_inside N Bd (φ := φ) (show i < 1024 from hi)).1
      (Nat.lt_add_right 128 hφ)
    show ((Hd.cellIn Mh 0 L.k (L.m / h.T) h.T φ i : ℤ) : K) =
      ((Hd.cellIn Mh' 0 L.k (L.m / h.T) h.T φ i : ℤ) : K)
    rw [Hd.cellIn_place, Hd.cellIn_place, Nat.zero_add, A.1 _ hin.1 _ hin.2.1 _ hin.2.2]
  · have hin := (Hd.placeIn_inside N Bd (φ := φ) (show i < 1024 from hi)).2.1 hφ
    show ((Hd.cellIn Mh h.NHf L.kD (L.mD / h.T) h.T φ i : ℤ) : K) =
      ((Hd.cellIn Mh' h.NHf L.kD (L.mD / h.T) h.T φ i : ℤ) : K)
    rw [Hd.cellIn_place, Hd.cellIn_place, hin.1, Nat.add_zero, A.2.1 _ hin.2.1 _ hin.2.2]
  · have hin := (Hd.placeIn_inside N Bd (φ := φ) (show i < 1024 from hi)).2.2.1 hφ
    show ((Hd.cellIn Mh (h.NHf + 1) L.kR (L.mR / h.T) h.T φ i : ℤ) : K) =
      ((Hd.cellIn Mh' (h.NHf + 1) L.kR (L.mR / h.T) h.T φ i : ℤ) : K)
    rw [Hd.cellIn_place, Hd.cellIn_place, hin.1, Nat.add_zero, A.2.2.1 _ hin.2.1 _ hin.2.2]
  · have hφ' : φ < 25600 := hφ
    have hc : b.cell (φ / h.d) (φ % h.d) < Head.nFeat .x := by
      rw [Bd.cell, N.d]
      show 5120 * (φ / 5120) + φ % 5120 < 25600
      omega
    have hin := (Hd.placeIn_inside N Bd (φ := b.cell (φ / h.d) (φ % h.d))
      (show i < 1024 from hi)).2.2.2 hc
    show ((Hd.cellIn Mh (h.NHf + 3) b.kxb (b.mxb / h.T) h.T (b.cell (φ / h.d) (φ % h.d)) i : ℤ) :
        K) =
      ((Hd.cellIn Mh' (h.NHf + 3) b.kxb (b.mxb / h.T) h.T (b.cell (φ / h.d) (φ % h.d)) i : ℤ) : K)
    rw [Hd.cellIn_place, Hd.cellIn_place, hin.1, Nat.add_zero, A.2.2.2 _ hin.2.1 _ hin.2.2]

theorem smallH_congr (A : AgreeH h L b Mh Mh') (S : Hd.SmallH h L b Mh) : Hd.SmallH h L b Mh' :=
  ⟨fun a ha r hr c hc => A.1 a ha r hr c hc ▸ S.1 a ha r hr c hc,
    fun r hr c hc => A.2.1 r hr c hc ▸ S.2.1 r hr c hc,
    fun r hr c hc => A.2.2.1 r hr c hc ▸ S.2.2.1 r hr c hc,
    fun r hr c hc => A.2.2.2 r hr c hc ▸ S.2.2.2 r hr c hc⟩

end

section
variable {h : Model.Head.Shape} {L : HL} {y : Model.Layer.Lay} {np : NormPar} {pol : AcceptancePolicy}
  {Wz : Mat} {x : Instance ppref} {Mh Mh' : Mats ℤ}

theorem headKeys_congr (N : Hd.NumH h L) (Bd : Hd.BorderH (borderOf y))
    (A : AgreeH h L (borderOf y) Mh Mh') (H : HeadKeys h L y np pol Wz x Mh) :
    HeadKeys h L y np pol Wz x Mh' := fun f a i ha hi => by
  rw [← Policy.keyM_same (sameMain_cellsH N Bd A Cb.Gl.F) np _ _ f ha hi]
  exact H f a i ha hi

theorem headR0_congr (N : Hd.NumH h L) (Bd : Hd.BorderH (borderOf y))
    (A : AgreeH h L (borderOf y) Mh Mh') (H : HeadR0 h L y np pol x Mh) :
    HeadR0 h L y np pol x Mh' := by
  have S := sameMain_cellsH N Bd A Cb.Gl.F
  obtain ⟨h1, ⟨h2, h3, h4⟩, h5⟩ := H
  refine ⟨smallH_congr A h1, ⟨fun i hi k hk => ?_, fun i hi => ⟨?_, ?_⟩, ?_, ?_⟩, h5⟩
  · rw [← Policy.idnM_same S np hi hk]
    exact h2 i hi k hk
  · rw [← Policy.dB4_same S _ hi]
    exact (h3 i hi).1
  · rw [← Policy.dZ_same S _ hi]
    exact (h3 i hi).2
  · rw [← Policy.sB2_same S]
    exact h4.1
  · rw [← Policy.sB3_same S]
    exact h4.2

/-- **The head's record reads the entries within the shapes alone.** -/
theorem headOrd_congr (N : Hd.NumH h L) (Bd : Hd.BorderH (borderOf y))
    (A : AgreeH h L (borderOf y) Mh Mh') (O : Hd.HeadOrdLB h L y np pol Wz x Mh) :
    Hd.HeadOrdLB h L y np pol Wz x Mh' :=
  headOrdLB_iff_split.2 ⟨headR0_congr N Bd A (headOrdLB_iff_split.1 O).1,
    headKeys_congr N Bd A (headOrdLB_iff_split.1 O).2⟩

end

end Meaning

#print axioms Meaning.AgreeH.symm
#print axioms Meaning.sameMain_cellsH
#print axioms Meaning.smallH_congr
#print axioms Meaning.headKeys_congr
#print axioms Meaning.headR0_congr
#print axioms Meaning.headOrd_congr
