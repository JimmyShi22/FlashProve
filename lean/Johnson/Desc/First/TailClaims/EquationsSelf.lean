-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/EquationsSelf.lean: what a yes of each of the smallness test's two plain
tests behind the adding hands out (selfTestP, rkSelfTestP: SelfTests.lean): every guard, by name; and,
for the first test, the guards in plain words: no column that a virtual row is meant to read has the
weight 0, and the coefficients on the test's own slots are those that were kept.

Definitions, statements and proofs. No routine of `verify-on-bytes` is named. USED OF THE FILES
UNDER OnBytes/, ON RECORDS AND PLAIN DATA ALONE: weightsOf, noneZero, allBelow with allBelow_spec,
isZeroE, zeroE, powE, t2fKappaByText; of the record the plain functions that rkSelfTestP calls (wants,
forestHeld, callHeld, piecesTile, pointsHeld, pieceWeightsHeld, tieShapeHeld, tieWeightsHeld,
planesShapeHeld, planesWeightsHeld, readShapeHeld, readWeightsHeld).
Main names:
  rk_all: a yes of rkSelfTestP hands out all eleven guards.
  self_all: a yes of selfTestP hands out all four.
  noneZero_spec: what noneZero's yes says. NoZero: the first test's second guard in plain words.
  self_tested: a yes of selfTestP gives NoZero, the lengths, and that the window is what was kept.
Limits: from a yes alone. WHAT THE NON-ZERO WEIGHTS ARE WORTH IS NOT SAID: nothing here says that a column
with a non-zero weight is bound by the one equation. In rk_all the guards stay Booleans of
`verify-on-bytes`'s plain functions.

-/
import Johnson.Desc.First.TailClaims.EquationsRaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open OnBytes.Tie.Pv.Tail.Port

/-- **A yes of the test by a second computation hands out all eleven guards.** -/
theorem rk_all (tl : HTailF2) (F : Fork) (h : rkSelfTestP tl F = .ok ()) :
    ∃ (g : Forest.Heard) (jo nbW : Nat) (Wn : List Want),
      tl.heard = some g ∧ tl.joinObj9 = some jo ∧ tl.wants = some (nbW, Wn) ∧
      ((F.trees.getD tl.ix.ZZ {}).rows.size == 2 * nbW + 2 && tl.forestHeld g &&
        [0, 1].all (tl.callHeld g nbW)) = true ∧
      tl.piecesTile F Wn = true ∧ tl.pointsHeld g = true ∧
      Wn.all (tl.pieceWeightsHeld F g (t2fKappaByText F.theta jo)) = true ∧
      ((((F.trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).coef.size == tl.tau &&
        ((F.trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).coef.size == tl.tau &&
        ((F.trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).L.size == 2 * tl.mz &&
        tl.gamX.size == tl.NM && tl.gamV.size == tl.NM &&
        (List.range tl.NM).all (tl.tieShapeHeld F) &&
        tl.shp.foldl (fun n s => n + s.m) 0 == tl.mz && tl.planesShapeHeld F g) = true) ∧
      ((((List.range tl.tau).all fun u =>
          ((F.trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).coef.getD u zeroE == powE F.theta u &&
          ((F.trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).coef.getD u zeroE ==
            ((F.trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).coef.getD u zeroE) &&
        (List.range tl.NM).all
          (tl.tieWeightsHeld F ((F.trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).L) &&
        tl.planesWeightsHeld F g jo) = true) ∧
      tl.readShapeHeld ((F.trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).L = true ∧
      tl.readWeightsHeld F ((F.trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).L = true := by
  unfold rkSelfTestP at h
  split at h
  case h_2 => cases h
  rename_i g hg
  split at h
  case h_2 => cases h
  rename_i jo hjo
  split at h
  case h_2 => cases h
  rename_i nbW Wn hw
  dsimp only at h
  obtain ⟨h5, h⟩ := guard_ok _ _ _ _ _ h
  obtain ⟨h7, h⟩ := guard_ok _ _ _ _ _ h
  obtain ⟨h8, h⟩ := guard_ok _ _ _ _ _ h
  obtain ⟨h10, h⟩ := guard_ok _ _ _ _ _ h
  obtain ⟨h12, h⟩ := guard_ok _ _ _ _ _ h
  obtain ⟨h14, h⟩ := guard_ok _ _ _ _ _ h
  obtain ⟨h16, h⟩ := guard_ok _ _ _ _ _ h
  have h18 := guard_last _ _ _ h
  exact ⟨g, jo, nbW, Wn, hg, hjo, hw, h5, h7, h8, h10, h12, h14, h16, h18⟩

/-- **A yes of the first test hands out all four guards.** -/
theorem self_all (tl : HTailF2) (nU : Array Nat) (F : Fork) (h : selfTestP tl nU F = .ok ()) :
    (nU == tl.nUF) = true ∧
      (selfUnits tl nU F && selfDigits tl F && selfLinked tl F && selfPlanes tl F &&
        selfSymbols tl F) = true ∧
      (tl.lsTail.size == tl.slotB - tl.slotA) = true ∧ selfSlots tl F = true := by
  unfold selfTestP at h
  obtain ⟨h1, h⟩ := guard_ok _ _ _ _ _ h
  obtain ⟨h2, h⟩ := guard_ok _ _ _ _ _ h
  obtain ⟨h3, h⟩ := guard_ok _ _ _ _ _ h
  have h4 := guard_last _ _ _ h
  exact ⟨h1, h2, h3, h4⟩

/-- What noneZero's yes says: L holds the entries first, .., first + count - 1, and none of them is 0. -/
theorem noneZero_spec {L : Array E} {first count : Nat} (h : noneZero L first count = true) :
    first + count ≤ L.size ∧ ∀ i, i < count → isZeroE (L.getD (first + i) zeroE) = false := by
  unfold noneZero at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hs, ha⟩ := h
  refine ⟨hs, fun i hi => ?_⟩
  have hz : i < (L.extract first (first + count)).size := by
    rw [Array.size_extract]
    omega
  have hx := (Array.all_iff_forall.1 ha) i hz
  have hlt : first + i < L.size := by omega
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
  simpa [Array.getElem_extract] using hx ⟨Nat.zero_le i, hz⟩

/-- The first test's second guard in plain words: no column that a virtual row is meant to read has the
weight 0. -/
structure NoZero (tl : HTailF2) (nU : Array Nat) (F : Fork) : Prop where
  /-- every entry of a table U1, U2, U3 that is there -/
  units : ∀ n, n < 3 → ∀ t, tl.ix.U.getD n none = some t → ∀ x, x < nU.getD n 0 →
    isZeroE ((weightsOf F t (x / (F.trees.getD t {}).K)).getD (x % (F.trees.getD t {}).K) zeroE) =
      false
  /-- every digit on the pieces' rows of ZZ: the low digits on row b, the high ones on row nb + b -/
  digits : ∀ b, b < tl.zzBlocks →
    (∀ i, i < tl.mz → isZeroE ((weightsOf F tl.ix.ZZ b).getD (0 + i) zeroE) = false) ∧
    ∀ i, i < tl.mz →
      isZeroE ((weightsOf F tl.ix.ZZ (tl.zzBlocks + b)).getD (tl.mz + i) zeroE) = false
  /-- the reads' row and the ties' row of ZZ -/
  linked : ∀ i, i < 2 * tl.mz →
    isZeroE ((weightsOf F tl.ix.ZZ tl.zzRowReads).getD (0 + i) zeroE) = false ∧
    isZeroE ((weightsOf F tl.ix.ZZ tl.zzRowTies).getD (0 + i) zeroE) = false
  /-- the three rows of BZ -/
  planes : ∀ r, r < 3 → ∀ i, i < tl.bzColumns →
    isZeroE ((weightsOf F tl.ix.BZ r).getD (0 + i) zeroE) = false
  /-- the one row of each symbol array -/
  symbols : ∀ mu, mu < tl.NM → ∀ i, i < (tl.shp.getD mu {}).J * (tl.shp.getD mu {}).k →
    isZeroE ((weightsOf F (tl.gtTree.getD mu 0) 0).getD (0 + i) zeroE) = false

/-- **What a yes of the first test gives.** -/
theorem self_tested (tl : HTailF2) (nU : Array Nat) (F : Fork) (h : selfTestP tl nU F = .ok ()) :
    nU = tl.nUF ∧ NoZero tl nU F ∧ tl.lsTail.size = tl.slotB - tl.slotA ∧
      F.LS.extract tl.slotA tl.slotB = tl.lsTail := by
  obtain ⟨h1, h2, h3, h4⟩ := self_all tl nU F h
  simp only [Bool.and_eq_true] at h2
  obtain ⟨⟨⟨⟨hu, hd⟩, hl⟩, hp⟩, hy⟩ := h2
  refine ⟨by simpa using h1, ⟨?_, ?_, ?_, ?_, ?_⟩, by simpa using h3, by simpa [selfSlots] using h4⟩
  · intro n hn t ht x hx
    simp only [selfUnits, List.all_eq_true, List.mem_range] at hu
    have a := hu n hn
    rw [ht] at a
    have b := allBelow_spec _ _ a x hx
    simpa using b
  · intro b hb
    simp only [selfDigits, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hd
    exact ⟨(noneZero_spec (hd b hb).1).2, (noneZero_spec (hd b hb).2).2⟩
  · intro i hi
    simp only [selfLinked, Bool.and_eq_true] at hl
    exact ⟨(noneZero_spec hl.1).2 i hi, (noneZero_spec hl.2).2 i hi⟩
  · intro r hr
    simp only [selfPlanes, List.all_eq_true, List.mem_range] at hp
    exact (noneZero_spec (hp r hr)).2
  · intro mu hmu
    simp only [selfSymbols, List.all_eq_true, List.mem_range] at hy
    exact (noneZero_spec (hy mu hmu)).2

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.rk_all
#print axioms VerifiableInference.Desc.First.TailClaims.Law.self_all
#print axioms VerifiableInference.Desc.First.TailClaims.Law.self_tested
