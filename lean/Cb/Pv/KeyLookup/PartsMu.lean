-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/PartsMu.lean: "the planes hold the counts", for a lookup whose keys come in parts,
with public padding: which entries meet the claim after the challenge at every value of the
challenge.

Plain mathematics: no protocol. The file imports no file of the program. No clause Know reads any of
it (Mu stands on the exact side alone); the law on multiplicities of the key's record (KeyMult.law)
is paid from laidQ_valid and validQ_congr. The setting and its names are those of
Cb/Pv/KeyLookup/PartsAlg.lean.

Main definitions.
  ValidQ      the entries write a valid vector of counts: all are bits; the places W ≤ j < 2^w hold
              0; for every value x the counts of the rows that equal x, and the public padding
              counts of these rows, add up to the number of keys of all parts, padding too, that
              equal x.
  hmultQ, hbitQ   counts and their binary digits: a row's count is the number of keys of all parts,
              padding not counted, for which it is chosen. Which places are padding (pad) and which
              row is chosen for a key (row) are arguments.
  LaidQ       every key is the row chosen for it, and the public list of padding counts the places
              of padding, row by row.
  MuOnQ       what is asked of a predicate Mu on (state, entries): for keys in the table, MidQ at
              every challenge. It has the shape of LkHead.MuOn (Cb/Ld/LdLkpHead2.lean).
Main theorems.
  validQ_mid    InParts, W ≤ 2^w, the padding rows are rows, ValidQ: then MidQ at every challenge.
  validQ_idle   ValidQ: then the product of a plane W ≤ j < 2^w is 1 at every challenge.
  laidQ_inParts   LaidQ gives InParts.
  laidQ_valid   allKeys < 2^W and LaidQ: then the digits hbitQ are valid.
  honestQ       allKeys < 2^W, W ≤ 2^w, the padding rows are rows, LaidQ: then the digits hbitQ meet
                MidQ at every challenge.
  muOnQ_valid, muOnQ_laid   MuOnQ holds of the predicate "ValidQ" and of "the entries are hbitQ, and
                LaidQ". These two do not see whether a predicate is empty.
  midQ_congr, validQ_congr   if W ≤ 2^w, MidQ and ValidQ read the entries at u < 2^T, j < 2^w alone.
  validQ_one_nil   at one part, without padding, ValidQ is Cb.LdLkp.Valid (Cb/Ld/LdLkpMult.lean).

Conditions: on public numbers, beside what each statement says of keys and entries.

Not claimed. That a prover of a program writes the digits hbitQ. That ValidQ or hbitQ agree, at one
part with padding, with ValidP (Cb/Pv/Lookup/Hon/ValidP.lean [not in this library]) or hbitP
(Cb/Pv/Lookup/Alg/PadAlg.lean): no theorem here says it. The proofs of validQ_mid, laidQ_valid and
multOf_hbitQ are after the three corresponding proofs of ValidP.lean [not in this library].

-/
import Cb.Pv.KeyLookup.PartsAlg
import Cb.Ld.LdLkpMult

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Finset Prob Cb.Lkp

section
variable {E : Type} [Field E]

open Classical in
/-- The bits write a valid vector of multiplicities, the public padding beside them. -/
def ValidQ (m : ℕ) (v : ℕ → ℕ) (T w W : ℕ) (key : ℕ → ℕ → E) (t : ℕ → E) (pads : List (ℕ × ℕ))
    (M : ℕ → ℕ → E) : Prop :=
  Bits T w M ∧ (∀ u < 2 ^ T, ∀ j, W ≤ j → j < 2 ^ w → M u j = 0) ∧
  ∀ x : E, ∑ u ∈ (range (2 ^ T)).filter (fun u => t u = x), (multOf W M u + padCnt pads u) =
    ∑ i ∈ range m, ((range (2 ^ v i)).filter fun b => key i b = x).card

/-- The honest multiplicity of the row u: the number of places of all parts that are not padding and
whose key hits the row u, by the prover's own choice of rows. -/
def hmultQ (m : ℕ) (v : ℕ → ℕ) (pad : ℕ → ℕ → Bool) (row : ℕ → ℕ → ℕ) (u : ℕ) : ℕ :=
  ∑ i ∈ range m,
    (((range (2 ^ v i)).filter fun b => pad i b = false).filter fun b => row i b = u).card

/-- The honest bits. -/
def hbitQ (m : ℕ) (v : ℕ → ℕ) (W : ℕ) (pad : ℕ → ℕ → Bool) (row : ℕ → ℕ → ℕ) (u j : ℕ) : E :=
  if j < W ∧ (hmultQ m v pad row u).testBit j = true then 1 else 0

/-- What the honest side knows. -/
structure LaidQ (m : ℕ) (v : ℕ → ℕ) (T : ℕ) (key : ℕ → ℕ → E) (t : ℕ → E) (pads : List (ℕ × ℕ))
    (pad : ℕ → ℕ → Bool) (row : ℕ → ℕ → ℕ) : Prop where
  rowLt : ∀ i < m, ∀ b < 2 ^ v i, row i b < 2 ^ T
  hit   : ∀ i < m, ∀ b < 2 ^ v i, key i b = t (row i b)
  laid  : ∀ u < 2 ^ T, padCnt pads u = ∑ i ∈ range m,
    (((range (2 ^ v i)).filter fun b => pad i b = true).filter fun b => row i b = u).card

/-- What is asked of a predicate that says "the planes hold the counts". -/
def MuOnQ {St J : Type} (m : ℕ) (v : ℕ → ℕ) (T w W : ℕ) (key : St → (J → E) → ℕ → ℕ → E)
    (tab : St → ℕ → E) (pads : List (ℕ × ℕ)) (bit : (J → E) → ℕ → ℕ → E)
    (Mu : St → (J → E) → Prop) : Prop :=
  ∀ st μ, InParts m v T (key st μ) (tab st) → Mu st μ →
    ∀ al : E, MidQ m v T w W (key st μ) (tab st) pads (bit μ) al

/-! ### a valid vector meets the relation after the challenge -/

theorem validQ_mid (m : ℕ) (v : ℕ → ℕ) (T w W : ℕ) (key : ℕ → ℕ → E) (t : ℕ → E)
    (pads : List (ℕ × ℕ)) (M : ℕ → ℕ → E) (hW : W ≤ 2 ^ w) (hin : InParts m v T key t)
    (hP : ∀ e ∈ pads, e.1 < 2 ^ T) (hV : ValidQ m v T w W key t pads M) (al : E) :
    MidQ m v T w W key t pads M al := by
  classical
  have hk : ∀ i ∈ range m, ∀ b ∈ range (2 ^ v i), key i b ∈ (range (2 ^ T)).image t :=
    fun i hi b hb => by
      obtain ⟨u, hu, he⟩ := hin i (mem_range.1 hi) b (mem_range.1 hb)
      exact mem_image.2 ⟨u, mem_range.2 hu, he.symm⟩
  have ht : ∀ u ∈ range (2 ^ T), t u ∈ (range (2 ^ T)).image t := fun u hu => mem_image_of_mem t hu
  have hval : ∀ x : E, ∑ u ∈ (range (2 ^ T)).filter (fun u => t u = x),
      (multOf W M u + padCnt pads u) =
        ∑ i ∈ range m, ((range (2 ^ v i)).filter fun b => key i b = x).card :=
    fun x => by convert hV.2.2 x
  refine ⟨hV.1, ?_, ?_⟩
  · have hsum : ∑ u ∈ range (2 ^ T), (multOf W M u + padCnt pads u) = allKeys m v := by
      rw [← sum_fiberwise_of_maps_to ht, sum_congr rfl fun x _ => hval x, sum_comm]
      unfold allKeys
      refine sum_congr rfl fun i hi => ?_
      rw [← card_eq_sum_card_fiberwise (hk i hi), card_range]
    have hpad : ∑ u ∈ range (2 ^ T), padCnt pads u = padNum pads := by
      rw [sum_range]
      exact sum_padCnt T pads hP
    have hsum' : ∑ u ∈ range (2 ^ T), multOf W M u = allKeys m v - padNum pads := by
      rw [sum_add_distrib, hpad] at hsum
      omega
    unfold Pin
    rw [sum_bits_fin T W M (fun u j => decide (M u j = 1)) fun u hu j hj =>
          eq_ite_of_bit (hV.1 u hu j (lt_of_lt_of_le hj hW)),
      Alg.Lookup.sum_bits_eq W (fun (u : Fin (2 ^ T)) j => decide (M u j = 1))]
    congr 1
    rw [← hsum', sum_range]
    rfl
  · have e : ∀ i ∈ range m, keyProd (v i) (key i) al =
        ∏ x ∈ (range (2 ^ T)).image t,
          (al - x) ^ ((range (2 ^ v i)).filter fun b => key i b = x).card := by
      intro i hi
      unfold keyProd
      rw [← prod_fiberwise_of_maps_to (hk i hi)]
      refine prod_congr rfl fun x _ => ?_
      rw [prod_congr rfl fun b hb => by rw [(mem_filter.1 hb).2], prod_const]
    unfold Ident
    rw [Cb.planes E T w W t M al hW hV.1, prod_range fun u => (al - t u) ^ multOf W M u,
      padFac_mul T t al (fun u : Fin (2 ^ T) => multOf W M u) pads hP,
      ← prod_range fun u => (al - t u) ^ (multOf W M u + padCnt pads u),
      ← prod_fiberwise_of_maps_to ht]
    unfold rootsProd
    rw [prod_congr rfl e, prod_comm]
    refine prod_congr rfl fun x _ => ?_
    rw [prod_pow_eq_pow_sum, ← hval x, ← prod_pow_eq_pow_sum]
    exact prod_congr rfl fun u hu => by rw [(mem_filter.1 hu).2]

theorem validQ_idle (m : ℕ) (v : ℕ → ℕ) (T w W : ℕ) (key : ℕ → ℕ → E) (t : ℕ → E)
    (pads : List (ℕ × ℕ)) (M : ℕ → ℕ → E) (hV : ValidQ m v T w W key t pads M) (al : E) (j : ℕ)
    (h1 : W ≤ j) (h2 : j < 2 ^ w) : tabProd T t M al j = 1 := by
  unfold tabProd
  refine prod_eq_one fun u hu => ?_
  rw [hV.2.1 u (mem_range.1 hu) j h1 h2, zero_mul, add_zero]

/-! ### the honest bits are valid -/

theorem card_split (S : Finset ℕ) (pad : ℕ → Bool) (row : ℕ → ℕ) (u : ℕ) :
    ((S.filter fun b => pad b = false).filter fun b => row b = u).card +
        ((S.filter fun b => pad b = true).filter fun b => row b = u).card =
      (S.filter fun b => row b = u).card := by
  rw [← card_filter_add_card_filter_not (s := S.filter fun b => row b = u) (fun b => pad b = true),
    Nat.add_comm]
  congr 1
  · refine congrArg card (Finset.ext fun b => ?_)
    simp only [mem_filter]
    tauto
  · refine congrArg card (Finset.ext fun b => ?_)
    simp only [mem_filter, Bool.not_eq_true]
    tauto

theorem hbitQ_eq (m : ℕ) (v : ℕ → ℕ) (W : ℕ) (pad : ℕ → ℕ → Bool) (row : ℕ → ℕ → ℕ) (u : ℕ)
    {j : ℕ} (hj : j < W) :
    (hbitQ m v W pad row u j : E) = if (hmultQ m v pad row u).testBit j = true then 1 else 0 := by
  unfold hbitQ
  simp [hj]

theorem hmultQ_le (m : ℕ) (v : ℕ → ℕ) (pad : ℕ → ℕ → Bool) (row : ℕ → ℕ → ℕ) (u : ℕ) :
    hmultQ m v pad row u ≤ allKeys m v := by
  unfold hmultQ allKeys
  refine sum_le_sum fun i _ => ?_
  refine le_trans (card_filter_le _ _) (le_trans (card_filter_le _ _) ?_)
  simp

/-- The multiplicity that the honest bits write. -/
theorem multOf_hbitQ (m : ℕ) (v : ℕ → ℕ) (W : ℕ) (pad : ℕ → ℕ → Bool) (row : ℕ → ℕ → ℕ)
    (hW : allKeys m v < 2 ^ W) (u : ℕ) :
    multOf W (hbitQ m v W pad row : ℕ → ℕ → E) u = hmultQ m v pad row u := by
  classical
  rw [← Alg.Lookup.mult_testBit W (fun u => hmultQ m v pad row u) u
    (lt_of_le_of_lt (hmultQ_le m v pad row u) hW)]
  unfold multOf Alg.Lookup.mult
  refine sum_congr rfl fun j hj => ?_
  show (if decide ((hbitQ m v W pad row u j : E) = 1) = true then 2 ^ j else 0) =
    if (hmultQ m v pad row u).testBit j = true then 2 ^ j else 0
  rw [hbitQ_eq m v W pad row u (mem_range.1 hj)]
  cases (hmultQ m v pad row u).testBit j <;> simp

omit [Field E] in
theorem laidQ_inParts {m : ℕ} {v : ℕ → ℕ} {T : ℕ} {key : ℕ → ℕ → E} {t : ℕ → E}
    {pads : List (ℕ × ℕ)} {pad : ℕ → ℕ → Bool} {row : ℕ → ℕ → ℕ}
    (hL : LaidQ m v T key t pads pad row) : InParts m v T key t :=
  fun i hi b hb => ⟨row i b, hL.rowLt i hi b hb, hL.hit i hi b hb⟩

theorem laidQ_valid (m : ℕ) (v : ℕ → ℕ) (T w W : ℕ) (key : ℕ → ℕ → E) (t : ℕ → E)
    (pads : List (ℕ × ℕ)) (pad : ℕ → ℕ → Bool) (row : ℕ → ℕ → ℕ) (hW : allKeys m v < 2 ^ W)
    (hL : LaidQ m v T key t pads pad row) :
    ValidQ m v T w W key t pads (hbitQ m v W pad row) := by
  classical
  refine ⟨fun u _ j _ => ?_, fun u _ j hj _ => ?_, fun x => ?_⟩
  · unfold hbitQ
    split_ifs <;> simp
  · unfold hbitQ
    rw [if_neg fun h => absurd h.1 (not_lt.2 hj)]
  · -- row by row: not padding + padding = all places that hit the row
    have hrow : ∀ u < 2 ^ T, multOf W (hbitQ m v W pad row : ℕ → ℕ → E) u + padCnt pads u =
        ∑ i ∈ range m, ((range (2 ^ v i)).filter fun b => row i b = u).card := by
      intro u hu
      rw [multOf_hbitQ m v W pad row hW u, hL.laid u hu]
      unfold hmultQ
      rw [← sum_add_distrib]
      exact sum_congr rfl fun i _ => card_split _ (pad i) (row i) u
    have hmap : ∀ i ∈ range m, ∀ b ∈ (range (2 ^ v i)).filter (fun b => key i b = x),
        row i b ∈ (range (2 ^ T)).filter fun u => t u = x := fun i hi b hb =>
      mem_filter.2 ⟨mem_range.2 (hL.rowLt i (mem_range.1 hi) b (mem_range.1 (mem_filter.1 hb).1)),
        (hL.hit i (mem_range.1 hi) b (mem_range.1 (mem_filter.1 hb).1)).symm.trans
          (mem_filter.1 hb).2⟩
    have hgoal : ∑ u ∈ (range (2 ^ T)).filter (fun u => t u = x),
        (multOf W (hbitQ m v W pad row : ℕ → ℕ → E) u + padCnt pads u) =
        ∑ i ∈ range m, ((range (2 ^ v i)).filter fun b => key i b = x).card := by
      rw [sum_congr rfl fun u hu => hrow u (mem_range.1 (mem_filter.1 hu).1), sum_comm]
      refine sum_congr rfl fun i hi => ?_
      rw [card_eq_sum_card_fiberwise (hmap i hi)]
      refine sum_congr rfl fun u hu => ?_
      rw [filter_filter]
      refine congrArg card (filter_congr fun b hb => ?_)
      constructor
      · intro h
        exact ⟨by rw [hL.hit i (mem_range.1 hi) b (mem_range.1 hb), h]; exact (mem_filter.1 hu).2,
          h⟩
      · exact fun h => h.2
    convert hgoal

/-- The honest bits, padding not counted, meet the relation after the challenge at every value. -/
theorem honestQ (m : ℕ) (v : ℕ → ℕ) (T w W : ℕ) (key : ℕ → ℕ → E) (t : ℕ → E)
    (pads : List (ℕ × ℕ)) (pad : ℕ → ℕ → Bool) (row : ℕ → ℕ → ℕ) (hW : W ≤ 2 ^ w)
    (hN : allKeys m v < 2 ^ W) (hP : ∀ e ∈ pads, e.1 < 2 ^ T)
    (hL : LaidQ m v T key t pads pad row) (al : E) :
    MidQ m v T w W key t pads (hbitQ m v W pad row) al :=
  validQ_mid m v T w W key t pads _ hW (laidQ_inParts hL) hP
    (laidQ_valid m v T w W key t pads pad row hN hL) al

/-- If W ≤ 2^w, MidQ reads the entries at u < 2^T, j < 2^w alone. -/
theorem midQ_congr (m : ℕ) (v : ℕ → ℕ) (T w W : ℕ) (key : ℕ → ℕ → E) (t : ℕ → E)
    (pads : List (ℕ × ℕ)) (M M' : ℕ → ℕ → E) (al : E) (hW : W ≤ 2 ^ w)
    (h : ∀ u < 2 ^ T, ∀ j < 2 ^ w, M u j = M' u j) (hM : MidQ m v T w W key t pads M' al) :
    MidQ m v T w W key t pads M al := by
  obtain ⟨h1, h2, h3⟩ := hM
  refine ⟨fun u hu j hj => by rw [h u hu j hj]; exact h1 u hu j hj, ?_, ?_⟩
  · unfold Pin at h2 ⊢
    rw [← h2]
    exact sum_congr rfl fun u hu =>
      sum_congr rfl fun j hj => by
        rw [h u (mem_range.mp hu) j (lt_of_lt_of_le (mem_range.mp hj) hW)]
  · unfold Ident at h3 ⊢
    rw [h3]
    congr 1
    refine prod_congr rfl fun j hj => ?_
    have ht : tabProd T t M al j = tabProd T t M' al j :=
      prod_congr rfl fun u hu => by
        rw [h u (mem_range.mp hu) j (lt_of_lt_of_le (mem_range.mp hj) hW)]
    rw [ht]

theorem multOf_congr (W : ℕ) (M M' : ℕ → ℕ → E) (u : ℕ) (h : ∀ j < W, M u j = M' u j) :
    multOf W M u = multOf W M' u := by
  classical
  unfold multOf Alg.Lookup.mult
  refine sum_congr rfl fun j hj => ?_
  show (if decide (M u j = 1) = true then 2 ^ j else 0) =
    if decide (M' u j = 1) = true then 2 ^ j else 0
  rw [h j (mem_range.1 hj)]

/-- If W ≤ 2^w, ValidQ reads the entries at u < 2^T, j < 2^w alone. -/
theorem validQ_congr (m : ℕ) (v : ℕ → ℕ) (T w W : ℕ) (key : ℕ → ℕ → E) (t : ℕ → E)
    (pads : List (ℕ × ℕ)) (M M' : ℕ → ℕ → E) (hW : W ≤ 2 ^ w)
    (h : ∀ u < 2 ^ T, ∀ j < 2 ^ w, M u j = M' u j) (hV : ValidQ m v T w W key t pads M') :
    ValidQ m v T w W key t pads M := by
  classical
  obtain ⟨h1, h2, h3⟩ := hV
  refine ⟨fun u hu j hj => by rw [h u hu j hj]; exact h1 u hu j hj,
    fun u hu j hj1 hj2 => by rw [h u hu j hj2]; exact h2 u hu j hj1 hj2, fun x => ?_⟩
  rw [← h3 x]
  refine sum_congr rfl fun u hu => ?_
  rw [multOf_congr W M M' u fun j hj =>
    h u (mem_range.1 (mem_filter.1 hu).1) j (lt_of_lt_of_le hj hW)]

/-! ### two predicates that meet MuOnQ -/

/-- "The entries write a valid vector" meets MuOnQ. -/
theorem muOnQ_valid {St J : Type} (m : ℕ) (v : ℕ → ℕ) (T w W : ℕ)
    (key : St → (J → E) → ℕ → ℕ → E) (tab : St → ℕ → E) (pads : List (ℕ × ℕ))
    (bit : (J → E) → ℕ → ℕ → E) (hW : W ≤ 2 ^ w) (hP : ∀ e ∈ pads, e.1 < 2 ^ T) :
    MuOnQ m v T w W key tab pads bit
      fun st μ => ValidQ m v T w W (key st μ) (tab st) pads (bit μ) :=
  fun st μ hin hv al => validQ_mid m v T w W (key st μ) (tab st) pads (bit μ) hW hin hP hv al

/-- "The entries are the digits of the counts, padding not counted" meets MuOnQ. -/
theorem muOnQ_laid {St J : Type} (m : ℕ) (v : ℕ → ℕ) (T w W : ℕ)
    (key : St → (J → E) → ℕ → ℕ → E) (tab : St → ℕ → E) (pads : List (ℕ × ℕ))
    (bit : (J → E) → ℕ → ℕ → E) (pad : ℕ → ℕ → Bool) (row : St → (J → E) → ℕ → ℕ → ℕ)
    (hW : W ≤ 2 ^ w) (hN : allKeys m v < 2 ^ W) (hP : ∀ e ∈ pads, e.1 < 2 ^ T) :
    MuOnQ m v T w W key tab pads bit fun st μ =>
      LaidQ m v T (key st μ) (tab st) pads pad (row st μ) ∧
      ∀ u < 2 ^ T, ∀ j < 2 ^ w, bit μ u j = hbitQ m v W pad (row st μ) u j :=
  fun st μ _ hm al => midQ_congr m v T w W (key st μ) (tab st) pads _ _ al hW hm.2
    (honestQ m v T w W (key st μ) (tab st) pads pad (row st μ) hW hN hP hm.1 al)

/-- At one part, without padding, ValidQ is the library's Valid. -/
theorem validQ_one_nil (v : ℕ → ℕ) (T w W : ℕ) (key : ℕ → ℕ → E) (t : ℕ → E) (M : ℕ → ℕ → E) :
    ValidQ 1 v T w W key t [] M ↔ Cb.LdLkp.Valid (v 0) T w W (key 0) t M := by
  simp [ValidQ, Cb.LdLkp.Valid, padCnt]

end
end Lk6

#print axioms Lk6.validQ_mid
#print axioms Lk6.validQ_idle
#print axioms Lk6.laidQ_valid
#print axioms Lk6.honestQ
#print axioms Lk6.validQ_congr
#print axioms Lk6.muOnQ_valid
#print axioms Lk6.muOnQ_laid
#print axioms Lk6.validQ_one_nil
