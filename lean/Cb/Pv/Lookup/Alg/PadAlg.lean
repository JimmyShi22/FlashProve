-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Alg/PadAlg.lean: the algebra of a lookup whose key vector is padded, without any
protocol.

Definitions, statements (in `Cb.Spec`) and proofs. As Cb/Gen/LkpAlg.lean, with padding.

A lookup shows that every key is a row of a table by comparing two products at a random point: that
of (point - key) over the keys, and that of (point - row) to the power of the row's count over the
rows.
The programs pad the key vector with rows of the table that are public. They leave these places out
of the counts and multiply the table's side by a public factor instead.

States: padNum, padCnt, padsOK (a test on public numbers), padFac (the public factor), NumKeysP (the
counts sum to the number of keys that are not padding), MidP (the claim after the point is drawn).
  cnt_badAl_pad_le: if a key is no row of the table, MidP holds for at most 2^n - 1 values of the
    point: the number without padding (conditions: E finite, W ≤ 2^w, 2^n < 2^W, 2^T (2^W - 1) < p,
    the characteristic, and padsOK).
  honestP: with the true counts, padding not counted (hbitP), MidP holds at every value of the point
    (conditions: 2^n < 2^W, padsOK, and LaidP: every key is the row chosen for it, and pads counts
    the padding positions row by row).
  midP_nil: without padding MidP is Mid (Cb/Gen/LkpAlg.lean).
Limits: padsOK is needed: with a padding "row" outside the table the count is false. pads is a list
of (row, how many). MidP does not say which keys are padding: InTable speaks of all 2^n keys.
That the programs pad so (OnBytes/Model/Look.lean, `Forest.pad`) is read off their text: no
statement here says so.

-/
import Cb.Gen.LkpAlgProofs

set_option autoImplicit false

namespace Cb.Lkp
open Finset

/-- How many padding keys there are. -/
def padNum (pads : List (ℕ × ℕ)) : ℕ := (pads.map Prod.snd).sum

/-- How many padding keys hold the row u. -/
def padCnt (pads : List (ℕ × ℕ)) (u : ℕ) : ℕ := (pads.map fun e => if e.1 = u then e.2 else 0).sum

/-- The test on the public numbers: every padding row is a row of the table; there are at most as
many padding keys as keys. -/
def padsOK (n T : ℕ) (pads : List (ℕ × ℕ)) : Bool :=
  pads.all (fun e => decide (e.1 < 2 ^ T)) && decide (padNum pads ≤ 2 ^ n)

theorem padsOK_in {n T : ℕ} {pads : List (ℕ × ℕ)} (h : padsOK n T pads = true) :
    ∀ e ∈ pads, e.1 < 2 ^ T := fun e he =>
  of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1 e he)

theorem padsOK_le {n T : ℕ} {pads : List (ℕ × ℕ)} (h : padsOK n T pads = true) :
    padNum pads ≤ 2 ^ n := of_decide_eq_true (Bool.and_eq_true_iff.mp h).2

variable {E : Type} [Field E]

/-- The public factor: the product of (al - padding key) over all padding keys. -/
def padFac (t : ℕ → E) (pads : List (ℕ × ℕ)) (al : E) : E :=
  (pads.map fun e => (al - t e.1) ^ e.2).prod

/-- The multiplicities sum to the number of keys that are not padding (P: how many are padding). -/
def NumKeysP (n T W P : ℕ) (M : ℕ → ℕ → E) : Prop :=
  ∑ u ∈ range (2 ^ T), ∑ j ∈ range W, (2 : E) ^ j * M u j = ((2 ^ n - P : ℕ) : E)

/-- The relation after the challenge, with the public factor. -/
def MidP (n T w W : ℕ) (key t : ℕ → E) (pads : List (ℕ × ℕ)) (M : ℕ → ℕ → E) (al : E) : Prop :=
  Bits T w M ∧ NumKeysP n T W (padNum pads) M ∧
  keyProd n key al = padFac t pads al * ∏ j ∈ range W, tabProd T t M al j ^ 2 ^ j

/-! ### the factor as further multiplicities -/

theorem prod_pow_single (T : ℕ) (t : ℕ → E) (al : E) (r c : ℕ) (hr : r < 2 ^ T) :
    ∏ u : Fin (2 ^ T), (al - t u) ^ (if r = (u : ℕ) then c else 0) = (al - t r) ^ c := by
  rw [Finset.prod_eq_single (⟨r, hr⟩ : Fin (2 ^ T))]
  · simp
  · intro b _ hb
    have hne : r ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sum_single (T r c : ℕ) (hr : r < 2 ^ T) :
    ∑ u : Fin (2 ^ T), (if r = (u : ℕ) then c else 0) = c := by
  rw [Finset.sum_eq_single (⟨r, hr⟩ : Fin (2 ^ T))]
  · simp
  · intro b _ hb
    have hne : r ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The factor times the table's side is the table's side with the padding counted in. -/
theorem padFac_mul (T : ℕ) (t : ℕ → E) (al : E) (m : Fin (2 ^ T) → ℕ) :
    ∀ pads : List (ℕ × ℕ), (∀ e ∈ pads, e.1 < 2 ^ T) →
      padFac t pads al * ∏ u : Fin (2 ^ T), (al - t u) ^ m u =
        ∏ u : Fin (2 ^ T), (al - t u) ^ (m u + padCnt pads u)
  | [], _ => by simp [padFac, padCnt]
  | e :: pads, h => by
    have ih := padFac_mul T t al m pads fun e' he' => h e' (List.mem_cons_of_mem _ he')
    have he : e.1 < 2 ^ T := h e List.mem_cons_self
    have e1 : padFac t (e :: pads) al = (al - t e.1) ^ e.2 * padFac t pads al := by
      simp [padFac]
    have e2 : ∀ u : ℕ, padCnt (e :: pads) u = (if e.1 = u then e.2 else 0) + padCnt pads u := by
      intro u
      simp [padCnt]
    rw [e1, mul_assoc, ih, ← prod_pow_single T t al e.1 e.2 he, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun u _ => ?_
    rw [e2, ← pow_add]
    congr 1
    omega

theorem sum_padCnt (T : ℕ) :
    ∀ pads : List (ℕ × ℕ), (∀ e ∈ pads, e.1 < 2 ^ T) →
      ∑ u : Fin (2 ^ T), padCnt pads u = padNum pads
  | [], _ => by simp [padNum, padCnt]
  | e :: pads, h => by
    have ih := sum_padCnt T pads fun e' he' => h e' (List.mem_cons_of_mem _ he')
    have he : e.1 < 2 ^ T := h e List.mem_cons_self
    have e2 : ∀ u : ℕ, padCnt (e :: pads) u = (if e.1 = u then e.2 else 0) + padCnt pads u := by
      intro u
      simp [padCnt]
    have e3 : padNum (e :: pads) = e.2 + padNum pads := by simp [padNum]
    simp only [e2]
    rw [Finset.sum_add_distrib, sum_single T e.1 e.2 he, ih, e3]

/-! ### the honest side -/

/-- The honest multiplicity of the row u: the number of positions that are not padding and whose key
hits the row u, by the prover's own choice of rows. -/
def hmultP (n : ℕ) (pad : ℕ → Bool) (row : ℕ → ℕ) (u : ℕ) : ℕ :=
  (((range (2 ^ n)).filter fun b => pad b = false).filter fun b => row b = u).card

/-- The honest bits. -/
def hbitP (n W : ℕ) (pad : ℕ → Bool) (row : ℕ → ℕ) (u j : ℕ) : E :=
  if j < W ∧ (hmultP n pad row u).testBit j = true then 1 else 0

/-- What the honest side knows: every key is the row that the prover chose for it; the public list
of padding counts the padding positions, row by row. -/
structure LaidP (n T : ℕ) (key t : ℕ → E) (pads : List (ℕ × ℕ)) (pad : ℕ → Bool) (row : ℕ → ℕ) :
    Prop where
  rowLt : ∀ b < 2 ^ n, row b < 2 ^ T
  hit   : ∀ b < 2 ^ n, key b = t (row b)
  laid  : ∀ u < 2 ^ T,
    padCnt pads u = (((range (2 ^ n)).filter fun b => pad b = true).filter fun b => row b = u).card

theorem prod_fiber (S : Finset ℕ) (row : ℕ → ℕ) (T : ℕ) (t : ℕ → E) (al : E)
    (h : ∀ b ∈ S, row b < 2 ^ T) :
    ∏ b ∈ S, (al - t (row b)) =
      ∏ u ∈ range (2 ^ T), (al - t u) ^ (S.filter fun b => row b = u).card := by
  rw [← Finset.prod_fiberwise_of_maps_to (s := S) (t := range (2 ^ T)) (g := row)
    fun b hb => mem_range.mpr (h b hb)]
  refine Finset.prod_congr rfl fun u _ => ?_
  rw [Finset.prod_congr rfl fun b hb => by rw [(mem_filter.mp hb).2], Finset.prod_const]

theorem card_fiber (S : Finset ℕ) (row : ℕ → ℕ) (T : ℕ) (h : ∀ b ∈ S, row b < 2 ^ T) :
    S.card = ∑ u ∈ range (2 ^ T), (S.filter fun b => row b = u).card :=
  Finset.card_eq_sum_card_fiberwise fun b hb => mem_coe.mpr (mem_range.mpr (h b (mem_coe.mp hb)))

theorem hbitP_eq (n W : ℕ) (pad : ℕ → Bool) (row : ℕ → ℕ) (u : ℕ) {j : ℕ} (hj : j < W) :
    (hbitP n W pad row u j : E) = if (hmultP n pad row u).testBit j = true then 1 else 0 := by
  unfold hbitP
  simp [hj]

theorem hmultP_lt (n W : ℕ) (pad : ℕ → Bool) (row : ℕ → ℕ) (h : 2 ^ n < 2 ^ W) (u : ℕ) :
    hmultP n pad row u < 2 ^ W := by
  refine lt_of_le_of_lt ?_ h
  unfold hmultP
  refine le_trans (card_filter_le _ _) (le_trans (card_filter_le _ _) ?_)
  simp

theorem mult_hmultP (n T W : ℕ) (pad : ℕ → Bool) (row : ℕ → ℕ) (h : 2 ^ n < 2 ^ W)
    (u : Fin (2 ^ T)) :
    Alg.Lookup.mult W (fun (u : Fin (2 ^ T)) j => (hmultP n pad row u).testBit j) u =
      hmultP n pad row u :=
  Alg.Lookup.mult_testBit W (fun u : Fin (2 ^ T) => hmultP n pad row u) u (hmultP_lt n W pad row h
      u)

end Cb.Lkp

namespace Cb.Spec
open Finset Prob Cb.Lkp

/-- The bad values of the challenge, with the public factor: the same count as without. -/
def cnt_badAl_pad_le : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (p : ℕ) [CharP E p] (n T w W : ℕ)
      (key t : ℕ → E) (pads : List (ℕ × ℕ)) (M : ℕ → ℕ → E),
    W ≤ 2 ^ w → 2 ^ n < 2 ^ W → 2 ^ T * (2 ^ W - 1) < p → padsOK n T pads = true →
    ¬ InTable n T key t →
    cnt (fun al : E => MidP n T w W key t pads M al) ≤ 2 ^ n - 1

/-- The honest bits, padding not counted, meet the relation after the challenge at every value. -/
def honestP : Prop :=
  ∀ (E : Type) [Field E] (n T w W : ℕ) (key t : ℕ → E) (pads : List (ℕ × ℕ))
      (pad : ℕ → Bool) (row : ℕ → ℕ),
    2 ^ n < 2 ^ W → padsOK n T pads = true → LaidP n T key t pads pad row →
    ∀ al, MidP n T w W key t pads (hbitP n W pad row) al

/-- With no padding the relation is `Mid` (Cb/Gen/LkpAlg.lean). -/
def midP_nil : Prop :=
  ∀ (E : Type) [Field E] (n T w W : ℕ) (key t : ℕ → E) (M : ℕ → ℕ → E) (al : E),
    MidP n T w W key t [] M al ↔ Mid n T w W key t M al

end Cb.Spec

namespace Cb
open Finset Prob Cb.Lkp

theorem midP_nil : Spec.midP_nil := by
  intro E _ n T w W key t M al
  simp [MidP, Mid, NumKeysP, NumKeys, padNum, padFac]

/-- If W ≤ 2^w, MidP reads the bits at u < 2^T, j < 2^w only (as `LdLkp.mid_congr`,
Cb/Ld/LdLkpProofs.lean). -/
theorem Lkp.midP_congr {E : Type} [Field E] (n T w W : ℕ) (key t : ℕ → E) (pads : List (ℕ × ℕ))
    (M M' : ℕ → ℕ → E) (al : E) (hW : W ≤ 2 ^ w)
    (h : ∀ u < 2 ^ T, ∀ j < 2 ^ w, M u j = M' u j) (hM : MidP n T w W key t pads M' al) :
    MidP n T w W key t pads M al := by
  obtain ⟨h1, h2, h3⟩ := hM
  refine ⟨fun u hu j hj => by rw [h u hu j hj]; exact h1 u hu j hj, ?_, ?_⟩
  · unfold NumKeysP at h2 ⊢
    rw [← h2]
    exact sum_congr rfl fun u hu =>
      sum_congr rfl fun j hj => by
        rw [h u (mem_range.mp hu) j (lt_of_lt_of_le (mem_range.mp hj) hW)]
  · rw [h3]
    congr 1
    refine prod_congr rfl fun j hj => ?_
    have ht : tabProd T t M al j = tabProd T t M' al j :=
      prod_congr rfl fun u hu => by
        rw [h u (mem_range.mp hu) j (lt_of_lt_of_le (mem_range.mp hj) hW)]
    rw [ht]

theorem cnt_badAl_pad_le : Spec.cnt_badAl_pad_le := by
  classical
  intro E _ _ p _ n T w W key t pads M hW hnW hp hpads hnot
  have hin := padsOK_in hpads
  have hle := padsOK_le hpads
  by_cases hBN : Bits T w M ∧ NumKeysP n T W (padNum pads) M
  · obtain ⟨hB, hN⟩ := hBN
    have hM : ∀ u < 2 ^ T, ∀ j < W, M u j = if decide (M u j = 1) = true then 1 else 0 :=
      fun u hu j hj => eq_ite_of_bit (hB u hu j (lt_of_lt_of_le hj hW))
    set β : Fin (2 ^ T) → ℕ → Bool := fun u j => decide (M u j = 1) with hβ
    have h1 : ∑ u, Alg.Lookup.mult W β u < p := by
      refine lt_of_le_of_lt ?_ hp
      have := Finset.sum_le_card_nsmul (univ : Finset (Fin (2 ^ T))) (Alg.Lookup.mult W β)
        (2 ^ W - 1) fun u _ => Nat.le_sub_one_of_lt (Alg.Lookup.mult_lt W β u)
      simpa using this
    have h2 : 2 ^ n - padNum pads < p := by
      refine lt_of_le_of_lt ?_ hp
      have h3 : 2 ^ n ≤ 2 ^ W - 1 := Nat.le_sub_one_of_lt hnW
      exact le_trans (Nat.sub_le _ _) (le_trans h3 (Nat.le_mul_of_pos_left _ (by positivity)))
    have hsum : ∑ u, Alg.Lookup.mult W β u = 2 ^ n - padNum pads := by
      refine Alg.Lookup.sum_mult_eq (E := E) p W β (2 ^ n - padNum pads) ?_ h1 h2
      rw [← hN, sum_bits_fin T W M (fun u j => decide (M u j = 1)) hM]
    unfold InTable at hnot
    push Not at hnot
    obtain ⟨b, hb, hbt⟩ := hnot
    have hc := Alg.Lookup.count_badAlpha_le (fun i : Fin (2 ^ n) => key i)
      (fun u : Fin (2 ^ T) => t u) ⟨0, by positivity⟩ 0
      (fun u : Fin (2 ^ T) => Alg.Lookup.mult W β u + padCnt pads u)
    rw [Fintype.card_fin] at hc
    refine le_trans (cnt_mono fun al hal => ?_) hc
    refine ⟨?_, ⟨⟨b, hb⟩, fun u => hbt u u.2⟩, ?_⟩
    · rw [Nat.zero_add, Finset.sum_add_distrib, hsum, sum_padCnt T pads hin, Fintype.card_fin]
      omega
    · rw [pow_zero, one_mul, ← padFac_mul T t al (Alg.Lookup.mult W β) pads hin,
        ← planes_fin T W t M al (fun u j => decide (M u j = 1)) hM, ← hal.2.2]
      unfold keyProd
      rw [prod_range]
  · rw [cnt_false fun al hal => hBN ⟨hal.1, hal.2.1⟩]
    exact Nat.zero_le _

theorem honestP : Spec.honestP := by
  intro E _ n T w W key t pads pad row hW hpads hL al
  have hin := padsOK_in hpads
  have hle := padsOK_le hpads
  set S0 : Finset ℕ := (range (2 ^ n)).filter fun b => pad b = false with hS0
  set S1 : Finset ℕ := (range (2 ^ n)).filter fun b => pad b = true with hS1
  have r0 : ∀ b ∈ S0, row b < 2 ^ T := fun b hb =>
    hL.rowLt b (mem_range.mp (mem_filter.mp hb).1)
  have r1 : ∀ b ∈ S1, row b < 2 ^ T := fun b hb =>
    hL.rowLt b (mem_range.mp (mem_filter.mp hb).1)
  have hβ : ∀ u < 2 ^ T, ∀ j < W, (hbitP n W pad row u j : E) =
      if (hmultP n pad row u).testBit j = true then 1 else 0 :=
    fun u _ j hj => hbitP_eq n W pad row u hj
  -- the number of padding positions is the public number
  have c1 : S1.card = padNum pads := by
    rw [card_fiber S1 row T r1, ← sum_padCnt T pads hin, Finset.sum_range]
    exact Finset.sum_congr rfl fun u _ => (hL.laid u u.2).symm
  have c01 : S1.card + S0.card = 2 ^ n := by
    have h := Finset.card_filter_add_card_filter_not (s := range (2 ^ n))
      (fun b => pad b = true)
    rw [card_range] at h
    have e : ((range (2 ^ n)).filter fun b => ¬ pad b = true) = S0 := by
      rw [hS0]
      exact Finset.filter_congr fun b _ => by simp
    rw [e] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · intro u _ j _
    unfold hbitP
    split_ifs <;> simp
  · unfold NumKeysP
    rw [sum_bits_fin T W (hbitP n W pad row) (fun u j => (hmultP n pad row u).testBit j) hβ,
      Alg.Lookup.sum_bits_eq W (fun (u : Fin (2 ^ T)) j => (hmultP n pad row u).testBit j)]
    congr 1
    have e : ∑ u : Fin (2 ^ T),
        Alg.Lookup.mult W (fun (u : Fin (2 ^ T)) j => (hmultP n pad row u).testBit j) u =
        S0.card := by
      rw [card_fiber S0 row T r0, Finset.sum_range]
      exact Finset.sum_congr rfl fun u _ => mult_hmultP n T W pad row hW u
    rw [e]
    omega
  · rw [planes_fin T W t (hbitP n W pad row) al (fun u j => (hmultP n pad row u).testBit j) hβ]
    have eK : keyProd n key al = (∏ b ∈ S1, (al - t (row b))) * ∏ b ∈ S0, (al - t (row b)) := by
      unfold keyProd
      rw [Finset.prod_congr rfl fun b hb => by rw [hL.hit b (mem_range.mp hb)],
        ← Finset.prod_filter_mul_prod_filter_not (range (2 ^ n)) fun b => pad b = true]
      congr 1
      exact Finset.prod_congr (Finset.filter_congr fun b _ => by simp) fun _ _ => rfl
    have e1 : ∏ b ∈ S1, (al - t (row b)) = padFac t pads al := by
      have h := padFac_mul T t al (fun _ => 0) pads hin
      simp only [pow_zero, Finset.prod_const_one, mul_one, Nat.zero_add] at h
      rw [h, prod_fiber S1 row T t al r1, Finset.prod_range]
      exact Finset.prod_congr rfl fun u _ => by rw [hL.laid u u.2]
    have e0 : ∏ b ∈ S0, (al - t (row b)) =
        ∏ u : Fin (2 ^ T), (al - t u) ^
          Alg.Lookup.mult W (fun (u : Fin (2 ^ T)) j => (hmultP n pad row u).testBit j) u := by
      rw [prod_fiber S0 row T t al r0, Finset.prod_range]
      exact Finset.prod_congr rfl fun u _ => by rw [mult_hmultP n T W pad row hW u]; rfl
    rw [eK, e1, e0]

end Cb
