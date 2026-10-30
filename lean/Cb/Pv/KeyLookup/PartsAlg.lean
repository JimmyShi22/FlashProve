-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/PartsAlg.lean: the identity behind a lookup whose keys come in parts, with public
padding: at how many values of the challenge it can hold while some key is no row of the table.

Plain mathematics: no protocol, no oracle. The file imports no file of the program.

The setting. Part i < m has 2^(v i) keys, key i b. The table has 2^T rows, t u. How often a row is
used is written in bits M u j, in W real planes of 2^w places. pads is a public list of pairs (a row
of the table, how many places of padding hold it), as in Cb/Pv/Lookup/Alg/PadAlg.lean.

Main definitions.
  allKeys m v   the number of all keys, padding counted: the sum of the 2^(v i).
  InParts       every key of every part is a row of the table: Cb.Lkp.InTable for each part.
  rootsProd     the product over the parts of the product of al - key.
  restProd      the same from part i on.
  Pin           the counts add up, in the field, to the number of keys that are not padding.
  Ident         rootsProd = the public factor times the product of (plane j's product)^(2^j).
  MidQ          the claim after the challenge: all entries are bits, Pin, Ident.
  padsOKQ       a test on public numbers: every padding row is a row of the table, and there is no
                more padding than keys.
  Adm           the conditions on public numbers: W ≤ 2^w; allKeys < 2^W; 2^T (2^W - 1) < p.
  BadAl         the challenge is bad: MidQ holds at it, yet some key of some part is no row.
  padPoly       the public factor as a polynomial in the challenge.
Main theorems.
  cnt_ident_le  if the entries of the real planes are bits, Pin holds and some key is no row, then
                Ident holds at no more than allKeys - 1 values of the challenge. The proof calls
                Alg.Lookup.count_badAlpha_le at the sum type over the parts; the padding is counted
                into the multiplicities. Nothing is read of places j ≥ W.
  cnt_mid_le, cnt_badAl_le   the same of MidQ and of BadAl, under Adm and padsOKQ.
  inParts_of_mid   MidQ at a challenge that is not bad gives InParts: the definition of BadAl,
                turned round.
  err_lt_card   under Adm, with p the characteristic, allKeys - 1 is below the number of elements of
                the field.
  midQ_one, midQ_one_nil, inParts_one   at one part MidQ is Cb.Lkp.MidP, without padding Cb.Lkp.Mid,
                and InParts is Cb.Lkp.InTable. These three see nothing that vanishes at one part. At
                two parts or more MidQ is held from two sides: by cnt_mid_le, and by honestQ of
                Cb/Pv/KeyLookup/PartsMu.lean.
  padPoly_eval, padPoly_monic, padPoly_natDegree, padPoly_ne_one   the factor is the value of a
                monic polynomial whose degree is the number of places of padding; with padding it is
                not the polynomial 1.
  padFac_eq_zero, padFac_ne_one_at   at a padding row that is held at least once the factor is 0, so
                it is not 1 as a function either.
  restProd_zero, restProd_step, restProd_last   the product of the roots, root by root.

Conditions: on public numbers alone (Adm, padsOKQ). None reads a witness. Why padsOKQ is asked: a
padding row outside the table could cancel a key outside the table.

Not claimed. Anything on rounds, blocks or knowledge soundness. That pads is a program's list. What
the counts of an honest prover satisfy (Cb/Pv/KeyLookup/PartsMu.lean). The proof of cnt_ident_le is
after cnt_badAl_pad_le of Cb/Pv/Lookup/Alg/PadAlg.lean.

-/
import Cb.Pv.Lookup.Alg.PadAlg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Finset Prob Cb.Lkp

/-! ## Public numbers -/

/-- The number of all keys, padding counted. -/
def allKeys (m : ℕ) (v : ℕ → ℕ) : ℕ := ∑ i ∈ range m, 2 ^ v i

/-- The test on the public numbers: every padding row is a row of the table; there are at most as
many padding keys as keys (N). -/
def padsOKQ (N T : ℕ) (pads : List (ℕ × ℕ)) : Bool :=
  pads.all (fun e => decide (e.1 < 2 ^ T)) && decide (padNum pads ≤ N)

theorem padsOKQ_in {N T : ℕ} {pads : List (ℕ × ℕ)} (h : padsOKQ N T pads = true) :
    ∀ e ∈ pads, e.1 < 2 ^ T := fun e he =>
  of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1 e he)

theorem padsOKQ_le {N T : ℕ} {pads : List (ℕ × ℕ)} (h : padsOKQ N T pads = true) :
    padNum pads ≤ N := of_decide_eq_true (Bool.and_eq_true_iff.mp h).2

/-- The conditions on the public numbers; p is the characteristic where a statement says so. -/
structure Adm (p m : ℕ) (v : ℕ → ℕ) (T w W : ℕ) : Prop where
  live : W ≤ 2 ^ w
  fits : allKeys m v < 2 ^ W
  char : 2 ^ T * (2 ^ W - 1) < p

theorem card_idx (m : ℕ) (v : ℕ → ℕ) :
    Fintype.card (Σ i : Fin m, Fin (2 ^ v i)) = allKeys m v := by
  unfold allKeys
  rw [Fintype.card_sigma, Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ => Fintype.card_fin _

/-! ## The claims -/

section
variable {E : Type} [Field E]

/-- Every key of every part is a row of the table. -/
def InParts (m : ℕ) (v : ℕ → ℕ) (T : ℕ) (key : ℕ → ℕ → E) (t : ℕ → E) : Prop :=
  ∀ i < m, InTable (v i) T (key i) t

/-- The product of the parts' roots. -/
def rootsProd (m : ℕ) (v : ℕ → ℕ) (key : ℕ → ℕ → E) (al : E) : E :=
  ∏ i ∈ range m, keyProd (v i) (key i) al

/-- The product of the roots of the parts i, .., m - 1. -/
def restProd (m : ℕ) (v : ℕ → ℕ) (key : ℕ → ℕ → E) (al : E) (i : ℕ) : E :=
  ∏ k ∈ Ico i m, keyProd (v k) (key k) al

/-- The pin: the multiplicities sum, in E, to the number of keys that are not padding. -/
def Pin (N T W P : ℕ) (M : ℕ → ℕ → E) : Prop :=
  ∑ u ∈ range (2 ^ T), ∑ j ∈ range W, (2 : E) ^ j * M u j = ((N - P : ℕ) : E)

/-- The identity at the challenge. -/
def Ident (m : ℕ) (v : ℕ → ℕ) (T W : ℕ) (key : ℕ → ℕ → E) (t : ℕ → E) (pads : List (ℕ × ℕ))
    (M : ℕ → ℕ → E) (al : E) : Prop :=
  rootsProd m v key al = padFac t pads al * ∏ j ∈ range W, tabProd T t M al j ^ 2 ^ j

/-- The relation after the challenge. -/
def MidQ (m : ℕ) (v : ℕ → ℕ) (T w W : ℕ) (key : ℕ → ℕ → E) (t : ℕ → E) (pads : List (ℕ × ℕ))
    (M : ℕ → ℕ → E) (al : E) : Prop :=
  Bits T w M ∧ Pin (allKeys m v) T W (padNum pads) M ∧ Ident m v T W key t pads M al

/-- The challenge is bad: the relation after it holds, yet some key is no row of the table. -/
def BadAl (m : ℕ) (v : ℕ → ℕ) (T w W : ℕ) (key : ℕ → ℕ → E) (t : ℕ → E) (pads : List (ℕ × ℕ))
    (M : ℕ → ℕ → E) (al : E) : Prop :=
  MidQ m v T w W key t pads M al ∧ ¬ InParts m v T key t

theorem rootsProd_sigma (m : ℕ) (v : ℕ → ℕ) (key : ℕ → ℕ → E) (al : E) :
    rootsProd m v key al = ∏ x : (Σ i : Fin m, Fin (2 ^ v i)), (al - key x.1 x.2) := by
  unfold rootsProd keyProd
  rw [Fintype.prod_sigma, Finset.prod_range]
  exact Finset.prod_congr rfl fun i _ => Finset.prod_range _

theorem restProd_zero (m : ℕ) (v : ℕ → ℕ) (key : ℕ → ℕ → E) (al : E) :
    restProd m v key al 0 = rootsProd m v key al := by
  unfold restProd rootsProd
  rw [Finset.range_eq_Ico]

theorem restProd_step (m : ℕ) (v : ℕ → ℕ) (key : ℕ → ℕ → E) (al : E) {i : ℕ} (hi : i < m) :
    restProd m v key al i = keyProd (v i) (key i) al * restProd m v key al (i + 1) :=
  Finset.prod_eq_prod_Ico_succ_bot hi _

theorem restProd_last (m : ℕ) (v : ℕ → ℕ) (key : ℕ → ℕ → E) (al : E) :
    restProd (m + 1) v key al m = keyProd (v m) (key m) al := by
  unfold restProd
  rw [Nat.Ico_succ_singleton, Finset.prod_singleton]

theorem inParts_of_mid {m : ℕ} {v : ℕ → ℕ} {T w W : ℕ} {key : ℕ → ℕ → E} {t : ℕ → E}
    {pads : List (ℕ × ℕ)} {M : ℕ → ℕ → E} {al : E} (h : MidQ m v T w W key t pads M al)
    (hb : ¬ BadAl m v T w W key t pads M al) : InParts m v T key t :=
  Classical.byContradiction fun hn => hb ⟨h, hn⟩

/-- At one part the relation is `Cb.Lkp.MidP`. -/
theorem midQ_one (v : ℕ → ℕ) (T w W : ℕ) (key : ℕ → ℕ → E) (t : ℕ → E) (pads : List (ℕ × ℕ))
    (M : ℕ → ℕ → E) (al : E) :
    MidQ 1 v T w W key t pads M al ↔ MidP (v 0) T w W (key 0) t pads M al := by
  simp [MidQ, MidP, Pin, NumKeysP, Ident, rootsProd, allKeys]

/-- At one part, without padding, the relation is `Cb.Lkp.Mid`. -/
theorem midQ_one_nil (v : ℕ → ℕ) (T w W : ℕ) (key : ℕ → ℕ → E) (t : ℕ → E) (M : ℕ → ℕ → E)
    (al : E) : MidQ 1 v T w W key t [] M al ↔ Mid (v 0) T w W (key 0) t M al :=
  (midQ_one v T w W key t [] M al).trans (Cb.midP_nil E (v 0) T w W (key 0) t M al)

omit [Field E] in
/-- At one part the claim on the keys is `Cb.Lkp.InTable`. -/
theorem inParts_one (v : ℕ → ℕ) (T : ℕ) (key : ℕ → ℕ → E) (t : ℕ → E) :
    InParts 1 v T key t ↔ InTable (v 0) T (key 0) t :=
  ⟨fun h => h 0 Nat.one_pos, fun h i hi => by
    obtain rfl : i = 0 := by omega
    exact h⟩

end

/-! ## The count -/

section
variable {E : Type} [Field E] [Fintype E]

/-- THE COUNT. The live entries are bits, the pin holds, some key of some part is no row of the
table: the identity holds at no more than allKeys - 1 values of the challenge. -/
theorem cnt_ident_le (p : ℕ) [CharP E p] (m : ℕ) (v : ℕ → ℕ) (T W : ℕ) (key : ℕ → ℕ → E)
    (t : ℕ → E) (pads : List (ℕ × ℕ)) (M : ℕ → ℕ → E) (hN : allKeys m v < 2 ^ W)
    (hp : 2 ^ T * (2 ^ W - 1) < p) (hP : padsOKQ (allKeys m v) T pads = true)
    (hB : ∀ u < 2 ^ T, ∀ j < W, M u j * (M u j - 1) = 0)
    (hPin : Pin (allKeys m v) T W (padNum pads) M) (hnot : ¬ InParts m v T key t) :
    cnt (fun al : E => Ident m v T W key t pads M al) ≤ allKeys m v - 1 := by
  classical
  have hin := padsOKQ_in hP
  have hle := padsOKQ_le hP
  have hM : ∀ u < 2 ^ T, ∀ j < W, M u j = if decide (M u j = 1) = true then 1 else 0 :=
    fun u hu j hj => eq_ite_of_bit (hB u hu j hj)
  set β : Fin (2 ^ T) → ℕ → Bool := fun u j => decide (M u j = 1) with hβ
  have h1 : ∑ u, Alg.Lookup.mult W β u < p := by
    refine lt_of_le_of_lt ?_ hp
    have := Finset.sum_le_card_nsmul (univ : Finset (Fin (2 ^ T))) (Alg.Lookup.mult W β)
      (2 ^ W - 1) fun u _ => Nat.le_sub_one_of_lt (Alg.Lookup.mult_lt W β u)
    simpa using this
  have h2 : allKeys m v - padNum pads < p := by
    refine lt_of_le_of_lt ?_ hp
    have h3 : allKeys m v ≤ 2 ^ W - 1 := Nat.le_sub_one_of_lt hN
    exact le_trans (Nat.sub_le _ _) (le_trans h3 (Nat.le_mul_of_pos_left _ (by positivity)))
  have hsum : ∑ u, Alg.Lookup.mult W β u = allKeys m v - padNum pads := by
    refine Alg.Lookup.sum_mult_eq (E := E) p W β (allKeys m v - padNum pads) ?_ h1 h2
    rw [← hPin, sum_bits_fin T W M (fun u j => decide (M u j = 1)) hM]
  have hex : ∃ i, i < m ∧ ∃ b, b < 2 ^ v i ∧ ∀ u < 2 ^ T, key i b ≠ t u := by
    by_contra hcon
    refine hnot fun i hi b hb => ?_
    by_contra hc2
    exact hcon ⟨i, hi, b, hb, fun u hu he => hc2 ⟨u, hu, he⟩⟩
  obtain ⟨i, hi, b, hb, hbt⟩ := hex
  have hc := Alg.Lookup.count_badAlpha_le
    (fun x : (Σ i : Fin m, Fin (2 ^ v i)) => key x.1 x.2)
    (fun u : Fin (2 ^ T) => t u) ⟨0, by positivity⟩ 0
    (fun u : Fin (2 ^ T) => Alg.Lookup.mult W β u + padCnt pads u)
  rw [card_idx] at hc
  refine le_trans (cnt_mono fun al hal => ?_) hc
  refine ⟨?_, ⟨⟨⟨i, hi⟩, ⟨b, hb⟩⟩, fun u => hbt u u.2⟩, ?_⟩
  · rw [Nat.zero_add, Finset.sum_add_distrib, hsum, sum_padCnt T pads hin, card_idx]
    omega
  · rw [pow_zero, one_mul, ← padFac_mul T t al (Alg.Lookup.mult W β) pads hin,
      ← planes_fin T W t M al (fun u j => decide (M u j = 1)) hM, ← rootsProd_sigma]
    exact hal

/-- The count, of the relation after the challenge. -/
theorem cnt_mid_le (p : ℕ) [CharP E p] (m : ℕ) (v : ℕ → ℕ) (T w W : ℕ) (key : ℕ → ℕ → E)
    (t : ℕ → E) (pads : List (ℕ × ℕ)) (M : ℕ → ℕ → E) (hA : Adm p m v T w W)
    (hP : padsOKQ (allKeys m v) T pads = true) (hnot : ¬ InParts m v T key t) :
    cnt (fun al : E => MidQ m v T w W key t pads M al) ≤ allKeys m v - 1 := by
  by_cases hBN : Bits T w M ∧ Pin (allKeys m v) T W (padNum pads) M
  · refine le_trans (cnt_mono fun al h => ?_)
      (cnt_ident_le p m v T W key t pads M hA.fits hA.char hP
        (fun u hu j hj => hBN.1 u hu j (lt_of_lt_of_le hj hA.live)) hBN.2 hnot)
    exact h.2.2
  · rw [cnt_false fun al hal => hBN ⟨hal.1, hal.2.1⟩]
    exact Nat.zero_le _

/-- The count of the bad challenges, for fixed keys, table and entries. -/
theorem cnt_badAl_le (p : ℕ) [CharP E p] (m : ℕ) (v : ℕ → ℕ) (T w W : ℕ) (key : ℕ → ℕ → E)
    (t : ℕ → E) (pads : List (ℕ × ℕ)) (M : ℕ → ℕ → E) (hA : Adm p m v T w W)
    (hP : padsOKQ (allKeys m v) T pads = true) :
    cnt (fun al : E => BadAl m v T w W key t pads M al) ≤ allKeys m v - 1 := by
  by_cases hin : InParts m v T key t
  · rw [cnt_false fun al h => h.2 hin]
    exact Nat.zero_le _
  · refine le_trans (cnt_mono fun al h => ?_) (cnt_mid_le p m v T w W key t pads M hA hP hin)
    exact h.1

theorem char_le_card (p : ℕ) [CharP E p] : p ≤ Fintype.card E := by
  have h := Fintype.card_le_of_injective (fun i : Fin p => ((i : ℕ) : E)) fun a b hab =>
    Fin.ext (Nat.ModEq.eq_of_lt_of_lt ((CharP.natCast_eq_natCast E p).1 hab) a.2 b.2)
  rwa [Fintype.card_fin] at h

/-- No bound at least 1: the count's bound is below the number of values of the challenge. -/
theorem err_lt_card (p : ℕ) [CharP E p] {m : ℕ} {v : ℕ → ℕ} {T w W : ℕ} (hA : Adm p m v T w W) :
    allKeys m v - 1 < Fintype.card E :=
  lt_of_le_of_lt (Nat.sub_le _ _)
    (lt_of_le_of_lt
      ((Nat.le_sub_one_of_lt hA.fits).trans (Nat.le_mul_of_pos_left _ (by positivity)))
      (lt_of_lt_of_le hA.char (char_le_card p)))

end

/-! ## The factor as a polynomial -/

section
variable {E : Type} [Field E]
open Polynomial

/-- The public factor as a polynomial in the challenge. -/
noncomputable def padPoly (t : ℕ → E) (pads : List (ℕ × ℕ)) : E[X] :=
  (pads.map fun e => (X - C (t e.1)) ^ e.2).prod

theorem padPoly_cons (t : ℕ → E) (e : ℕ × ℕ) (pads : List (ℕ × ℕ)) :
    padPoly t (e :: pads) = (X - C (t e.1)) ^ e.2 * padPoly t pads := by
  simp [padPoly]

theorem padFac_cons (t : ℕ → E) (e : ℕ × ℕ) (pads : List (ℕ × ℕ)) (al : E) :
    padFac t (e :: pads) al = (al - t e.1) ^ e.2 * padFac t pads al := by
  simp [padFac]

theorem padPoly_eval (t : ℕ → E) (al : E) :
    ∀ pads : List (ℕ × ℕ), (padPoly t pads).eval al = padFac t pads al
  | [] => by simp [padPoly, padFac]
  | e :: pads => by
    rw [padPoly_cons, padFac_cons, eval_mul, padPoly_eval t al pads]
    simp

theorem padPoly_monic (t : ℕ → E) : ∀ pads : List (ℕ × ℕ), (padPoly t pads).Monic
  | [] => by simp [padPoly]
  | e :: pads => by
    rw [padPoly_cons]
    exact ((monic_X_sub_C _).pow _).mul (padPoly_monic t pads)

theorem padPoly_natDegree (t : ℕ → E) :
    ∀ pads : List (ℕ × ℕ), (padPoly t pads).natDegree = padNum pads
  | [] => by simp [padPoly, padNum]
  | e :: pads => by
    rw [padPoly_cons, ((monic_X_sub_C (t e.1)).pow e.2).natDegree_mul (padPoly_monic t pads),
      (monic_X_sub_C (t e.1)).natDegree_pow, natDegree_X_sub_C, padPoly_natDegree t pads]
    simp [padNum]

/-- At a padding row that is held at least once the public factor is 0. -/
theorem padFac_eq_zero (t : ℕ → E) : ∀ (pads : List (ℕ × ℕ)) (e : ℕ × ℕ), e ∈ pads → 0 < e.2 →
    padFac t pads (t e.1) = 0
  | [], _, he, _ => by cases he
  | q :: pads, e, he, h => by
    rw [padFac_cons]
    rcases List.mem_cons.1 he with rfl | h'
    · rw [sub_self, zero_pow (by omega), zero_mul]
    · rw [padFac_eq_zero t pads e h' h, mul_zero]

theorem padFac_ne_one_at (t : ℕ → E) (pads : List (ℕ × ℕ)) (e : ℕ × ℕ) (he : e ∈ pads)
    (h : 0 < e.2) : padFac t pads (t e.1) ≠ 1 := by
  rw [padFac_eq_zero t pads e he h]
  exact zero_ne_one

/-- With padding the public factor is not 1 as a polynomial in the challenge. -/
theorem padPoly_ne_one (t : ℕ → E) (pads : List (ℕ × ℕ)) (h : 0 < padNum pads) :
    padPoly t pads ≠ 1 := by
  intro he
  have h1 := padPoly_natDegree t pads
  rw [he, natDegree_one] at h1
  omega

end

end Lk6

#print axioms Lk6.cnt_ident_le
#print axioms Lk6.cnt_mid_le
#print axioms Lk6.cnt_badAl_le
#print axioms Lk6.err_lt_card
#print axioms Lk6.inParts_of_mid
#print axioms Lk6.midQ_one
#print axioms Lk6.midQ_one_nil
#print axioms Lk6.inParts_one
#print axioms Lk6.padPoly_eval
#print axioms Lk6.padPoly_ne_one
#print axioms Lk6.padFac_ne_one_at
#print axioms Lk6.restProd_zero
#print axioms Lk6.restProd_step
#print axioms Lk6.restProd_last
