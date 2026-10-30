-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/AtCap.lean
(kind K9's soundness lemma): THEOREMS: K9's OWN COUNT IS BELOW THE
CAP. Every piece of a description carries as its errors the cap: at each round (the number of the
round's written challenges) / 2^128 (Iop/ErrCap.lean: Err.cap 128). K9's rows are proved at K9's own
count: allErr (fun _ _ => d) 0 ds: at most d field elements are bad (d: the bound on the exponents
of chi), counted in written challenges (Johnson/Flat/ReadingCountAll.lean). Here: that count is at
most the cap, so the hypothesis "herr" of k9_row, k9_row_at, k9_row_moves is paid at the cap.
  num_k9      THE ONE INEQUALITY IN NUMBERS: for d ≤ 2^60 and any bits of work w:
              (1 + 2^-128)^3 * (d / (|E| - 1) / 2^w) ≤ 2^-128. (|E| = p^3, p = 2^64 - 2^32 + 1; the
              factor is the sampler's bias for the one element drawn, in the finer form "Ex": three
              factors an element, none for anything else.) NO WORK IS NEEDED.
  herr_cap    at any rounds: the condition AllHeldEx at 2^-128 gives "K9's count ≤ the cap".
  herr_cap_one   at one round that draws one element (and t matrix entries): from d ≤ 2^60 alone.
  k9Round, dsOf_k9Round   K9's own round, by K9's entry (Batch/Kind.lean): it draws one element.
              (Its kind ".elems" is written here by hand: that the piece which a description makes
              of K9's draw has just this record is asked where it is spent: hds, Law/RowAtS.lean.)
  herr_cap_k9 **at K9's own round: K9's count is at most the cap, for d ≤ 2^60.**
WHAT d IS: the hypothesis hok of the rows asks that the exponents differ and are at most d. At the
plan's numbers the exponents are below the entry's "rows" (the segment's claims and the smallness
test's equations): 32,005,923 at the largest segment of the full size, by hand: below 2^25. THAT THE
EXPONENTS ARE BELOW THE ENTRY's rows IS NO THEOREM YET.

-/
import Iop.ErrCap
import Johnson.Flat.ReadingCountAll
import Johnson.Desc.First.Batch.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Flat OnBytes.Maker
open _root_.Run (ckP EV NZ)
open _root_.Iop (Err kapSl)

theorem card_nz_ge : 2 ^ 191 ≤ Fintype.card (NZ .two) := by
  rw [← Nat.card_eq_fintype_card, OnBytes.Slice.card_NZ]
  have e : Fmt.Fld.two.p = 2 ^ 64 - 2 ^ 32 + 1 := rfl
  rw [e]
  norm_num

theorem kapSl_le_two : kapSl 128 ≤ 2 := by
  unfold kapSl
  have h : ((2 : ℝ≥0∞) ^ 128)⁻¹ ≤ 1 := by
    rw [ENNReal.inv_le_one]
    exact one_le_pow₀ (by norm_num)
  calc (1 : ℝ≥0∞) + ((2 : ℝ≥0∞) ^ 128)⁻¹ ≤ 1 + 1 := by gcongr
    _ = 2 := by norm_num

/-- **The one inequality in numbers.** -/
theorem num_k9 (d w : ℕ) (hd : d ≤ 2 ^ 60) :
    kapSl 128 ^ 3 * (((d : ℕ) : ℝ≥0∞) / ((Fintype.card (NZ .two) : ℕ) : ℝ≥0∞) / 2 ^ w) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 128 := by
  have h1 : kapSl 128 ^ 3 ≤ (2 : ℝ≥0∞) ^ 3 := pow_le_pow_left₀ (zero_le _) kapSl_le_two 3
  have h2 : ((d : ℕ) : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ 60 := by exact_mod_cast hd
  have h3 : (2 : ℝ≥0∞) ^ 191 ≤ ((Fintype.card (NZ .two) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast card_nz_ge
  have h4 : ((d : ℕ) : ℝ≥0∞) / ((Fintype.card (NZ .two) : ℕ) : ℝ≥0∞) ≤
      (2 : ℝ≥0∞) ^ 60 / (2 : ℝ≥0∞) ^ 191 := ENNReal.div_le_div h2 h3
  have h5 : ((d : ℕ) : ℝ≥0∞) / ((Fintype.card (NZ .two) : ℕ) : ℝ≥0∞) / 2 ^ w ≤
      ((d : ℕ) : ℝ≥0∞) / ((Fintype.card (NZ .two) : ℕ) : ℝ≥0∞) :=
    ENNReal.div_le_of_le_mul (le_mul_of_one_le_right (zero_le _) (one_le_pow₀ (by norm_num)))
  have c0 : ((2 : ℝ≥0∞) ^ 63) ≠ 0 := pow_ne_zero _ (by norm_num)
  have ct : ((2 : ℝ≥0∞) ^ 63) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  calc kapSl 128 ^ 3 * (((d : ℕ) : ℝ≥0∞) / ((Fintype.card (NZ .two) : ℕ) : ℝ≥0∞) / 2 ^ w)
      ≤ (2 : ℝ≥0∞) ^ 3 * ((2 : ℝ≥0∞) ^ 60 / (2 : ℝ≥0∞) ^ 191) :=
        mul_le_mul' h1 (h5.trans h4)
    _ = (2 : ℝ≥0∞) ^ 63 * 1 / ((2 : ℝ≥0∞) ^ 63 * (2 : ℝ≥0∞) ^ 128) := by
        rw [← mul_div_assoc, ← pow_add, ← pow_add, mul_one]
    _ = 1 / (2 : ℝ≥0∞) ^ 128 := ENNReal.mul_div_mul_left _ _ c0 ct
    _ = (2 : ℝ≥0∞)⁻¹ ^ 128 := by rw [one_div, ENNReal.inv_pow]

/-- At any rounds: the condition at 2^-128 gives "K9's count is at most the cap". -/
theorem herr_cap (d : ℕ) (ds : List RDT) (hlog : ∀ r ∈ ds, r.entry.logN ≤ 64)
    (hh : AllHeldEx (fun _ _ => d) ((2 : ℝ≥0∞)⁻¹ ^ 128) 0 ds) :
    Err.le (allErr (fun _ _ => d) 0 ds) (Err.cap 128 (uLT (ckP .two) ds)) :=
  Err.le_cap_of_below_inv 128 _ (allErr_below_ex _ 0 ds hlog hh)

/-- At one round that draws one element. -/
theorem herr_cap_one (d : ℕ) (hd : d ≤ 2 ^ 60) (r : RDT) (t : ℕ)
    (hds : Fmt.dsOf r.entry r.kind = [.elem, .trits t]) (hlog : r.entry.logN ≤ 64) :
    Err.le (allErr (fun _ _ => d) 0 [r]) (Err.cap 128 (uLT (ckP .two) [r])) :=
  herr_cap d [r]
    (fun q hq => by
      rw [List.mem_singleton.1 hq]
      exact hlog)
    ((allHeldEx_one (fun _ _ => d) _ 0 r t hds).2 (num_k9 d r.entry.work hd))

/-- K9's own round, as the file format has a round's data: K9's entry; elements are drawn; nothing
is sent, no tree is opened. -/
def k9Round (p : K9.Where) : RDT := ⟨⟨K9.entry p, .elems, [], [], []⟩, []⟩

theorem dsOf_k9Round (p : K9.Where) :
    Fmt.dsOf (k9Round p).entry (k9Round p).kind = [.elem, .trits 0] := rfl

/-- **At K9's own round K9's count is at most the cap.** -/
theorem herr_cap_k9 (p : K9.Where) (d : ℕ) (hd : d ≤ 2 ^ 60) :
    Err.le (allErr (fun _ _ => d) 0 [k9Round p]) (Err.cap 128 (uLT (ckP .two) [k9Round p])) :=
  herr_cap_one d hd (k9Round p) 0 (dsOf_k9Round p) (Nat.zero_le 64)

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.num_k9
#print axioms VerifiableInference.Desc.K9L.herr_cap
#print axioms VerifiableInference.Desc.K9L.herr_cap_one
#print axioms VerifiableInference.Desc.K9L.herr_cap_k9
