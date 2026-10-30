-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.PayPub
import OnBytes.Slice.ManyErr
import OnBytes.Slice.Rates
/-
Johnson/Desc/K12/Law/BatPriceLaw.lean: WHAT A YES OF batPriceOk (H2K/BatPriceOk.lean) GIVES: THE LIBRARY's OWN COMPARISON ON A ROUND's COUNT. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  chalsB_eq       the native number of a written round's verifier messages IS Fintype.card (wRound w.rd).Chal (over the library's card_wRound)
  wOf_eq · roundBelow_like   wOf d, (bsRound .two d.entry d.kind).w and (bsOf .two (dsOf …)).w are one number (by definition) · RoundBelow reads of a round its entry and its kind alone: so it passes from the plan's written round w0.rd to any round with w0's entry and kind
  batBelow_of_ok  the plan's first stage and first written round w0 stand · batPriceOk p r k = true ⇒ RoundBelow (batV0 p r) w0.rd (2⁻¹ ^ k) (OnBytes/Slice/ManyErr.lean: n * w ≤ εs * the number of the round's challenge values)
  batPay_gives    … · the radius letter is r · batPayOk p r k = true ⇒ PayPub p rad w0.entry.rows (batV0 p r) ∧ RoundBelow (batV0 p r) w0.rd (2⁻¹ ^ k): ONE TEST WITH CODE, WHICH CAN FAIL EVERYWHERE, GIVES BOTH; of johOk it asks the FIRST stage's clauses alone
WHAT IT DOES NOT SAY: that batV0 bounds anything: that is the payer's (H2K/TupleVals.lean, under its premises) · at or beyond the Johnson radius batV0 is 0 and the statement is idle: to be read beside johOk at the same radius · batPriceOk's yes is a run's word · one round of one block: no level of security.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Fmt.M1 (Stage)
open scoped ENNReal

theorem chalsB_eq (w : WR) : chalsB w = Fintype.card (wRound w.rd).Chal := by
  rw [card_wRound, Fintype.card_fun, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool]
  rfl

/-- The three names of the sampler's number are one number. -/
theorem wOf_eq (d : PQ.RD) : wOf d = (bsOf .two (Fmt.dsOf d.entry d.kind)).w := rfl

/-- The comparison reads of a round its entry and its kind alone. -/
theorem roundBelow_like (n : ℕ) (d d' : PQ.RD) (εs : ℝ≥0∞) (he : d.entry = d'.entry)
    (hk : d.kind = d'.kind) (h : RoundBelow n d' εs) : RoundBelow n d εs := by
  unfold RoundBelow at h ⊢
  rw [card_wRound] at h ⊢
  have hw : wOf d = wOf d' := by
    show (bsRound .two d.entry d.kind).w = (bsRound .two d'.entry d'.kind).w
    rw [he, hk]
  rw [he, hk, hw]
  exact h


theorem batBelow_of_ok (p : P12) (r : Stage → ℕ) (k : ℕ) (a : Stage) (rest : List Stage)
    (hs : p.nums.stages = a :: rest) (w0 : WR) (l : List WR)
    (hw : writtenOf p.nums = some (w0 :: l)) (h : batPriceOk p r k = true) :
    RoundBelow (batV0 p r) w0.rd ((2 : ℝ≥0∞)⁻¹ ^ k) := by
  have hat : batAtB p = some (stN a, w0) := by
    unfold batAtB
    rw [hs, hw]
    rfl
  have hv : batV0 p r = v0On (stN a) (r (stN a)) w0.entry.rows := by
    unfold batV0
    rw [hat]
    rfl
  unfold batPriceOk at h
  rw [hat, Option.any_some] at h
  have h1 : v0On (stN a) (r (stN a)) w0.entry.rows * wOfB (Fmt.dsOf w0.entry w0.kind) * 2 ^ k ≤
      chalsB w0 := of_decide_eq_true h
  rw [← hv, wOfB_eq, chalsB_eq] at h1
  have h2 := share_le (batV0 p r * (bsOf .two (Fmt.dsOf w0.entry w0.kind)).w) 1 (2 ^ k)
    (Fintype.card (wRound w0.rd).Chal) (Nat.pos_of_ne_zero (pow_ne_zero _ two_ne_zero))
    (by rw [Nat.one_mul]; exact h1)
  show ((batV0 p r * wOf w0.rd : ℕ) : ℝ≥0∞) ≤ _
  refine le_trans h2 (le_of_eq ?_)
  rw [Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat, one_div, ENNReal.inv_pow]

/-- ONE TEST WITH CODE GIVES BOTH: the public half of what the payer asks, at v₀ := batV0, and
the library's comparison on that count. -/
theorem batPay_gives (p : P12) (r : Stage → ℕ) (rad : Sg → ℕ) (hr : ∀ s, rad s = r s.st) (k : ℕ)
    (a : Stage) (rest : List Stage) (hs : p.nums.stages = a :: rest) (w0 : WR) (l : List WR)
    (hw : writtenOf p.nums = some (w0 :: l)) (h : batPayOk p r k = true) :
    PayPub p rad w0.entry.rows (batV0 p r) ∧
      RoundBelow (batV0 p r) w0.rd ((2 : ℝ≥0∞)⁻¹ ^ k) := by
  have hat : batAtB p = some (stN a, w0) := by
    unfold batAtB
    rw [hs, hw]
    rfl
  unfold batPayOk at h
  rw [hat, Option.any_some] at h
  have h' : (ok (stageJL (stN a) (r (stN a))) &&
      priceOn (stN a) w0 (r (stN a)) w0.entry.rows k) = true := h
  rw [Bool.and_eq_true] at h'
  refine ⟨?_, batBelow_of_ok p r k a rest hs w0 l hw ?_⟩
  · intro a' rest' hs'
    obtain ⟨rfl, _⟩ := List.cons.inj (hs'.symm.trans hs)
    have hJ : ok (stageJL a' (r (stN a'))) = true := h'.1
    refine ⟨by rw [hr]; exact stageJ_of_L hJ, ?_⟩
    have hv : batV0 p r = lstJB (stN a') (r (stN a')) * (w0.entry.rows - 1) := by
      unfold batV0
      rw [hat]
      rfl
    rw [hv, hr, lstJB_eq]
    exact le_refl _
  · unfold batPriceOk
    rw [hat, Option.any_some]
    exact h'.2

end H2K.Pub

#print axioms H2K.Pub.chalsB_eq
#print axioms H2K.Pub.roundBelow_like
#print axioms H2K.Pub.batBelow_of_ok
#print axioms H2K.Pub.batPay_gives
