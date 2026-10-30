-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/MarkRoundsK.lean: A MARK THAT SPEAKS ONLY WHERE, AT ONE OF A LIST OF A MEMBER's
ROUNDS, THE ONE ELEMENT DRAWN IS ONE OF AT MOST k FORBIDDEN VALUES: ITS SENTENCE `MarkDebt`
(Johnson/Desc/ProofFile/Honest/Law/CoverJoin.lean) AT STRINGS OF HASH BLOCKS, AT THE WRITTEN PAIR
WITH THE FACTOR k. THE GENERAL FORM OF `markDebt_of_list_blocks` (Johnson/P1K8R/MarkRounds.lean),
WHICH IS ITS CASE k = 2. Lemmas; NONE OF THE LIBRARY's GOALS. Nothing on completeness, soundness or
hiding.

B: the forbidden values, as a sentence on a field element. k: at most so many elements meet it.
  `bad_gate_blocks_k`   one listed round
  `held_of_rounds_blocks_k`, `markDebt_of_rounds_blocks_k`   the mark's stated share is held; the
      mark's sentence
  `rounds_share_k`, `rounds_ok_k`   the value of the written pair ⟨k * n * (2 ^ 128 + 1) ^ 3, pGold
      ^ 3 * (2 ^ 128) ^ 3⟩; its denominator is not 0
  **`markDebt_of_list_blocks_k`**   the sentence of a mark with a list of rounds and that pair as
      its share
  `cnt_zero`, **`markDebt_of_list_blocks_one`**   the case of the one forbidden value 0
  `markDebt_of_list_blocks_two`   the case of 0 and 1: `markDebt_of_list_blocks`' own statement, as
      one call
By: `gate_of_count_blocks` (Johnson/P1K8R/GateOfCount.lean) · `rounds_le`, `oneBad_some`,
`listedN_le`, `cnt_zero_one` (MarkRounds.lean) · `share_val_gen` (Johnson/P1K8R/DeadMark.lean) ·
markDebt_of_held.
Limits. As in MarkRounds.lean: (hsp) and (hbad) are premises on a mark's text; (h1) on the data; a
round that draws several elements is not covered; the uniform law on the rounds' messages is named,
not derived. No number is evaluated.

-/
import Johnson.P1K8R.MarkRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Slice
open OnBytes.Maker (RDT uLT drawnT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open ProofFile.Honest (Odds Mark Held MarkDebt markDebt_of_held)
open Iop
open scoped ENNReal

/-- **One listed round: at strings of hash blocks.** -/
theorem bad_gate_blocks_k (bad : Fmt.Drawn → Bool) (B : Cb.Gl.E → Prop) (k : ℕ)
    (hbad : ∀ dr x, bad dr = true → dr.elems = [Slice.ofE x] → B x) (hB : Prob.cnt B ≤ k)
    (d : RDT) (h1 : OneElem d.entry d.kind) (hlog : d.entry.logN ≤ 64) :
    Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ckP .two) [d]) |
      oneBad bad (drawnT (_root_.Run.ckP .two) [d] ρ) = true} ≤
      kapSl 128 ^ 3 * ((k : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) :=
  le_trans (Prob.pr_mono _ fun _ hρ => oneBad_some bad _ hρ)
    (gate_of_count_blocks d h1 hlog (fun dr => bad dr = true) B hbad k hB)

/-- **The mark's stated share is held.** -/
theorem held_of_rounds_blocks_k (mkR : Mark) (bad : Fmt.Drawn → Bool) (B : Cb.Gl.E → Prop)
    (k : ℕ) (mk : ℕ → Bool) (ds : List RDT)
    (hsp : ∀ fr own, (mkR.test fr own).isSome = true → anyBad bad mk 0 own = true)
    (hbad : ∀ dr x, bad dr = true → dr.elems = [Slice.ofE x] → B x) (hB : Prob.cnt B ≤ k)
    (h1 : ∀ i d, ds[i]? = some d → mk i = true → OneElem d.entry d.kind ∧ d.entry.logN ≤ 64)
    (hok : mkR.share.ok = true)
    (hval : (listedN mk 0 ds.length : ℝ≥0∞) *
      (kapSl 128 ^ 3 * ((k : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)) ≤ mkR.share.val)
    (fr : List Fmt.Drawn) :
    Held (_root_.Run.ckP .two) ds (fun own => (mkR.test fr own).isSome) mkR.share :=
  ⟨hok, le_trans (le_trans (Prob.pr_mono _ fun _ hρ => hsp fr _ hρ)
    (rounds_le _ bad mk _ ds fun i d hi hm =>
      bad_gate_blocks_k bad B k hbad hB d (h1 i d hi hm).1 (h1 i d hi hm).2)) hval⟩

/-- **The mark's sentence.** -/
theorem markDebt_of_rounds_blocks_k (mkR : Mark) (bad : Fmt.Drawn → Bool) (B : Cb.Gl.E → Prop)
    (k : ℕ) (mk : ℕ → Bool) (ds : List RDT)
    (hsp : ∀ fr own, (mkR.test fr own).isSome = true → anyBad bad mk 0 own = true)
    (hbad : ∀ dr x, bad dr = true → dr.elems = [Slice.ofE x] → B x) (hB : Prob.cnt B ≤ k)
    (h1 : ∀ i d, ds[i]? = some d → mk i = true → OneElem d.entry d.kind ∧ d.entry.logN ≤ 64)
    (hok : mkR.share.ok = true)
    (hval : (listedN mk 0 ds.length : ℝ≥0∞) *
      (kapSl 128 ^ 3 * ((k : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)) ≤ mkR.share.val)
    (Q : List Fmt.Drawn → Prop) : MarkDebt (_root_.Run.ckP .two) mkR ds Q mkR.share.val :=
  markDebt_of_held _ _ _ Q fun fr _ =>
    held_of_rounds_blocks_k mkR bad B k mk ds hsp hbad hB h1 hok hval fr

/-- The written pair's value. -/
theorem rounds_share_k (k n : ℕ) :
    (⟨k * n * (2 ^ 128 + 1) ^ 3, Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩ : Odds).val =
      (n : ℝ≥0∞) * (kapSl 128 ^ 3 * ((k : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)) := by
  rw [share_val_gen (k * n) (Code.pGold ^ 3) 128, Slice.two_p]
  simp only [div_eq_mul_inv]
  push_cast
  ring

/-- The written pair's denominator is not 0. -/
theorem rounds_ok_k (a : ℕ) : (⟨a, Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩ : Odds).ok = true := by
  have hp : Code.pGold ^ 3 ≠ 0 := by
    rw [← OnBytes.Slice.two_p]
    decide
  show ((Code.pGold ^ 3 * (2 ^ 128) ^ 3 : ℕ) != 0) = true
  simp only [bne_iff_ne, ne_eq, Nat.mul_eq_zero, not_or]
  exact ⟨hp, by positivity⟩

/-- **The sentence of a mark with a list of rounds and the written pair as its share.** -/
theorem markDebt_of_list_blocks_k (mkR : Mark) (bad : Fmt.Drawn → Bool) (B : Cb.Gl.E → Prop)
    (k : ℕ) (L : List ℕ) (ds : List RDT)
    (hsp : ∀ fr own, (mkR.test fr own).isSome = true →
      anyBad bad (fun i => decide (i ∈ L)) 0 own = true)
    (hbad : ∀ dr x, bad dr = true → dr.elems = [Slice.ofE x] → B x) (hB : Prob.cnt B ≤ k)
    (h1 : ∀ i d, ds[i]? = some d → i ∈ L → OneElem d.entry d.kind ∧ d.entry.logN ≤ 64)
    (hshare : mkR.share = ⟨k * L.length * (2 ^ 128 + 1) ^ 3, Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩)
    (Q : List Fmt.Drawn → Prop) : MarkDebt (_root_.Run.ckP .two) mkR ds Q mkR.share.val :=
  markDebt_of_rounds_blocks_k mkR bad B k _ ds hsp hbad hB
    (fun i d hi hm => h1 i d hi (of_decide_eq_true hm))
    (by rw [hshare]; exact rounds_ok_k _)
    (by
      rw [hshare, rounds_share_k]
      exact mul_le_mul' (by exact_mod_cast listedN_le L 0 ds.length) le_rfl) Q

theorem cnt_zero : Prob.cnt (fun x : Cb.Gl.E => x = 0) ≤ 1 :=
  Prob.cnt_le_one fun _ _ ha hb => ha.trans hb.symm

/-- **The one forbidden value 0.** -/
theorem markDebt_of_list_blocks_one (mkR : Mark) (bad : Fmt.Drawn → Bool) (L : List ℕ)
    (ds : List RDT)
    (hsp : ∀ fr own, (mkR.test fr own).isSome = true →
      anyBad bad (fun i => decide (i ∈ L)) 0 own = true)
    (hbad : ∀ dr x, bad dr = true → dr.elems = [Slice.ofE x] → x = 0)
    (h1 : ∀ i d, ds[i]? = some d → i ∈ L → OneElem d.entry d.kind ∧ d.entry.logN ≤ 64)
    (hshare : mkR.share = ⟨1 * L.length * (2 ^ 128 + 1) ^ 3, Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩)
    (Q : List Fmt.Drawn → Prop) : MarkDebt (_root_.Run.ckP .two) mkR ds Q mkR.share.val :=
  markDebt_of_list_blocks_k mkR bad (fun x => x = 0) 1 L ds hsp hbad cnt_zero h1 hshare Q

/-- The two forbidden values 0 and 1: as one call. -/
theorem markDebt_of_list_blocks_two (mkR : Mark) (bad : Fmt.Drawn → Bool) (L : List ℕ)
    (ds : List RDT)
    (hsp : ∀ fr own, (mkR.test fr own).isSome = true →
      anyBad bad (fun i => decide (i ∈ L)) 0 own = true)
    (hbad : ∀ dr x, bad dr = true → dr.elems = [Slice.ofE x] → x = 0 ∨ x = 1)
    (h1 : ∀ i d, ds[i]? = some d → i ∈ L → OneElem d.entry d.kind ∧ d.entry.logN ≤ 64)
    (hshare : mkR.share = ⟨2 * L.length * (2 ^ 128 + 1) ^ 3, Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩)
    (Q : List Fmt.Drawn → Prop) : MarkDebt (_root_.Run.ckP .two) mkR ds Q mkR.share.val :=
  markDebt_of_list_blocks_k mkR bad (fun x => x = 0 ∨ x = 1) 2 L ds hsp hbad cnt_zero_one h1
    hshare Q

end P1K8

#print axioms P1K8.bad_gate_blocks_k
#print axioms P1K8.rounds_share_k
#print axioms P1K8.rounds_ok_k
#print axioms P1K8.markDebt_of_list_blocks_k
#print axioms P1K8.markDebt_of_list_blocks_one
#print axioms P1K8.markDebt_of_list_blocks_two
