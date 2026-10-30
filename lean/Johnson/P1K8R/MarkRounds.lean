-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/MarkRounds.lean: A MARK THAT SPEAKS ONLY WHERE, AT ONE OF THE LISTED ROUNDS OF A
MEMBER, THE ONE DRAWN FIELD ELEMENT IS 0 OR 1, OR NO FIELD ELEMENT IS THERE: ITS MEASURE OVER ALL
THE MEMBER's ROUNDS, AND ITS SENTENCE `MarkDebt` (Johnson/Desc/ProofFile/Honest/Law/CoverJoin.lean).
Definitions and lemmas; NONE OF THE LIBRARY's GOALS. Nothing on completeness, soundness or hiding.
General in the member, the list and the test at a round.

ds: the data of a member's rounds. mk j: round number j is listed. bad: a test on one round's drawn
value.
  `oneBad`, `roundGates`, `anyBad`, `listedN`   one gate a round (`Gate`,
      Johnson/Desc/ProofFile/Honest/Law/SharesHeld.lean); "some listed round's drawn value is bad";
      the number of listed rounds
  `gates_ds`, `spoken_rounds`, `gatesHeld_rounds`, `gates_sum`   what these gates are
  **`rounds_le`**   the kit a letter: IF at each listed round, over that round's own messages, bad
      speaks with measure at most q: THEN over all the rounds' messages "some listed round's drawn
      value is bad" has measure at most listedN * q
  **`bad_gate`**, **`bad_gate_blocks`**   a round that draws one field element and nothing else;
      (hbad) wherever bad speaks at a drawn value whose elements are [x], x is 0 or 1: the measure
      is at most 2 / p ^ 3 at Run.ck .two, and kapSl 128 ^ 3 times that at Run.ckP .two
  **`held_of_rounds`**, **`held_of_rounds_blocks`**   mkR a mark; (hsp) its test speaks only where
      `anyBad bad mk 0` does; (hbad); every listed round draws one element; the stated share's
      denominator is not 0 and its value is at least listedN times the one round's bound: `Held` of
      its test and its share, at every front
  **`markDebt_of_rounds`**, **`markDebt_of_rounds_blocks`**   so `MarkDebt` at the share's value, at
      whatever P
  `listedN_le`, `rounds_ok`, **`markDebt_of_list_blocks`**   the listed rounds given as a list L of
      numbers: they are no more than L is long, whatever L; with the written pair at n := L.length
      as the mark's share: `MarkDebt` at Run.ckP .two in one call
  `rounds_share`   the value of the written pair ⟨2 * n * (2 ^ 128 + 1) ^ 3, pGold ^ 3 * (2 ^ 128) ^
      3⟩ is n times the bound at strings of hash blocks
By: gates_le (SharesHeld.lean) · prRho_ds (SharesChain.lean) · markDebt_of_held (CoverSeat.lean) ·
`gate_of_count`, `gate_of_count_blocks` (Johnson/P1K8R/GateOfCount.lean) · `share_val_gen`
(Johnson/P1K8R/DeadMark.lean).
Kin. Johnson/Desc/ProofFile/Honest/Small/MarkRounds.lean, of other authors: its `roundGates` and
`markDebt_of_rounds` are namesakes in another namespace, and this file's first half goes the same
road: one gate for each listed round, then the sum over the rounds. There the kit is a letter, test
and number may differ from round to round, each round's bound is a premise, and the end is the sum
over the list. Here one test `bad` serves all listed rounds; under (hbad) one round's bound is
counted, not asked (`bad_gate`, `bad_gate_blocks`), and the end is the mark's own stated share.
Neither file imports the other.
Limits. (hsp) and (hbad) are premises on a mark's text. A round that draws several elements is not
covered. The uniform law on the rounds' messages is named, not derived. No number is evaluated.
-/
import Johnson.P1K8R.GateOfCount
import Johnson.P1K8R.DeadMark
import Johnson.Desc.ProofFile.Honest.Law.SharesChain
import Johnson.Desc.ProofFile.Honest.Law.CoverSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Slice
open OnBytes.Maker (RDT uLT drawnT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open ProofFile.Honest (Odds Mark Held Gate spoken GatesHeld gates_le prRho_ds MarkDebt markDebt_of_held)
open _root_.Run.PQ (CK)
open Iop
open scoped ENNReal

/-- The test at a list of just one drawn value. -/
def oneBad (bad : Fmt.Drawn → Bool) : List Fmt.Drawn → Bool
  | [dr] => bad dr
  | _ => false

/-- One gate a round. -/
def roundGates (bad : Fmt.Drawn → Bool) (mk : ℕ → Bool) (q : ℝ≥0∞) : ℕ → List RDT → List Gate
  | _, [] => []
  | j, d :: ds =>
    ⟨[d], fun _ own => mk j && oneBad bad own, if mk j = true then q else 0⟩ ::
      roundGates bad mk q (j + 1) ds

/-- Some listed round's drawn value is bad. -/
def anyBad (bad : Fmt.Drawn → Bool) (mk : ℕ → Bool) : ℕ → List Fmt.Drawn → Bool
  | _, [] => false
  | j, x :: l => (mk j && bad x) || anyBad bad mk (j + 1) l

/-- The number of listed rounds among n from number j on. -/
def listedN (mk : ℕ → Bool) (j n : ℕ) : ℕ := ((List.range' j n).filter mk).length

theorem listedN_succ (mk : ℕ → Bool) (j n : ℕ) :
    listedN mk j (n + 1) = (if mk j = true then 1 else 0) + listedN mk (j + 1) n := by
  unfold listedN
  rw [List.range'_succ, List.filter_cons]
  split
  · rw [List.length_cons]
    omega
  · omega

theorem gates_ds (bad : Fmt.Drawn → Bool) (mk : ℕ → Bool) (q : ℝ≥0∞) :
    ∀ (ds : List RDT) (j : ℕ), (roundGates bad mk q j ds).flatMap (·.ds) = ds
  | [], _ => rfl
  | d :: ds, j => by
    simp only [roundGates, List.flatMap_cons, List.singleton_append]
    rw [gates_ds bad mk q ds (j + 1)]

theorem spoken_rounds (bad : Fmt.Drawn → Bool) (mk : ℕ → Bool) (q : ℝ≥0∞) :
    ∀ (ds : List RDT) (j : ℕ) (fr dr : List Fmt.Drawn), dr.length = ds.length →
      spoken (roundGates bad mk q j ds) fr dr = anyBad bad mk j dr
  | [], _, _, dr, h => by
    obtain rfl := List.length_eq_zero_iff.1 h
    rfl
  | d :: ds, j, fr, dr, h => by
    cases dr with
    | nil => simp at h
    | cons x l =>
      have hl : l.length = ds.length := by simpa using h
      simp only [roundGates, spoken, anyBad, List.length_singleton, List.take_succ_cons,
        List.take_zero, List.drop_succ_cons, List.drop_zero, oneBad]
      rw [spoken_rounds bad mk q ds (j + 1) _ l hl]

theorem gates_sum (bad : Fmt.Drawn → Bool) (mk : ℕ → Bool) (q : ℝ≥0∞) :
    ∀ (ds : List RDT) (j : ℕ),
      ((roundGates bad mk q j ds).map (·.p)).sum = (listedN mk j ds.length : ℝ≥0∞) * q
  | [], j => by simp [roundGates, listedN]
  | d :: ds, j => by
    simp only [roundGates, List.map_cons, List.sum_cons, List.length_cons]
    rw [gates_sum bad mk q ds (j + 1), listedN_succ]
    split
    · push_cast
      ring
    · push_cast
      ring

theorem gatesHeld_rounds (C : CK) (bad : Fmt.Drawn → Bool) (mk : ℕ → Bool) (q : ℝ≥0∞) :
    ∀ (ds : List RDT) (j : ℕ) (fr : List Fmt.Drawn),
      (∀ i d, ds[i]? = some d → mk (j + i) = true →
        Iop.prRho {ρ : Iop.Rho (uLT C [d]) | oneBad bad (drawnT C [d] ρ) = true} ≤ q) →
      GatesHeld C (roundGates bad mk q j ds) fr
  | [], _, _, _ => trivial
  | d :: ds, j, fr, h => by
    refine ⟨?_, fun ρ _ => gatesHeld_rounds C bad mk q ds (j + 1) _ fun i d' hi hm =>
      h (i + 1) d' (by simpa using hi) (by rw [← Nat.add_assoc, Nat.add_right_comm]; exact hm)⟩
    show Iop.prRho {ρ : Iop.Rho (uLT C [d]) | (mk j && oneBad bad (drawnT C [d] ρ)) = true} ≤
      if mk j = true then q else 0
    cases hm : mk j with
    | true =>
      simp only [Bool.true_and, if_true]
      exact h 0 d rfl (by rw [Nat.add_zero]; exact hm)
    | false =>
      simp only [Bool.false_and, Bool.false_eq_true, if_false]
      exact Iop.prRho_empty _ fun ρ hρ => by cases hρ

/-- **From one round's measure to the measure over all the member's rounds.** -/
theorem rounds_le (C : CK) (bad : Fmt.Drawn → Bool) (mk : ℕ → Bool) (q : ℝ≥0∞) (ds : List RDT)
    (h : ∀ i d, ds[i]? = some d → mk i = true →
      Iop.prRho {ρ : Iop.Rho (uLT C [d]) | oneBad bad (drawnT C [d] ρ) = true} ≤ q) :
    Iop.prRho {ρ : Iop.Rho (uLT C ds) | anyBad bad mk 0 (drawnT C ds ρ) = true} ≤
      (listedN mk 0 ds.length : ℝ≥0∞) * q := by
  have k := gates_le C (roundGates bad mk q 0 ds) [] (gatesHeld_rounds C bad mk q ds 0 []
    fun i d hi hm => h i d hi (by rw [Nat.zero_add] at hm; exact hm))
  rw [gates_sum, prRho_ds C (gates_ds bad mk q ds 0)
    (fun dr => spoken (roundGates bad mk q 0 ds) [] dr = true)] at k
  refine le_trans (Prob.pr_mono _ fun ρ hρ => ?_) k
  show spoken (roundGates bad mk q 0 ds) [] (drawnT C ds ρ) = true
  rw [spoken_rounds bad mk q ds 0 [] _ (ProofFile.Honest.drawnT_len C ds ρ)]
  exact hρ

theorem cnt_zero_one : Prob.cnt (fun x : Cb.Gl.E => x = 0 ∨ x = 1) ≤ 2 :=
  (Prob.cnt_or_le _ _).trans (Nat.add_le_add
    (Prob.cnt_le_one fun _ _ ha hb => ha.trans hb.symm)
    (Prob.cnt_le_one fun _ _ ha hb => ha.trans hb.symm))

theorem oneBad_some (bad : Fmt.Drawn → Bool) (l : List Fmt.Drawn) (h : oneBad bad l = true) :
    ∃ dr, l = [dr] ∧ bad dr = true := by
  cases l with
  | nil => cases h
  | cons x t =>
    cases t with
    | nil => exact ⟨x, rfl, h⟩
    | cons _ _ => cases h

/-- **One listed round: at typed challenges.** -/
theorem bad_gate (bad : Fmt.Drawn → Bool)
    (hbad : ∀ dr x, bad dr = true → dr.elems = [Slice.ofE x] → x = 0 ∨ x = 1) (d : RDT)
    (h1 : OneElem d.entry d.kind) :
    Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ck .two) [d]) |
      oneBad bad (drawnT (_root_.Run.ck .two) [d] ρ) = true} ≤
      ((2 : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) :=
  le_trans (Prob.pr_mono _ fun _ hρ => oneBad_some bad _ hρ)
    (gate_of_count d h1 (fun dr => bad dr = true) _ hbad 2 cnt_zero_one)

/-- **One listed round: at strings of hash blocks.** -/
theorem bad_gate_blocks (bad : Fmt.Drawn → Bool)
    (hbad : ∀ dr x, bad dr = true → dr.elems = [Slice.ofE x] → x = 0 ∨ x = 1) (d : RDT)
    (h1 : OneElem d.entry d.kind) (hlog : d.entry.logN ≤ 64) :
    Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ckP .two) [d]) |
      oneBad bad (drawnT (_root_.Run.ckP .two) [d] ρ) = true} ≤
      kapSl 128 ^ 3 * ((2 : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) :=
  le_trans (Prob.pr_mono _ fun _ hρ => oneBad_some bad _ hρ)
    (gate_of_count_blocks d h1 hlog (fun dr => bad dr = true) _ hbad 2 cnt_zero_one)

/-- **The mark's stated share is held: at typed challenges.** -/
theorem held_of_rounds (mkR : Mark) (bad : Fmt.Drawn → Bool) (mk : ℕ → Bool) (ds : List RDT)
    (hsp : ∀ fr own, (mkR.test fr own).isSome = true → anyBad bad mk 0 own = true)
    (hbad : ∀ dr x, bad dr = true → dr.elems = [Slice.ofE x] → x = 0 ∨ x = 1)
    (h1 : ∀ i d, ds[i]? = some d → mk i = true → OneElem d.entry d.kind)
    (hok : mkR.share.ok = true)
    (hval : (listedN mk 0 ds.length : ℝ≥0∞) *
      (((2 : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)) ≤ mkR.share.val)
    (fr : List Fmt.Drawn) :
    Held (_root_.Run.ck .two) ds (fun own => (mkR.test fr own).isSome) mkR.share :=
  ⟨hok, le_trans (le_trans (Prob.pr_mono _ fun _ hρ => hsp fr _ hρ)
    (rounds_le _ bad mk _ ds fun i d hi hm => bad_gate bad hbad d (h1 i d hi hm))) hval⟩

/-- **The mark's stated share is held: at strings of hash blocks.** -/
theorem held_of_rounds_blocks (mkR : Mark) (bad : Fmt.Drawn → Bool) (mk : ℕ → Bool)
    (ds : List RDT)
    (hsp : ∀ fr own, (mkR.test fr own).isSome = true → anyBad bad mk 0 own = true)
    (hbad : ∀ dr x, bad dr = true → dr.elems = [Slice.ofE x] → x = 0 ∨ x = 1)
    (h1 : ∀ i d, ds[i]? = some d → mk i = true → OneElem d.entry d.kind ∧ d.entry.logN ≤ 64)
    (hok : mkR.share.ok = true)
    (hval : (listedN mk 0 ds.length : ℝ≥0∞) *
      (kapSl 128 ^ 3 * ((2 : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)) ≤ mkR.share.val)
    (fr : List Fmt.Drawn) :
    Held (_root_.Run.ckP .two) ds (fun own => (mkR.test fr own).isSome) mkR.share :=
  ⟨hok, le_trans (le_trans (Prob.pr_mono _ fun _ hρ => hsp fr _ hρ)
    (rounds_le _ bad mk _ ds fun i d hi hm =>
      bad_gate_blocks bad hbad d (h1 i d hi hm).1 (h1 i d hi hm).2)) hval⟩

/-- **The mark's sentence: at typed challenges.** -/
theorem markDebt_of_rounds (mkR : Mark) (bad : Fmt.Drawn → Bool) (mk : ℕ → Bool) (ds : List RDT)
    (hsp : ∀ fr own, (mkR.test fr own).isSome = true → anyBad bad mk 0 own = true)
    (hbad : ∀ dr x, bad dr = true → dr.elems = [Slice.ofE x] → x = 0 ∨ x = 1)
    (h1 : ∀ i d, ds[i]? = some d → mk i = true → OneElem d.entry d.kind)
    (hok : mkR.share.ok = true)
    (hval : (listedN mk 0 ds.length : ℝ≥0∞) *
      (((2 : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)) ≤ mkR.share.val)
    (Q : List Fmt.Drawn → Prop) : MarkDebt (_root_.Run.ck .two) mkR ds Q mkR.share.val :=
  markDebt_of_held _ _ _ Q fun fr _ => held_of_rounds mkR bad mk ds hsp hbad h1 hok hval fr

/-- **The mark's sentence: at strings of hash blocks.** -/
theorem markDebt_of_rounds_blocks (mkR : Mark) (bad : Fmt.Drawn → Bool) (mk : ℕ → Bool)
    (ds : List RDT)
    (hsp : ∀ fr own, (mkR.test fr own).isSome = true → anyBad bad mk 0 own = true)
    (hbad : ∀ dr x, bad dr = true → dr.elems = [Slice.ofE x] → x = 0 ∨ x = 1)
    (h1 : ∀ i d, ds[i]? = some d → mk i = true → OneElem d.entry d.kind ∧ d.entry.logN ≤ 64)
    (hok : mkR.share.ok = true)
    (hval : (listedN mk 0 ds.length : ℝ≥0∞) *
      (kapSl 128 ^ 3 * ((2 : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)) ≤ mkR.share.val)
    (Q : List Fmt.Drawn → Prop) : MarkDebt (_root_.Run.ckP .two) mkR ds Q mkR.share.val :=
  markDebt_of_held _ _ _ Q fun fr _ =>
    held_of_rounds_blocks mkR bad mk ds hsp hbad h1 hok hval fr

/-- The written pair's value. -/
theorem rounds_share (n : ℕ) :
    (⟨2 * n * (2 ^ 128 + 1) ^ 3, Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩ : Odds).val =
      (n : ℝ≥0∞) * (kapSl 128 ^ 3 * ((2 : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)) := by
  rw [share_val_gen (2 * n) (Code.pGold ^ 3) 128, Slice.two_p]
  simp only [div_eq_mul_inv]
  push_cast
  ring

/-- The listed rounds are no more than the list is long. -/
theorem listedN_le (L : List ℕ) (j n : ℕ) :
    listedN (fun i => decide (i ∈ L)) j n ≤ L.length := by
  unfold listedN
  have hnd : ((List.range' j n).filter fun i => decide (i ∈ L)).Nodup :=
    (List.nodup_range' 1 (by decide)).filter _
  exact (List.subperm_of_subset hnd fun x hx => by
    simpa using (List.mem_filter.1 hx).2).length_le

/-- The written pair's denominator is not 0. -/
theorem rounds_ok (n : ℕ) :
    (⟨2 * n * (2 ^ 128 + 1) ^ 3, Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩ : Odds).ok = true := by
  have hp : Code.pGold ^ 3 ≠ 0 := by
    rw [← OnBytes.Slice.two_p]
    decide
  show ((Code.pGold ^ 3 * (2 ^ 128) ^ 3 : ℕ) != 0) = true
  simp only [bne_iff_ne, ne_eq, Nat.mul_eq_zero, not_or]
  exact ⟨hp, by positivity⟩

/-- **The sentence of a mark with a list of rounds and the written pair as its share.** -/
theorem markDebt_of_list_blocks (mkR : Mark) (bad : Fmt.Drawn → Bool) (L : List ℕ)
    (ds : List RDT)
    (hsp : ∀ fr own, (mkR.test fr own).isSome = true →
      anyBad bad (fun i => decide (i ∈ L)) 0 own = true)
    (hbad : ∀ dr x, bad dr = true → dr.elems = [Slice.ofE x] → x = 0 ∨ x = 1)
    (h1 : ∀ i d, ds[i]? = some d → i ∈ L → OneElem d.entry d.kind ∧ d.entry.logN ≤ 64)
    (hshare : mkR.share = ⟨2 * L.length * (2 ^ 128 + 1) ^ 3, Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩)
    (Q : List Fmt.Drawn → Prop) : MarkDebt (_root_.Run.ckP .two) mkR ds Q mkR.share.val :=
  markDebt_of_rounds_blocks mkR bad _ ds hsp hbad
    (fun i d hi hm => h1 i d hi (of_decide_eq_true hm))
    (by rw [hshare]; exact rounds_ok _)
    (by
      rw [hshare, rounds_share]
      exact mul_le_mul' (by exact_mod_cast listedN_le L 0 ds.length) le_rfl) Q

end P1K8

#print axioms P1K8.oneBad
#print axioms P1K8.roundGates
#print axioms P1K8.anyBad
#print axioms P1K8.listedN
#print axioms P1K8.listedN_succ
#print axioms P1K8.gates_ds
#print axioms P1K8.spoken_rounds
#print axioms P1K8.gates_sum
#print axioms P1K8.gatesHeld_rounds
#print axioms P1K8.rounds_le
#print axioms P1K8.cnt_zero_one
#print axioms P1K8.oneBad_some
#print axioms P1K8.bad_gate
#print axioms P1K8.bad_gate_blocks
#print axioms P1K8.held_of_rounds
#print axioms P1K8.held_of_rounds_blocks
#print axioms P1K8.markDebt_of_rounds
#print axioms P1K8.markDebt_of_rounds_blocks
#print axioms P1K8.rounds_share
#print axioms P1K8.listedN_le
#print axioms P1K8.rounds_ok
#print axioms P1K8.markDebt_of_list_blocks
