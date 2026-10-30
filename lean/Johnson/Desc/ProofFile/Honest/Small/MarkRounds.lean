-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/MarkRounds.lean: WHAT IS OWED FOR A MARK (`MarkDebt`,
Honest/Law/CoverJoin.lean) THAT SPEAKS ONLY WHERE A TEST ON ONE ROUND's CHALLENGE IS TRUE AT ONE OF
A LIST OF ROUNDS: the sum, over that list, of a bound over THAT ONE ROUND's messages. CONDITIONAL.
One list of gates, and lemmas with their proofs. No kind of sub-protocol is named here. WHICH MARKS
ARE OF THIS MAKE: the test B is handed one round's challenge and no challenge in front: a mark whose
test weighs its own samples against challenges in front, or two rounds' samples against each other,
is not. None of the library's goals. Whose: part 4's.

  `roundGates`      one gate a round (`Gate`, Honest/Law/SharesHeld.lean); `roundGates_ds`,
                    `roundGates_spoken`, `roundGates_held`, `roundGates_sum_le`
  `markDebt_of_rounds`   **the debt**

What it is not. NO NUMBER IS EVALUATED: the kit C of verifier's messages, the rounds' data dsb and
the bounds z are letters. The bound over one round's messages (hz) is a premise: how a measure over
a kit's typed challenges comes from a count of what they show hangs on the kit. MET FOR NOTHING at z
:= 1. The uniform law on the messages: that the messages of any run have it is not said. A union
bound: it is no count of the set at which the mark speaks. Called: `pr_mono` (Prob), `prRho_empty`
(Iop/ViewKit.lean), `gatesHeld_all` (Honest/Law/SharesChain.lean), `spoken_le`
(Honest/Law/SharesFile.lean), `drawnT_len` (Honest/Law/Due.lean). Over files that have not yet
landed in the library: the last three and what they import.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Law.CoverJoin
import Johnson.Desc.ProofFile.Honest.Law.SharesFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open scoped ENNReal
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

/-- One gate a round: at round number i + j of a list it speaks where G is true of that number and B
is true, at that number, of the round's own challenge; its number is z (i + j) there, and 0 where G
is false. -/
def roundGates (G : Nat → Bool) (B : Nat → List Fmt.Drawn → Bool) (z : Nat → ℝ≥0∞) :
    Nat → List RDT → List Gate
  | _, [] => []
  | i, d :: ds =>
    ⟨[d], fun _ own => G i && B i own, if G i then z i else 0⟩ :: roundGates G B z (i + 1) ds

/-- The gates' rounds in a row are the list. -/
theorem roundGates_ds (G : Nat → Bool) (B : Nat → List Fmt.Drawn → Bool) (z : Nat → ℝ≥0∞) (i : Nat)
    (ds : List RDT) : (roundGates G B z i ds).flatMap (·.ds) = ds := by
  induction ds generalizing i with
  | nil => rfl
  | cons d ds ih =>
    show [d] ++ (roundGates G B z (i + 1) ds).flatMap (·.ds) = d :: ds
    rw [ih]
    rfl

private theorem drop_one_drop {α : Type} (l : List α) (j : Nat) :
    (l.drop 1).drop j = l.drop (j + 1) := by
  cases l <;> simp

/-- Some gate speaks just if, at a round of the list of whose number G is true, B is true of that
round's challenge alone. -/
theorem roundGates_spoken (G : Nat → Bool) (B : Nat → List Fmt.Drawn → Bool) (z : Nat → ℝ≥0∞)
    (i : Nat) (ds : List RDT) (fr dr : List Fmt.Drawn) :
    spoken (roundGates G B z i ds) fr dr = true ↔
      ∃ j, j < ds.length ∧ G (i + j) = true ∧ B (i + j) ((dr.drop j).take 1) = true := by
  induction ds generalizing i fr dr with
  | nil =>
    constructor
    · intro h
      cases h
    · rintro ⟨j, hj, _⟩
      cases hj
  | cons d ds ih =>
    show ((G i && B i (dr.take 1)) ||
      spoken (roundGates G B z (i + 1) ds) (fr ++ dr.take 1) (dr.drop 1)) = true ↔ _
    rw [Bool.or_eq_true, Bool.and_eq_true, ih]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨j, hj, h1, h2⟩)
      · exact ⟨0, Nat.succ_pos _, h1, h2⟩
      · refine ⟨j + 1, Nat.succ_lt_succ hj, ?_, ?_⟩
        · rw [show i + (j + 1) = i + 1 + j by omega]
          exact h1
        · rw [show i + (j + 1) = i + 1 + j by omega, ← drop_one_drop]
          exact h2
    · rintro ⟨j, hj, h1, h2⟩
      cases j with
      | zero => exact Or.inl ⟨h1, h2⟩
      | succ j =>
        refine Or.inr ⟨j, Nat.lt_of_succ_lt_succ hj, ?_, ?_⟩
        · rw [show i + 1 + j = i + (j + 1) by omega]
          exact h1
        · rw [show i + 1 + j = i + (j + 1) by omega, drop_one_drop]
          exact h2

/-- Of a list's numbers from i on: the one at i, once, and those from i + 1 on. -/
theorem roundSum_split (z : Nat → ℝ≥0∞) (i : Nat) : ∀ L : List Nat,
    (if i ∈ L then z i else 0) + ((L.filter fun r => decide (i + 1 ≤ r)).map z).sum ≤
      ((L.filter fun r => decide (i ≤ r)).map z).sum
  | [] => by simp
  | a :: L => by
    have ih := roundSum_split z i L
    have ih' : ((L.filter fun r => decide (i + 1 ≤ r)).map z).sum ≤
        ((L.filter fun r => decide (i ≤ r)).map z).sum := le_trans le_add_self ih
    rcases Nat.lt_trichotomy a i with h | h | h
    · have e1 : decide (i + 1 ≤ a) = false := decide_eq_false (by omega)
      have e2 : decide (i ≤ a) = false := decide_eq_false (by omega)
      have e3 : (i ∈ a :: L) ↔ i ∈ L := by
        rw [List.mem_cons]
        constructor
        · rintro (h' | h')
          · omega
          · exact h'
        · exact Or.inr
      rw [List.filter_cons_of_neg (by rw [e1]; exact Bool.false_ne_true),
        List.filter_cons_of_neg (by rw [e2]; exact Bool.false_ne_true), if_congr e3 rfl rfl]
      exact ih
    · subst h
      have e1 : decide (a + 1 ≤ a) = false := decide_eq_false (by omega)
      have e2 : decide (a ≤ a) = true := decide_eq_true (Nat.le_refl _)
      rw [List.filter_cons_of_neg (by rw [e1]; exact Bool.false_ne_true),
        List.filter_cons_of_pos (p := fun r => decide (a ≤ r)) e2, if_pos List.mem_cons_self,
        List.map_cons, List.sum_cons]
      exact add_le_add le_rfl ih'
    · have e1 : decide (i + 1 ≤ a) = true := decide_eq_true (by omega)
      have e2 : decide (i ≤ a) = true := decide_eq_true (by omega)
      have e3 : (i ∈ a :: L) ↔ i ∈ L := by
        rw [List.mem_cons]
        constructor
        · rintro (h' | h')
          · omega
          · exact h'
        · exact Or.inr
      rw [List.filter_cons_of_pos (p := fun r => decide (i + 1 ≤ r)) e1,
        List.filter_cons_of_pos (p := fun r => decide (i ≤ r)) e2, if_congr e3 rfl rfl,
        List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, add_left_comm]
      exact add_le_add le_rfl ih

/-- The gates' numbers from the round number i on. -/
theorem roundGates_sum_from (L : List Nat) (B : Nat → List Fmt.Drawn → Bool) (z : Nat → ℝ≥0∞) :
    ∀ (ds : List RDT) (i : Nat),
    ((roundGates (fun i => decide (i ∈ L)) B z i ds).map (·.p)).sum ≤
      ((L.filter fun r => decide (i ≤ r)).map z).sum
  | [], _ => zero_le _
  | d :: ds, i => by
    have ih := roundGates_sum_from L B z ds (i + 1)
    show (if decide (i ∈ L) = true then z i else 0) +
      ((roundGates (fun i => decide (i ∈ L)) B z (i + 1) ds).map (·.p)).sum ≤ _
    rw [if_congr decide_eq_true_iff rfl rfl]
    exact le_trans (add_le_add le_rfl ih) (roundSum_split z i L)

/-- The gates' numbers add up to no more than z over L: each round once, whatever L holds twice or
beyond the list. -/
theorem roundGates_sum_le (L : List Nat) (B : Nat → List Fmt.Drawn → Bool) (z : Nat → ℝ≥0∞)
    (ds : List RDT) :
    ((roundGates (fun i => decide (i ∈ L)) B z 0 ds).map (·.p)).sum ≤ (L.map z).sum := by
  have h := roundGates_sum_from L B z ds 0
  have e : L.filter (fun r => decide (0 ≤ r)) = L := by simp
  rw [e] at h
  exact h

/-- Each gate is held, where each round at which G is true is. -/
theorem roundGates_held (C : CK) (G : Nat → Bool) (B : Nat → List Fmt.Drawn → Bool)
    (z : Nat → ℝ≥0∞) : ∀ (ds : List RDT) (i : Nat),
    (∀ j d, ds[j]? = some d → G (i + j) = true →
      Iop.prRho {ρ : Iop.Rho (uLT C [d]) | B (i + j) (drawnT C [d] ρ) = true} ≤ z (i + j)) →
    ∀ g ∈ roundGates G B z i ds, ∀ fr, Iop.prRho {ρ : Iop.Rho (uLT C g.ds) |
      g.test fr (drawnT C g.ds ρ) = true} ≤ g.p
  | [], _, _, g, hg, _ => by cases hg
  | d :: ds, i, h, g, hg, fr => by
    rcases List.mem_cons.1 hg with rfl | hg'
    · show Iop.prRho {ρ : Iop.Rho (uLT C [d]) | (G i && B i (drawnT C [d] ρ)) = true} ≤
        (if G i then z i else 0)
      cases hG : G i with
      | false =>
        refine le_trans (Iop.prRho_empty _ fun ρ hρ => ?_) (zero_le _)
        have hρ' : (false && B i (drawnT C [d] ρ)) = true := hρ
        cases hρ'
      | true =>
        have h0 := h 0 d rfl hG
        simpa using h0
    · exact roundGates_held C G B z ds (i + 1) (fun j d' hd hGj => by
        have := h (j + 1) d' hd (by rw [show i + (j + 1) = i + 1 + j by omega]; exact hGj)
        rwa [show i + (j + 1) = i + 1 + j by omega] at this) g hg' fr

/-- **WHAT IS OWED FOR A MARK, FROM BOUNDS OVER ONE ROUND's MESSAGES.** C: the kit, any. dsb: the
data of the member's rounds: it has a round at each number of L (hlen). P: what is handed of the
challenges in front. hsp: at a front that P lets in and at as many challenges as the member has
rounds: where the mark speaks, B is true, at some number r of L, of the member's challenge number r
alone. z r: a bound on the measure, OVER THAT ONE ROUND's MESSAGES, of "B is true at r". -/
theorem markDebt_of_rounds (C : CK) (dsb : List RDT) (mk : Mark) (L : List Nat)
    (B : Nat → List Fmt.Drawn → Bool) (z : Nat → ℝ≥0∞)
    (P : List Fmt.Drawn → Prop)
    (hsp : ∀ fr, P fr → ∀ own, own.length = dsb.length → (mk.test fr own).isSome = true →
      ∃ r ∈ L, B r ((own.drop r).take 1) = true)
    (hlen : ∀ r ∈ L, r < dsb.length)
    (hz : ∀ r ∈ L, ∀ d, dsb[r]? = some d →
      Iop.prRho {ρ : Iop.Rho (uLT C [d]) | B r (drawnT C [d] ρ) = true} ≤ z r) :
    MarkDebt C mk dsb P (L.map z).sum := by
  intro fr hP
  have hH : GatesHeld C (roundGates (fun i => decide (i ∈ L)) B z 0 dsb) fr :=
    gatesHeld_all C _ (roundGates_held C _ B z dsb 0 fun j d hd hG => by
      rw [Nat.zero_add] at hG ⊢
      exact hz j (of_decide_eq_true hG) d hd) fr
  have key := spoken_le C _ dsb (roundGates_ds _ B z 0 dsb) fr hH
  refine le_trans (Prob.pr_mono _ fun ρ hρ => ?_) (le_trans key (roundGates_sum_le _ B z dsb))
  obtain ⟨r, hr, h0⟩ := hsp fr hP _ (drawnT_len C dsb ρ) hρ
  exact (roundGates_spoken _ B z 0 dsb fr _).2 ⟨r, hlen r hr, by
    rw [Nat.zero_add]
    exact decide_eq_true hr, by
    rw [Nat.zero_add]
    exact h0⟩

#print axioms roundGates_ds
#print axioms drop_one_drop
#print axioms roundGates_spoken
#print axioms roundSum_split
#print axioms roundGates_sum_from
#print axioms roundGates_sum_le
#print axioms roundGates_held
#print axioms markDebt_of_rounds

end ProofFile.Honest.Small
