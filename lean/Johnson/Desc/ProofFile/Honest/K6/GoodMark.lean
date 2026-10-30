-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/GoodMark.lean: THE TEST `goodK6` (Honest/K6/Good.lean), TURNED
ROUND, AS A MARK AT THE MEMBER "THE OUTPUT HEAD's OWN ROUNDS" (K6), AND WHAT IS OWED FOR IT
(`MarkDebt`, Honest/Law/CoverJoin.lean). CONDITIONAL. One mark, and lemmas with their proofs. None
of the library's goals.

What a mark is, after Honest/Law/Marks.lean: an event of the challenges at which the verifier
rejects nothing, and which is counted all the same, once: a rejection behind it can be bounded only
where the mark has not spoken. This one speaks where the first element sampled at one of 4 lt + 2
lPd + 2 named rounds is 0 (`goodRounds`; the count: `goodK6Events`, `goodRounds_length`).

  `goodK6Mark`      THE MARK
  `goodK6Mark_speaks`, `goodK6Mark_iff`   where it speaks
  `goodK6_markDebt`   **the debt is met at the sum, over the rounds that the test reads, of a bound
                    over THAT ONE ROUND's messages on "its first sampled element is 0"**: a call of
                    `markDebt_of_rounds` (Honest/Small/MarkRounds.lean); `goodK6_markDebt_one`: at
                    one bound for all
  `goodRounds_lt_of_fits`   the data have a round at each number that the test reads, where they are
                    the declared rounds' own
  `headFirstNo_isSome`, `elemOf_take_one`, `elemOf_at`, `drawsOk_of_fit`, `drawFit_at`   small
                    tools, for this mark and its like

What it is not. NO NUMBER IS EVALUATED, AND NONE IS TO BE QUOTED AS HELD: the kit C of verifier's
messages, the rounds' data dsb and the bounds z are letters. The bound over one round's messages
(hz) is a premise: how a measure over a kit's typed challenges comes from a count of what they show
hangs on the kit. MET FOR NOTHING at z := 1. The mark's stated share (`goodK6Odds`) is a stated
number, no bound: no lemma here spends it. The uniform law on the messages: that the messages of any
run have it is not said. What the mark's silence gives stands in Honest/K6/GoodSilent.lean. Called:
`markDebt_of_rounds` (Honest/Small/MarkRounds.lean), `goodK6_no_iff`, `goodRounds_length`,
`goodRounds_draw` (Honest/K6/GoodRounds.lean). Over files that have not yet landed in the library:
these, and what they import.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Small.MarkRounds
import Johnson.Desc.ProofFile.Honest.Law.Due
import Johnson.Desc.ProofFile.Honest.K6.GoodOdds
import Johnson.Desc.ProofFile.Honest.K6.GoodRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open scoped ENNReal
open OnBytes (E isZeroE okE)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Kinds (Head.Par)
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

/-- **THE MARK**: at the member a, of that member's own challenges alone: it speaks just where
`goodK6` rejects, and names the first clause that fails. The share is a stated number, no bound. -/
def goodK6Mark (p : Head.Par) (a : Place) : Mark :=
  { place := a, test := fun _ own => goodK6Says p own, share := goodK6Odds p }

/-- A first clause that fails is there just if not all hold. -/
theorem headFirstNo_isSome (l : List (String × Bool)) :
    (headFirstNo l).isSome = !(l.all (·.2)) := by
  unfold headFirstNo
  rw [Option.isSome_map]
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [List.find?_cons, List.all_cons]
    cases hc : c.2 with
    | true => simpa using ih
    | false => simp

/-- The mark speaks just where the test rejects. -/
theorem goodK6Mark_speaks (p : Head.Par) (a : Place) (fr own : List Fmt.Drawn) :
    ((goodK6Mark p a).test fr own).isSome = !goodK6 p own :=
  headFirstNo_isSome (goodK6Clauses p own)

/-- It speaks just if at one of the rounds that the test reads the first sampled element is 0. -/
theorem goodK6Mark_iff (p : Head.Par) (a : Place) (fr own : List Fmt.Drawn) :
    ((goodK6Mark p a).test fr own).isSome = true ↔
      ∃ r ∈ goodRounds p, isZeroE (elemOf own r) = true := by
  rw [goodK6Mark_speaks, Bool.not_eq_true', goodK6_no_iff]

/-- The first element of the first challenge, of the list and of its first member alone. -/
theorem elemOf_take_one (dr : List Fmt.Drawn) : elemOf (dr.take 1) 0 = elemOf dr 0 := by
  cases dr <;> rfl

/-- The first element of the member's challenge number r, of the list and of that challenge alone.
-/
theorem elemOf_at (own : List Fmt.Drawn) (r : Nat) :
    elemOf ((own.drop r).take 1) 0 = elemOf own r := by
  rw [elemOf_take_one]
  unfold elemOf
  rw [List.getElem?_drop, Nat.add_zero]

/-! ## From one round's messages -/

/-- **WHAT IS OWED FOR THE MARK, FROM BOUNDS OVER ONE ROUND's MESSAGES.** C: the kit, any. dsb: the
data of the member's rounds: it has a round at each number that the test reads (hlen). z r: at the
round number r, a bound on the measure, OVER THAT ONE ROUND's MESSAGES, of "the first element that
the round samples is 0". P: what is handed of the challenges in front: any: the test reads none. -/
theorem goodK6_markDebt (C : CK) (dsb : List RDT) (p : Head.Par) (a : Place) (z : Nat → ℝ≥0∞)
    (hlen : ∀ r ∈ goodRounds p, r < dsb.length)
    (hz : ∀ r ∈ goodRounds p, ∀ d, dsb[r]? = some d →
      Iop.prRho {ρ : Iop.Rho (uLT C [d]) | isZeroE (elemOf (drawnT C [d] ρ) 0) = true} ≤ z r)
    (P : List Fmt.Drawn → Prop) :
    MarkDebt C (goodK6Mark p a) dsb P ((goodRounds p).map z).sum :=
  Small.markDebt_of_rounds C dsb (goodK6Mark p a) (goodRounds p)
    (fun _ l => isZeroE (elemOf l 0)) z P
    (fun fr _ own _ h => by
      obtain ⟨r, hr, h0⟩ := (goodK6Mark_iff p a fr own).1 h
      exact ⟨r, hr, (congrArg isZeroE (elemOf_at own r)).trans h0⟩)
    hlen hz

/-- The same at one number for all rounds. -/
theorem goodK6_markDebt_one (C : CK) (dsb : List RDT) (p : Head.Par) (a : Place) (z : ℝ≥0∞)
    (hlen : ∀ r ∈ goodRounds p, r < dsb.length)
    (hz : ∀ r ∈ goodRounds p, ∀ d, dsb[r]? = some d →
      Iop.prRho {ρ : Iop.Rho (uLT C [d]) | isZeroE (elemOf (drawnT C [d] ρ) 0) = true} ≤ z)
    (P : List Fmt.Drawn → Prop) :
    MarkDebt C (goodK6Mark p a) dsb P ((goodK6Events p : ℝ≥0∞) * z) := by
  have h := goodK6_markDebt C dsb p a (fun _ => z) hlen hz P
  rw [List.map_const', List.sum_replicate, nsmul_eq_mul, goodRounds_length] at h
  exact h

/-- hlen, where the data are the declared rounds' own. -/
theorem goodRounds_lt_of_fits (p : Head.Par) (dsb : List RDT)
    (h : List.Forall₂ KindFits dsb p.rounds) : ∀ r ∈ goodRounds p, r < dsb.length := by
  intro r hr
  have h1 := goodRounds_draw p r hr
  unfold headDrawsAt at h1
  obtain ⟨d, hd, _⟩ := Option.map_eq_some_iff.1 h1
  rw [h.length_eq]
  exact (List.getElem?_eq_some_iff.1 hd).1

/-! ## Two tools on challenges that fit declared rounds -/

/-- Every word of every sampled element is below the prime. -/
theorem drawsOk_of_fit : ∀ (zs : List Fmt.DeclaredRound) (own : List Fmt.Drawn),
    drawsFit zs own = true → (own.all fun d => (elemsOf d).all okE) = true
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | z :: zs, R :: Rs, h => by
    have h' : (drawFit z R && drawsFit zs Rs) = true := h
    rw [Bool.and_eq_true] at h'
    rw [List.all_cons, Bool.and_eq_true]
    refine ⟨?_, drawsOk_of_fit zs Rs h'.2⟩
    have hf := h'.1
    unfold drawFit at hf
    simp only [Bool.and_eq_true] at hf
    have hw := hf.1.2
    unfold elemsOf
    rw [List.all_map]
    exact hw

/-- The round number r has its challenge, and that one fits. -/
theorem drawFit_at : ∀ (zs : List Fmt.DeclaredRound) (own : List Fmt.Drawn), drawsFit zs own = true →
    ∀ (r : Nat) (d : Fmt.DeclaredRound), zs[r]? = some d → ∃ R, own[r]? = some R ∧ drawFit d R = true
  | [], _, _, r, d, hd => by cases hd
  | _ :: _, [], h, _, _, _ => by cases h
  | z :: zs, R :: Rs, h, r, d, hd => by
    have h' : (drawFit z R && drawsFit zs Rs) = true := h
    rw [Bool.and_eq_true] at h'
    cases r with
    | zero =>
      obtain rfl : z = d := Option.some.inj hd
      exact ⟨R, rfl, h'.1⟩
    | succ r => exact drawFit_at zs Rs h'.2 r d hd

#print axioms headFirstNo_isSome
#print axioms goodK6Mark_speaks
#print axioms goodK6Mark_iff
#print axioms elemOf_take_one
#print axioms elemOf_at
#print axioms goodK6_markDebt
#print axioms goodK6_markDebt_one
#print axioms goodRounds_lt_of_fits
#print axioms drawsOk_of_fit
#print axioms drawFit_at

end ProofFile.Honest.K6
