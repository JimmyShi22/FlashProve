-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/DrawFits.lean: WHAT THE LAW ON A SEGMENT's FIRST PLACE (`LinkPlain`,
Returns/LinkSent.lean) ASKS OF THE VERIFIER's OWN DRAWS FOLLOWS FROM THE TEST ON ROUNDS THAT
`Block.step` RUNS IN FRONT OF EVERY DECISION (`roundsFit`, Johnson/Desc/Block.lean), AT THE KIND's
OWN TWO ROUNDS, UNDER TWO TIES OF THE PLAN's NUMBERS TO THE SENDING's PUBLIC LETTER. Statements and
proofs.

NOTHING ON A ROUND OF SEEDS IS PROVED ANEW: `zip_factors` (Johnson/Prover/Send/Factors.lean) and
`dsElems_place` (Johnson/Prover/Send/Form.lean) are called; the proof follows `factors_of_fit`
there, which has the like at the sending kind's own rounds.

  `dsElems_tied` the format's list of a round of seeds, at an entry whose two counts are the
                    letter's
  `rounds_give` THE STATEMENT: rounds that fit the kind's rounds, p.seeds = seeds * (coordinates +
                    1) and p.nonZero = seeds give five fields of `LinkPlain`: `range` · `draw` ·
                    `poss` · `trits` · `factor`
  `rounds_give_shown` the same at the two rounds as a decision is shown them: without the digest

Limits. THE TWO TIES ARE PREMISES: that a plan's numbers meet them is not shown here. "No factor is
0" is said of words, as the sending's text says it. Of the rounds' items (`vals`, `answers`), of
`fits₁` and of `locOk` nothing is said. What `roundsFit` says of two rounds' counts and range
stands, general in the rounds, in Johnson/Prover/Link/FormSwitchLaws.lean too (`fit_says`): not
called. Nothing on how a round is drawn. Nothing on any property.

-/
import Johnson.Prover.Send.Form
import Johnson.Top.H0.Tw.K2C.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (roundsFit drawsMarkedNonzeroHaveNonzeroWords noDigest)
open VerifiableInference.Desc.First.K2 (P2 rounds)
open Johnson.Prover.Send (zip_factors dsElems_place)

theorem dsElems_tied (e : Fmt.Entry) (Z : K1.Par) (h0 : Z.seeds ≠ 0)
    (hE : e.drawE = Z.seeds * (Z.coordinates + 1)) (hN : e.drawNZ = Z.seeds) :
    Fmt.dsElems e .seeds = Fmt.dsSeeds Z.seeds Z.coordinates := by
  rw [← dsElems_place Z h0]
  unfold Fmt.dsElems
  rw [if_pos rfl, if_pos rfl, hE, hN]
  rfl

/-- **Rounds that fit give what the law asks of the draws.** -/
theorem rounds_give (p : P2) (Z : K1.Par) (r₁ r₂ : Fmt.RoundView)
    (hE : p.seeds = Z.seeds * (Z.coordinates + 1)) (hN : p.nonZero = Z.seeds)
    (h : roundsFit (rounds p) [r₁, r₂] = true) :
    (∀ q ∈ r₂.drawn.poss, q < 2 ^ p.logN) ∧
      (r₁.drawn.elems.map E.ofTriple).length = Z.seeds * (Z.coordinates + 1) ∧
      r₁.drawn.poss = [] ∧ r₁.drawn.trits = [] ∧
      ∀ z ∈ K1.seedsOf Z r₁, isZeroE z.2 = false := by
  simp only [rounds, roundsFit, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨_, e1⟩, p1⟩, t1⟩, _⟩, _⟩, nz⟩, ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, q2⟩, _⟩, _⟩, _⟩ := h
  have hlen : r₁.drawn.elems.length = Z.seeds * (Z.coordinates + 1) := (beq_iff_eq.1 e1).trans hE
  refine ⟨fun q hq => of_decide_eq_true (List.all_eq_true.1 q2 q hq), by rw [List.length_map, hlen],
    List.length_eq_zero_iff.1 (beq_iff_eq.1 p1), List.length_eq_zero_iff.1 (beq_iff_eq.1 t1), ?_⟩
  by_cases h0 : Z.seeds = 0
  · intro z hz
    unfold K1.seedsOf at hz
    rw [h0] at hz
    simp [K1.cutSeeds] at hz
  · unfold drawsMarkedNonzeroHaveNonzeroWords at nz
    have hkind : Fmt.kindOf "SEND seed" = some .seeds := by decide
    simp only [hkind, Option.any_some] at nz
    rw [dsElems_tied _ Z h0 hE hN] at nz
    exact zip_factors Z.coordinates Z.seeds r₁.drawn.elems hlen nz

/-- The same at the rounds as a decision is shown them. -/
theorem rounds_give_shown (p : P2) (Z : K1.Par) (r₁ r₂ : Fmt.RoundView)
    (hE : p.seeds = Z.seeds * (Z.coordinates + 1)) (hN : p.nonZero = Z.seeds)
    (h : roundsFit (rounds p) [r₁, r₂] = true) :
    (∀ q ∈ (noDigest r₂).drawn.poss, q < 2 ^ p.logN) ∧
      ((noDigest r₁).drawn.elems.map E.ofTriple).length = Z.seeds * (Z.coordinates + 1) ∧
      (noDigest r₁).drawn.poss = [] ∧ (noDigest r₁).drawn.trits = [] ∧
      ∀ z ∈ K1.seedsOf Z (noDigest r₁), isZeroE z.2 = false :=
  rounds_give p Z r₁ r₂ hE hN h

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.dsElems_tied
#print axioms VerifiableInference.Desc.K2.Honest.Returns.rounds_give
#print axioms VerifiableInference.Desc.K2.Honest.Returns.rounds_give_shown
