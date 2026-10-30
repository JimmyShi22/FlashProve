-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawCap.lean: THE SMALLNESS TEST, ITS FIRST HALF: "ITS COUNT IS AT MOST THE
CAP", WITH NO FACTOR FOR THE SAMPLER'S BIAS, AS CLOSED PROPOSITIONS BY NAME.

The round of the draw is priced at 2 ^ -(the number of combinations) to the letter: there is no
room under a cap at that price. So it matters that the proved block's count, carried to the round's
written verifier messages, bears no factor above 1. `RoundBelow n d ε` (OnBytes/Slice/ManyErr.lean)
is, unfolded: n times the sampler's number w is at most ε times the number of the round's written
verifier messages: no further factor stands in it. Nothing is proved anew here: each theorem is one
of Johnson/Desc/First/K8/LawPrice.lean, LawParted.lean or Johnson/Flat/NoRoomSmall.lean, with its
arguments bound.
  `K08CountBelow`: at every place and all sizes with the place's numbers: the proved block's count
    (the values that can be drawn, divided by 2 ^ tau) is a share of at most 2 ^ -tau.
  `K08CountCap128`: at 128 combinations: of at most 2 ^ -128.
  `K08CountNoRoom`: at 128 combinations and at least one column: ONE MORE bad value is too many,
    and 2 ^ -129 is not met: the room is 0.
Limits. THE COUNT IS THAT OF ONE INSTANCE: no factor for a number of instances or of slots stands in
it. That a place has 128 combinations is a premise of the second and the third. That the count of
bad values of the protocol's round is at most the proved block's count is the proved block's
theorem, under the letters of Johnson/Desc/First/K8/LawPiece.lean. Why the factor is 1: the round
draws matrix entries alone (`onlyTrits`, Johnson/Desc/First/K8/Law.lean), and the sampler's bias is
a factor for each drawn element of the extension field (`below_round_div_ex`,
OnBytes/Slice/RatesEx.lean).

-/
import Johnson.Desc.First.K8.LawParted

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Desc.First.K8

open Cb.Pv.Tail OnBytes.Slice VerifiableInference.Number

def K08CountBelow : Prop :=
  ∀ (p : Par) (s : Size), Fits p s →
    RoundBelow (Fintype.card (Dr s) / 2 ^ s.tau) (rd p) ((2 : ℝ≥0∞)⁻¹ ^ s.tau)

theorem k08CountBelow : K08CountBelow := fun _ _ hf => hear_price_tau hf

def K08CountCap128 : Prop :=
  ∀ (p : Par) (s : Size), Fits p s → p.tau = 128 →
    RoundBelow (Fintype.card (Dr s) / 2 ^ s.tau) (rd p) ((2 : ℝ≥0∞)⁻¹ ^ 128)

theorem k08CountCap128 : K08CountCap128 := fun _ _ hf hτ => hear_price hf hτ

def K08CountNoRoom : Prop :=
  ∀ (p : Par) (s : Size), Fits p s → p.tau = 128 → 1 ≤ s.columns →
    ¬ RoundBelow (Fintype.card (Dr s) / 2 ^ s.tau + 1) (rd p) ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧
      ¬ RoundBelow (Fintype.card (Dr s) / 2 ^ s.tau) (rd p) ((2 : ℝ≥0∞)⁻¹ ^ 129)

theorem k08CountNoRoom : K08CountNoRoom := fun _ s hf hτ hc => by
  rw [card_dr_div s (hf.tau.trans hτ)]
  exact ⟨not_below_succ hc (entriesOnly hf hτ), not_below_129 hc (entriesOnly hf hτ)⟩

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.k08CountBelow
#print axioms VerifiableInference.Desc.First.K8.k08CountCap128
#print axioms VerifiableInference.Desc.First.K8.k08CountNoRoom
