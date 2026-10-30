-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Sc3.lean: CONDITIONAL: the verifier's end term of a sumcheck of weighted
products, READ IN A FIELD, against the honest side's summand. Statements with their proofs. rho: any
reading (OnBytes/Model/HideLaws.lean).

The verifier's row of such a sumcheck (`left`, Johnson/Desc/First/Att/LeftP.lean) holds, where it
returns, by the library's `left_spec` (K5LeftLaw.lean beside it), the end term `sc3Flat`
(OnBytes/Tie/Pv/Att/Flat.lean): the sum over the pieces b of W_b times what is shown for the end
values 2 b and 2 b + 1. All of an attention segment's sumchecks but the one for the key at the index
are of this form; their summands' terms are `pairsOf` (Johnson/Desc/K5/Honest/Index.lean).

Main names:
  `Summand.formula_pairs`   where the terms at a point are `pairsOf np W`, the summand's formula
                            (TermsLaw.lean of this folder) is that sum, on any values
  `Summand.named_pairs`     such a summand with 2 np end values names end values alone
  `s0_is_cf`                **the end term, read, is the formula.** CONDITIONAL on: the terms at the
                            point are `pairsOf np W`; the verifier's weights are np and read as W's;
                            what the verifier takes for end value j reads as the value laid in the
                            formula. Whoever reads the weights and the ledger pays these.

Limits. Nothing says what the weights or the shown values are. Nothing is claimed on soundness,
completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.TermsLaw
import Johnson.Desc.K5.Honest.Index
import OnBytes.Tie.Pv.Att.Flat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open OnBytes.Tie.Pv.Att (sc3Flat sc3Flat_read)

variable {K : Type} [Field K] (ρ : Reading K)

namespace Lists

theorem sum_range_map (g : Nat → K) : ∀ n : Nat,
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_map g n,
      Finset.sum_range_succ]
    simp

end Lists

open Lists

/-- Where the terms at x are weighted products of two end values, the formula is the sum over the
pieces of the weight times the two values. -/
theorem Summand.formula_pairs (S : Summand) (x : List E) (np : Nat) (W : Array E)
    (h : S.terms x = pairsOf np W) (ev : Nat → K) :
    S.formula ρ x ev =
      ∑ b ∈ Finset.range np, ρ.val (W.getD b zeroE) * ev (2 * b) * ev (2 * b + 1) := by
  unfold Summand.formula
  rw [h]
  unfold pairsOf
  rw [List.map_map, sum_range_map]
  refine Finset.sum_congr rfl fun b _ => ?_
  show ρ.val (W.getD b zeroE) * ([(⟨oneE, 2 * b, zeroE⟩ : Factor), ⟨oneE, 2 * b + 1, zeroE⟩].map
    fun f => ρ.val f.a * ev f.n + ρ.val f.b).prod = _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, ρ.one, ρ.zero]
  ring

/-- Such a summand with 2 np end values names end values alone. -/
theorem Summand.named_pairs (S : Summand) (np : Nat) (he : S.ends = 2 * np)
    (h : ∀ x : List E, x.length = S.vars → ∃ W, S.terms x = pairsOf np W) :
    S.Named (2 * np) := by
  refine ⟨he, fun x hx t ht f hf => ?_⟩
  obtain ⟨W, hW⟩ := h x hx
  rw [hW] at ht
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ht
  have hb' := List.mem_range.1 hb
  rcases List.mem_cons.1 hf with rfl | hf
  · show 2 * b < 2 * np
    omega
  · rw [List.mem_singleton.1 hf]
    show 2 * b + 1 < 2 * np
    omega

/-- **The verifier's end term of a sumcheck of products, read, is the summand's formula**,
CONDITIONAL on: the summand's terms at rs are weighted products under weights W; the verifier's
weights Wt are as many and read alike; what the verifier takes for end value j reads as ev j. -/
theorem s0_is_cf (S : Summand) (rs : List E) (np : Nat) (W Wt : Array E) (sh : Nat → E)
    (ev : Nat → K) (ht : S.terms rs = pairsOf np W) (hsz : Wt.size = np)
    (hW : ∀ b, b < np → ρ.val (Wt.getD b zeroE) = ρ.val (W.getD b zeroE))
    (hsh : ∀ j, j < 2 * np → ρ.val (sh j) = ev j) :
    ρ.val (sc3Flat Wt sh Wt.size 0 zeroE) = S.formula ρ rs ev := by
  subst hsz
  rw [sc3Flat_read ρ Wt sh Wt.size, S.formula_pairs ρ rs _ W ht ev, Finset.sum_range]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hW b.1 b.2, hsh (2 * b.1) (by omega), hsh (2 * b.1 + 1) (by omega)]

end H2K5.Honest

#print axioms H2K5.Honest.Lists.sum_range_map
#print axioms H2K5.Honest.Summand.formula_pairs
#print axioms H2K5.Honest.Summand.named_pairs
#print axioms H2K5.Honest.s0_is_cf
