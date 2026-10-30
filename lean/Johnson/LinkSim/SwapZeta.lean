-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/SwapZeta.lean: how the written error of index privacy changes when the link's
prover and simulator are substituted.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has (namespace OnBytes.LinkSim). All statements hold for all parameters.
  zetaW_swap_add   the error zetaW (Johnson/WholeKey/Zeta.lean) after the substitution (layLink,
      layNums, Johnson/LinkSim/Swap.lean), plus (M + 1) * N.zL and (M + 1) * N.hL, equals the error
      at a₀ and N. Here M + 1 is the number of copies, and N.zL and N.hL are N's two error terms
      for the link: simulation and aborts.
  zetaW_swap_le   so the error after the substitution is at most the error at a₀ and N, for all
      numbers of queries and of requests.
  zetaW_swap_eq   and equal where N's two error terms for the link are 0 already.
  zetaW_of_four   two structures of parameters with the same number of copies and the same three
      bounds on proof-of-work attempts have the same error, for all other parameters.
  zetaW_layLink   so the substitution keeps a₀'s error, for any numbers.
  zetaW_layNums   for any structure of parameters a, the error at layNums N plus (a.M + 1) * N.zL
      and (a.M + 1) * N.hL equals the error at N.

How it fits. Johnson/LinkSim/Swap.lean carries the premises of index privacy from a₀ to the
parameters after the substitution. Whoever then applies the statement of index privacy there uses
its error there. Of the honest party's parameters the error formula reads the number of copies and
the three bounds on attempts, and nothing else; the substitution keeps these four.
Johnson/LinkSim/AtHome/FitZeta.lean applies zetaW_of_four and zetaW_layNums at homeR b Z; no file
under Johnson/LinkSim/ calls zetaW_swap_le or zetaW_swap_eq. They serve whoever applies index
privacy after the substitution and wants the error there.

Limits. These are facts on the error's formula; they say nothing on whether the error is small.
Nothing says that either error is below 1, and at a bound of 1 or more the clause on the distance in
a statement of index privacy is trivially true, and only the clause on the simulator's trace is
left. "At most" compares two written numbers; the parameters before and after the substitution
define two different schemes. The error is in the extended non-negative reals, so "less" is said by
a sum.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.Swap
import Johnson.WholeKey.Zeta

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LinkSim
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (Sd : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (p : Params)

/-- **Of the honest party's parameters the error reads only the number of copies and the three
bounds on proof-of-work attempts.** -/
theorem zetaW_of_four (a a' : AtRecs lam L Bd aT aL) (c : CoinNums Bd) (u : NumsW)
    (hM : a.M = a'.M) (hT : a.capT = a'.capT) (hL : a.capL = a'.capL) (hB : a.capB = a'.capB) :
    zetaW W Sd p a c u = zetaW W Sd p a' c u := by
  cases a
  cases a'
  dsimp only at hM hT hL hB
  subst hM hT hL hB
  rfl

/-- For any structure of parameters a: the error at layNums N plus (a.M + 1) * N.zL and
(a.M + 1) * N.hL equals the error at N. -/
theorem zetaW_layNums (a : AtRecs lam L Bd aT aL) (c : CoinNums Bd) (N : NumsW) (t n : ℕ) :
    zetaW W Sd p a c (layNums N) t n +
        (((a.M + 1 : ℕ) : ℝ≥0∞) * N.zL + ((a.M + 1 : ℕ) : ℝ≥0∞) * N.hL) =
      zetaW W Sd p a c N t n := by
  unfold zetaW layNums
  simp only [mul_zero, add_zero]
  ring

section
variable (a₀ : AtRecs lam L Bd aT aL) (c : CoinNums Bd)
  (H : Honest L.link (I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed))) (kL : Enum H.Coin) (v₀ : a₀.RV)
  (E : Enum (RunBits lam a₀.nR a₀.nK a₀.nJ p.sFS c.ℓ c.ℓr W.depthReqL))

/-- The substitution keeps a₀'s error. -/
theorem zetaW_layLink (c' : CoinNums Bd) (u : NumsW) :
    zetaW W Sd p (layLink W p a₀ c H kL v₀ E) c' u = zetaW W Sd p a₀ c' u :=
  zetaW_of_four W Sd p _ _ c' u rfl rfl rfl rfl

/-- The error after the substitution, plus (M + 1) * N.zL and (M + 1) * N.hL, equals the error
before. -/
theorem zetaW_swap_add (N : NumsW) (t n : ℕ) :
    zetaW W Sd p (layLink W p a₀ c H kL v₀ E) c (layNums N) t n +
        (((a₀.M + 1 : ℕ) : ℝ≥0∞) * N.zL + ((a₀.M + 1 : ℕ) : ℝ≥0∞) * N.hL) =
      zetaW W Sd p a₀ c N t n := by
  rw [zetaW_layLink]
  exact zetaW_layNums W Sd p a₀ c N t n

/-- **The error after the substitution is at most the error at a₀.** -/
theorem zetaW_swap_le (N : NumsW) (t n : ℕ) :
    zetaW W Sd p (layLink W p a₀ c H kL v₀ E) c (layNums N) t n ≤ zetaW W Sd p a₀ c N t n :=
  (zetaW_swap_add W Sd p a₀ c H kL v₀ E N t n) ▸ le_self_add

/-- Equal where the link's two error terms are 0 already. -/
theorem zetaW_swap_eq (N : NumsW) (hz : N.zL = 0) (hh : N.hL = 0) (t n : ℕ) :
    zetaW W Sd p (layLink W p a₀ c H kL v₀ E) c (layNums N) t n = zetaW W Sd p a₀ c N t n := by
  rw [← zetaW_swap_add W Sd p a₀ c H kL v₀ E N t n, hz, hh, mul_zero, add_zero, add_zero]

end

end OnBytes.LinkSim

#print axioms OnBytes.LinkSim.zetaW_of_four
#print axioms OnBytes.LinkSim.zetaW_layNums
#print axioms OnBytes.LinkSim.zetaW_layLink
#print axioms OnBytes.LinkSim.zetaW_swap_add
#print axioms OnBytes.LinkSim.zetaW_swap_le
#print axioms OnBytes.LinkSim.zetaW_swap_eq
