-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerErr128.lean: THE ERRORS OF THE LOOKUP's WRITTEN ROUNDS AT THE LEVEL
OF 128 BITS A ROUND: two corollaries of Johnson/Desc/First/Look/K3CallerErrW.lean. NO SOUNDNESS OF
ANY TEXT THAT RUNS IS CLAIMED.

Why. K3CallerErrW.lean bounds each written round's error by 2^-157 of that round's own challenge
values. A condition at the level of 128 bits a round asks the bound 2^-128.

Main names.
  pow157_le: 2^-157 ≤ 2^-128.
  lookupC_written128: lookupC_written at 2^-128: for every caller whose record passes FoNums.ok, at
    any number of test bits.
  dig_written128: dig_written at 2^-128: at the closed caller of a link's digits.
Limits. Those of K3CallerErrW.lean: a share is a count among all strings of hash blocks and test
bits: nothing on the hash function; round by round: no sum over the rounds is bounded here. The
errors are the least that bear the proved block's (bearT), not a cap.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerErrW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole Cb.Fo TwRound
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open scoped ENNReal

theorem pow157_le : ((2 : ℝ≥0∞)⁻¹ ^ 157) ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 := by
  have h1 : (2 : ℝ≥0∞)⁻¹ ≤ 1 := ENNReal.inv_le_one.2 one_le_two
  exact pow_le_pow_right_of_le_one' h1 (by norm_num)

/-- **Each written round of a lookup: at most 2^-128 of its own challenge values.** -/
theorem lookupC_written128 (L : List LookupCCaller) (hL : OkLookupC L) (c : LookupCCaller)
    (hc : c ∈ L) (wk : ℕ) (ds : List RDT) (hP : ∀ d ∈ ds, Plain (toRD d))
    (he : ds.map (·.entry) = forEnts wk c.h) (ε' : Err (uLT (ckP .two) ds))
    (hb : bearT ds _ ((kLookupC L).ε c) = some ε') : Err.Below ε' ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  Err.Below.mono_bound pow157_le (lookupC_written L hL c hc wk ds hP he ε' hb)

end VerifiableInference.OnPublicFiles

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model VerifiableInference.OnPublicFiles
open scoped ENNReal

/-- **The same at the closed caller of a link's digits.** -/
theorem dig_written128 {set : Params.Setting} {x : Place} {tl : HTailF2} {D : Sent}
    {rad : OracleShape → Nat} {pp : Nat} (Ex : Iop.ExtSpec) (Wp : Type)
    (H : DigOK set x tl D rad pp) (ds : List OnBytes.Maker.RDT)
    (hP : ∀ d ∈ ds, Fo.Peel.Plain (OnBytes.Flat.toRD d))
    (he : ds.map (·.entry) = (P.ofPlace set true x).rounds.map (·.entry))
    (ε' : Iop.Err (OnBytes.Maker.uLT (_root_.Run.ckP .two) ds))
    (hb : Fo.Peel.bearT ds _ ((kLookupCR [noRider (digCaller x tl D rad Ex Wp)]).ε
      (noRider (digCaller x tl D rad Ex Wp))) = some ε') :
    Iop.Err.Below ε' ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  Iop.Err.Below.mono_bound pow157_le (dig_written Ex Wp H ds hP he ε' hb)

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.OnPublicFiles.lookupC_written128
#print axioms VerifiableInference.Desc.First.Look.dig_written128
