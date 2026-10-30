-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Top/OnePlanner.lean: two returns of the planner give the key file's maker's return,
and the return of the proof file's own copy of the planner.

Two returns are named: hX, that `publicOfO` (Johnson/Desc/Ok/PlanWritten/PublicAt.lean) returns X₀
at the three public files; hm, that `Key.madeAt` (Johnson/Desc/Key/Road.lean) returns m at X₀, the
layout file and the fixed digest.

Main names:
  `keyLaid_of_parts`: from hX, hm and the return of `Key.keyDataAndDecisionOfPlannerAnswer` at X₀ and m (the key file's
    IOP as written in Lean, its tests and its entry tests), `theKeyLaid` returns that value.
  `madeOf_of_madeAt`: from hX and hm, the proof file's own copy of the planner
    (`ProofFile.PlainG.madeOf`, Johnson/Desc/ProofFile/PlanPlain.lean) returns m with the segments'
    routines blanked (`ProofFile.Law.blankM`).

What is not claimed. THAT EITHER RETURN HOLDS AT ANY FILES. That anything runs once: two texts are
shown to return one value, but for the blanked field, of whose content the equations say nothing.
Nothing on soundness.

-/
import Johnson.Goal.Description.PlanKey
import Johnson.Desc.ProofFile.Law.PlainIsMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifierAndGoals
open OnBytes.Params (exc_bind)
open VerifiableInference.PlanWritten (publicOfO plannedAtO madeOfAtO)
open VerifiableInference.Desc.Key

/-- **The key file's maker returns, from three returns inside it.** -/
theorem keyLaid_of_parts {Z : PublicFiles} {X₀ : OnBytes.Model.Verify.Public}
    {m : Johnson.G.OfPlan.Made} {K : OnBytes.Maker.WholeD × KeyRun}
    (hX : publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : madeAt X₀ Z.lay fixedDigest = .ok m) (hB : keyDataAndDecisionOfPlannerAnswer X₀ Z.lay m = .ok K) :
    theKeyLaid (asDescriptionFiles Z) = .ok K := by
  show (publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay)).bind (fun X => keyDataAndDecisionAtFixedDigest X Z.lay) = .ok K
  rw [hX]
  show (madeAt X₀ Z.lay fixedDigest).bind (keyDataAndDecisionOfPlannerAnswer X₀ Z.lay) = .ok K
  rw [hm]
  exact hB

/-- **The proof file's copy of the planner returns what the key file's has made**, the segments'
routines blanked. -/
theorem madeOf_of_madeAt {o : SecondHashFunctionType} {pol KL lay : ByteArray} {X₀ : OnBytes.Model.Verify.Public}
    {m : Johnson.G.OfPlan.Made} (hX : publicOfO o pol KL (some lay) = .ok X₀)
    (hm : madeAt X₀ lay fixedDigest = .ok m) :
    ProofFile.PlainG.madeOf o pol lay KL = .ok (ProofFile.Law.blankM m) := by
  have hp := (plannedAtO_of_madeAt hX hm).1
  have hs : (VerifiableInference.Number.sendsFrom m.p.chains.made >>=
      VerifiableInference.Number.packMade m.p) = .ok m := by
    unfold madeAt at hm
    obtain ⟨chains, _, hm⟩ := exc_bind hm
    obtain ⟨built, _, hm⟩ := exc_bind hm
    obtain ⟨l, h3, hm⟩ := exc_bind hm
    split at hm
    · cases hm
      have e : Johnson.G.sendsFrom chains.made =
          VerifiableInference.Number.sendsFrom chains.made := rfl
      show (VerifiableInference.Number.sendsFrom chains.made >>= _) = _
      rw [← e, h3]
      rfl
    · cases hm
  rw [ProofFile.Law.madeOf_eq]
  unfold madeOfAtO
  rw [show VerifiableInference.Desc.fixedConfigurationDigest = fixedDigest from rfl, hp]
  show (VerifiableInference.Number.sendsFrom m.p.chains.made >>=
      VerifiableInference.Number.packMade m.p).map ProofFile.Law.blankM = _
  rw [hs]
  rfl

end FlashProve

#print axioms FlashProve.keyLaid_of_parts
#print axioms FlashProve.madeOf_of_madeAt
