-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFGuard/StrikeAt.lean: the proofs of the four statements of
Johnson/LPFGuard/AtDescription.lean. Statements there; proofs here.

Main names.
* `laidPBare_eq`: `laidPBare = LPFD.Full.proofDataAndDecisionOfPublicFiles`, as functions: `strike` (Strike.lean) and
  `funext`.
* `strike_description`: `theDescriptionBare` is `Text.theDescription laidPBare`; by `laidPBare_eq`
  that is `Text.theDescription LPFD.Full.proofDataAndDecisionOfPublicFiles`, which is `VerifierAndGoals.theDescription`
  (`Text.theDescription_at`, DoorText.lean).
* `verify_congr`: at two equal descriptions, each with its own parser, and at two forms that are
  equal across the two types, `VerifierAndGoals.verify` is the same.
* `strike_verdict`: `verify_congr` at `strike_description`; the form's type is
  `FlashProve.FormBytes` at both, by unfolding.
* `strike_system`, `strike_any`: by rewriting with `strike_description`.

Limits. AtDescription.lean's eleven and Unguarded.lean's eleven, whole.

For proofs only; no program imports this file.


-/
import Johnson.LPFGuard.AtDescription
import Johnson.LPFGuard.Strike

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFGuard

open VerifiableInference (Commitment Token)

theorem laidPBare_eq : laidPBare = LPFD.Full.proofDataAndDecisionOfPublicFiles := by
  funext o pol lay KL
  exact strike o pol lay KL

/-- **At the goals' description.** -/
theorem strike_description : Spec.strike_description := by
  unfold Spec.strike_description theDescriptionBare
  rw [laidPBare_eq]
  exact Text.theDescription_at.symm

theorem verify_congr {D D' : VerifierAndGoals.Description} (h : D = D') (Z : VerifierAndGoals.PublicFiles)
    (commitment : Commitment) (prompt output : List Token) (B : D.Form) (B' : D'.Form)
    (hB : HEq B B') :
    VerifierAndGoals.verify D Z (D.parse Z) commitment prompt output B =
      VerifierAndGoals.verify D' Z (D'.parse Z) commitment prompt output B' := by
  subst h
  rw [eq_of_heq hB]

/-- **At `VerifierAndGoals.verify`.** -/
theorem strike_verdict : Spec.strike_verdict := fun o Z commitment prompt output B =>
  verify_congr (congrFun strike_description o) Z commitment prompt output B B HEq.rfl

/-- **At the argument system of which the goals on the honest side and on binding speak.** -/
theorem strike_system : Spec.strike_system := fun o Z s => by rw [strike_description]

theorem strike_any : Spec.strike_any := fun P => by rw [strike_description]

end LPFGuard

#print axioms LPFGuard.laidPBare_eq
#print axioms LPFGuard.strike_description
#print axioms LPFGuard.verify_congr
#print axioms LPFGuard.strike_verdict
#print axioms LPFGuard.strike_system
#print axioms LPFGuard.strike_any
