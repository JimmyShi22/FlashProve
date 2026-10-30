-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/HomeInputTie.lean: how the parameters with an all-zero digest, `homeR b Z`, relate to the
verifier's parameters at Z.

Summary. E2E/LinkLaidPrivacy.lean and the files that build on it are stated at `homeR b Z`
(Johnson/Goal/Conditions/HomeAtWider.lean); the other files of this group are stated at the
verifier's parameters, `(atSecondHashFunction theDescription).input Z c m`. This file proves two equations
between the two. No statement here is about a prover, a distribution or a simulator. The main limit:
the equations are for one digest, all zeros; that `VerifierAndGoals.verify` is ever called at this digest is
not proved.

Main results.
  `home_is_reBound`: for every b and Z there is a second public reading m such that `homeR b Z` is
    `(atSecondHashFunction theDescription).input Z allZeroDigest m` with one field reset: `coinBound`, a number of coins, to
    b Z.
  `home_is_own`: for every Z there are a b and an m such that `homeR b Z` is `(atSecondHashFunction
    theDescription).input Z allZeroDigest m` itself: b Z is those parameters' own number of coins.

How. `homeR b Z` is by definition the parameters of the value that the library builds, with `coinBound`
reset (`VerifierAndGoals.input_reBound`); that value is the description where the library's top-level
statements read it (`VerifierAndGoals.ofBuilt`).

Terms: E2E/HidingTerms.lean.

Limits.
- Which m it is, is not stated ("there is"): in the proof it is the empty list at the built value.
- Tied: for the b of `home_is_own`, `homeR b Z` is one of the verifier's parameters at Z, namely at
  c := `allZeroDigest` and one m; for any other b it differs from them in the field `coinBound` alone, which the
  verifier does not read (`VerifierAndGoals.verify_reBound`, Johnson/Goal/Conditions/ReBound.lean).
- Not tied: to the digest and the second reading that `VerifierAndGoals.verify` computes from Z.
- Statements of the form P r pass along the equation by rewriting (`atHome`,
  E2E/LinkLaidPrivacy.lean, does so). Those of E2E/LinkLaidPrivacy.lean and the files that build on
  it name terms typed at `homeR b Z` (`laidAt`, `explicitLinkProver`, `homeSim`), and no file restates them at
  the verifier's parameters.
- No file of this group imports this one.

Helper lemma.
  `reBound_self`: parameters whose field `coinBound` is reset to its own value are unchanged.


-/
import Johnson.Goal.Conditions.HomeAtWider
import Johnson.Goal.Description.Description

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.HomeTie
open VerifiableInference.OnPublicFiles (InnerCompilerInput)
open VerifierAndGoals (PublicFiles input_reBound)
open FlashProve (homeR flashProveDescription allZeroDigest)

theorem reBound_self (R : InnerCompilerInput) : R.reBound R.coinBound = R := rfl

theorem home_is_reBound (b : PublicFiles → ℕ) (Z : PublicFiles) :
    ∃ m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More,
      homeR b Z = ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z allZeroDigest m).reBound (b Z) :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∃ m : D.More, homeR b Z = (D.input Z allZeroDigest m).reBound (b Z))
    ⟨[], input_reBound flashProveDescription b Z allZeroDigest []⟩

theorem home_is_own (Z : PublicFiles) :
    ∃ (b : PublicFiles → ℕ) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More),
      homeR b Z = (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z allZeroDigest m :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∃ (b : PublicFiles → ℕ) (m : D.More), homeR b Z = D.input Z allZeroDigest m)
    ⟨fun Z' => (flashProveDescription.input Z' allZeroDigest []).coinBound, [],
      (input_reBound flashProveDescription (fun Z' => (flashProveDescription.input Z' allZeroDigest []).coinBound) Z allZeroDigest []).trans
        (reBound_self (flashProveDescription.input Z allZeroDigest []))⟩

end AtPublicFiles.HomeTie

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.HomeTie.reBound_self
#print axioms AtPublicFiles.HomeTie.home_is_reBound
#print axioms AtPublicFiles.HomeTie.home_is_own
