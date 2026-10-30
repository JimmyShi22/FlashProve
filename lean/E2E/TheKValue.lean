-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TheKValue.lean: THE K OF RECORD: the thirteen entries and the later chains' rows.

Limits. A definition. This file proves nothing about completeness, soundness or zero knowledge.
-/
import E2E.TheThirteenOfRecord
import AtFullSide.M1.KRecord

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.TheSides
open ProofFile.Honest.Term (baseFilling)

/-- **The K of record**, at a return of the base filling, under the head. -/
def theKOfRecord {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (A₀ : ProofFile.Honest.OnlineProverWithDescription AtPublicFiles.AtFiles.FullSizeMatrix ProofFile.Honest.IndexCommitterCoins ProofFile.Honest.Cells Unit Unit)
    (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ A₀.Z Np cF x₀) :
    KindRows (baseFilling files) A₀.Z A₀.G :=
  theK (theThirteen files A₀.Z A₀.G) (theThirteen_apart files A₀.Z A₀.G)
    (AtFullSide.M1.laterOurs A₀ h)

end AtPublicFiles.TheSides

#print axioms AtPublicFiles.TheSides.theKOfRecord
