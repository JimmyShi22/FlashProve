-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/AnswersAre.lean: at the description's own object: the written committer's
out-of-domain (OOD) answers at a seed, spelled as a file spells them, are the answers of the
committer that runs, at the spelled seed: `AnswersAre Z` (Johnson/Bind/Cpp/Spells.lean), at every Z,
with no premise. No hash function is named.
Limits. Values in a field, at the full-size shape. No binding of the commitment (the opening form,
`BindsWith`, VerifiableInference/MoreStatements.lean), no correctness of extraction and no index
privacy is stated here. Nothing on any program.

-/
import Johnson.Bind.Cpp.AnswersObject
import Johnson.Bind.Cpp.Spells
import Johnson.Goal.Description.AtBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.Cpp
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice

/-- The typed pads are the coins' words, read in the field. -/
theorem riOf_pads (Z : PublicFiles) (x : Coins) :
    HEq (riOf Z x).1 (fun b j => toF (x.pad b.val j.val) : PadsOf frS 402653181) := HEq.rfl

/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8
  theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate theProofGate theLinkGate
  theProvers theNamed LPFD.Full.GF FlashProve.thePlan FlashProve.theItem
  Bind.Twin.answers OnBytes.K.IdTable.spellAns OnBytes.K.IdTable.spellSeedL

/-- **THE WRITTEN COMMITTER'S OOD ANSWERS, SPELLED, ARE THE RUNNING COMMITTER'S**, at every Z. -/
theorem answersAre (Z : PublicFiles) : AnswersAre Z := fun M x sd =>
  answersAre_of_eq (ppAtFiles (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL) (theCoding (asDescriptionFiles Z))
    (hE_the (asDescriptionFiles Z)) (flashProveDescription.F Z) (flashProveDescription.P Z) M (riOf Z x) sd x (riOf_pads Z x)

end Bind.Cpp

#print axioms Bind.Cpp.riOf_pads
#print axioms Bind.Cpp.answersAre
