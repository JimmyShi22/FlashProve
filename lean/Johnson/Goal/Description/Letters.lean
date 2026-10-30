-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/Letters.lean: values for the letters of the theorems on the goal G8 at
`flashProveData`, so that each of their hypotheses can be written as a closed statement.
`thePhiO`: an index's weights where the matrix holds an index. `thePsi`: a total map to weights.
`theClaim`: the public files' table is lawful, the matrix holds an index, and the output meets the
table's policy at that index's weights. `theC0`, `theM0`: any: the digest of zeros; the empty list.
The error has no value here.

-/
import Johnson.Goal.Description.Description
import Johnson.PV.DescribeO

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open _root_.Iop (Dig)

def theC0 : Digest := fun _ => false

def theM0 : List (Dig 256) := []

def thePhiO (Z : PublicFiles) (s : IntegerTransformer.Settings) (valid : settingsAreValid s = true) :
    (dataAtFiles flashProveData Z).A.Mat → Option (ModelWeights s) := fun M => phiO valid M

def thePsi (Z : PublicFiles) (s : IntegerTransformer.Settings) (valid : settingsAreValid s = true) :
    (dataAtFiles flashProveData Z).A.Mat → ModelWeights s := fun M => phiAt valid M

def theClaim (Z : PublicFiles) : (dataAtFiles flashProveData Z).A.Mat → List Token → List Token → Prop := fun M prompt
    output =>
  ∃ lawful : Inst.Model.Lawful (ppAtFiles (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL),
    claimPolicyO (ppAtFiles (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL) lawful M prompt output

end FlashProve
