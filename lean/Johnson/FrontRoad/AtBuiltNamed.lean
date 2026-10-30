-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/AtBuiltNamed.lean: the family of inputs at the built description, by name:
FamilyLaws (AtBuiltMore.lean) holds at an explicit family, over the input at explicit values c₀, m₀.
Terms and the limits that go with any quote: Spec.lean.

What this file proves.
  layoutsOfBuiltDescription L c₀ m₀ Z  the library's family layoutsByPublicReadingAtDescriptionOfFields (Johnson/Flat/Told/Dec/LayoutsAtDescriptionOfFields.lean) at the
                      parameters of descriptionOfDataOnBytes L.
  familyLaws_built    FamilyLaws (descriptionOfDataOnBytes L) Z c₀ m₀ (layoutsOfBuiltDescription L c₀ m₀ Z) Prod.mk, for every L.
  familyLaws_the      the same at L := flashProveData, c₀ := allZeroDigest (the all-zero digest) and m₀ := [].

Limits. Those of AtBuilt.lean: nothing on soundness, completeness or hiding is said here.
familyLaws_the is at the built description descriptionOfDataOnBytes flashProveData. That this is the description that the
release's goal statements use (atSecondHashFunction theDescription) is a theorem, not an unfolding
(theDescription_eq, Johnson/Goal/Description/Description.lean): a whole statement is transferred
there by ofBuilt.

How it fits. hasFamilyLaws_description (AtBuiltMore.lean) has c₀, m₀ and the family under "there
are". The library's map from weights to indices (backThe, Johnson/Goal/Conditions/BindsAtThe.lean)
has its values in the index type of the built description's input at (allZeroDigest, []). A statement that
names that map needs the family named over that very input. AtWeights.lean, Joined.lean and
AtHomeT.lean use familyLaws_the.
-/
import Johnson.FrontRoad.AtBuiltMore
import Johnson.Goal.Conditions.BindsAtThe

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace OnBytes.FrontRoad
open VerifierAndGoals FlashProve FlashProve VerifiableInference VerifiableInference.OnPublicFiles Rom
open _root_.Iop (Dig)

/-- The library's family layoutsByPublicReadingAtDescriptionOfFields at the parameters of descriptionOfDataOnBytes L. -/
def layoutsOfBuiltDescription (L : DescriptionData) (c₀ : Digest) (m₀ : List (Dig 256)) (Z : PublicFiles) :
    LayoutsByPublicReading ((descriptionOfDataOnBytes L).input Z c₀ m₀) :=
  layoutsByPublicReadingAtDescriptionOfFields (dataAtFiles L) (committerAndProverWithParser (dataAtFiles L) L.honest decodeD L.f₀) c₀ m₀ Z

/-- FamilyLaws holds at descriptionOfDataOnBytes L, for every L, and the family layoutsOfBuiltDescription. -/
theorem familyLaws_built (L : DescriptionData) (c₀ : Digest) (m₀ : List (Dig 256)) (Z : PublicFiles) :
    FamilyLaws (descriptionOfDataOnBytes L) Z c₀ m₀ (layoutsOfBuiltDescription L c₀ m₀ Z) Prod.mk :=
  familyLaws_star (dataAtFiles L) (committerAndProverWithParser (dataAtFiles L) L.honest decodeD L.f₀) c₀ m₀ Z

/-- FamilyLaws holds at descriptionOfDataOnBytes flashProveData, allZeroDigest and [], at the family layoutsOfBuiltDescription: over the input
whose index type holds the values of the library's map from weights (backThe). -/
theorem familyLaws_the (Z : PublicFiles) :
    FamilyLaws (descriptionOfDataOnBytes flashProveData) Z allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] Z) Prod.mk :=
  familyLaws_built flashProveData allZeroDigest [] Z

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.familyLaws_built
#print axioms OnBytes.FrontRoad.familyLaws_the
