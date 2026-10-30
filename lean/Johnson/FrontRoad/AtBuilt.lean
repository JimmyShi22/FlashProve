-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/AtBuilt.lean: at the description that the release's goal statements use (atSecondHashFunction
theDescription), the inputs at all values c and m of the two public readings are one family over one
input. There is a family T whose input at d = (c, m) equals the description's input at (c, m), as a
whole, and whose public reading satisfies the four premises of Spec.frontPrivacy on it.
Terms and the limits that go with any quote: Spec.lean.

What this file proves.
  HasFamily D Z     There are c₀, m₀, a family T over D.input Z c₀ m₀ and a map pair of (c, m) onto
                    T.D such that T.at (pair c m) = D.input Z c m; the reading has no coins and
                    queries public strings only, none twice; and at every d every public string
                    codes a point of the spare oracle.
  at_input_star     the equation, for a description made by descriptionOfFields and the library's family
                    layoutsByPublicReadingAtDescriptionOfFields. By DescriptionDataAtFiles.at_layoutsByPublicReading (Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean); input_descriptionOfFields
                    (Johnson/Goal/Tie/DescribeT.lean) holds by unfolding.
  hasFamily_star, hasFamily_built, hasFamily_description   HasFamily at such a description; at
        descriptionOfDataOnBytes L for every L; at atSecondHashFunction theDescription, to which ofBuilt
        (Johnson/Goal/Description/Description.lean) transfers it.
  forall_at         If pair is onto and the equation holds, what holds at D.input Z c m for all c, m
                    holds at T.at d for all d.

Limits. An equation between terms of the library: nothing on soundness, completeness or hiding. The
family is under "there are". Its fields for an honest side are fillers of which nothing is required.
All limits of Spec.lean hold here too.

How it fits. VerifierAndGoals.verify queries the hash function for c and m and then calls the compiled
verifier at D.input Z c m, whose types, as defined, depend on (c, m). The steps of ZKCP/PublicRead/
and Johnson/PublicAt/ need a family of schemes with fixed types, which LayoutsByPublicReading
(Johnson/Top/InnerCompiledVerifierByPublicReading.lean) gives. For soundness the library needed only that the two
verifiers decide alike (fits_descriptionOfFields, Johnson/Flat/Told/Dec/LayoutsAtDescriptionOfFields.lean). A statement on honest sides
at D.input Z c m needs the inputs themselves to be equal. AtBuiltMore.lean uses at_input_star, and
AtHomeT.lean forall_at. No file uses HasFamily or its three theorems: the later files use FamilyLaws
(AtBuiltMore.lean), which has its clauses and three more.
-/
import Johnson.Flat.Told.Dec.LayoutsAtDescriptionOfFields
import Johnson.Goal.Description.Description

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace OnBytes.FrontRoad
open VerifierAndGoals FlashProve FlashProve VerifiableInference VerifiableInference.OnPublicFiles Rom
open TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop (Dig)

/-- There are c₀, m₀, a family T over D.input Z c₀ m₀ and a map pair onto T.D such that T.at (pair c
m) = D.input Z c m and the public reading satisfies the four premises of Spec.frontPrivacy
(Spec.lean) on it. -/
def HasFamily (D : Description) (Z : PublicFiles) : Prop :=
  ∃ (c₀ : Digest) (m₀ : D.More) (T : LayoutsByPublicReading (D.input Z c₀ m₀)) (pair : Digest → D.More → T.D),
    (∀ d, ∃ c m, d = pair c m) ∧ (∀ c m, T.at (pair c m) = D.input Z c m) ∧ T.Pub.NoCoin ∧
      (T.Pub.AsksIn fun _ s => T.Pt s) ∧ NoRepeat T.Pub ∧ ∀ d s, T.Pt s → IsOther (T.m d) s

section Star
variable (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (H : CommitterProverFormAndParser fun Z => (S Z).toDescriptionFields) (c₀ : Digest)
  (m₀ : List (Dig 256))

/-- For a description made by descriptionOfFields, the input of the library's family layoutsByPublicReadingAtDescriptionOfFields at (c, m) is
the description's input at (c, m). -/
theorem at_input_star (Z : PublicFiles) (c : Digest) (m : List (Dig 256)) :
    (layoutsByPublicReadingAtDescriptionOfFields S H c₀ m₀ Z).at (c, m) = (descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).input Z c m :=
  (S Z).at_layoutsByPublicReading c₀ m₀ (c, m)

end Star

/-- HasFamily holds at every description that descriptionOfFields makes of the frames of a family S of DescriptionDataAtFiles
and a side H over them. -/
theorem hasFamily_star (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (H : CommitterProverFormAndParser fun Z => (S Z).toDescriptionFields)
    (c₀ : Digest) (m₀ : List (Dig 256)) (Z : PublicFiles) :
    HasFamily (descriptionOfFields (fun Z => (S Z).toDescriptionFields) H) Z :=
  ⟨c₀, m₀, layoutsByPublicReadingAtDescriptionOfFields S H c₀ m₀ Z, Prod.mk, fun d => ⟨d.1, d.2, rfl⟩, at_input_star S H c₀ m₀ Z,
    layoutsByPublicReading_noCoin (S Z) c₀ m₀, layoutsByPublicReading_asks (S Z) c₀ m₀, layoutsByPublicReading_once (S Z) c₀ m₀,
    layoutsByPublicReading_spare (S Z) c₀ m₀⟩

/-- HasFamily holds at descriptionOfDataOnBytes L, for every L. -/
theorem hasFamily_built (L : DescriptionData) (Z : PublicFiles) : HasFamily (descriptionOfDataOnBytes L) Z :=
  hasFamily_star (dataAtFiles L) _ (fun _ => false) [] Z

/-- HasFamily holds at the description that the release's goal statements use, atSecondHashFunction
theDescription. -/
theorem hasFamily_description (Z : PublicFiles) : HasFamily (atSecondHashFunction theDescription) Z :=
  ofBuilt (Q := fun D => HasFamily D Z) (hasFamily_built flashProveData Z)

/-- If pair is onto and T.at (pair c m) = D.input Z c m, what holds at the description's input for
all c and m holds at the family's input for all d. -/
theorem forall_at {D : Description} {Z : PublicFiles} {c₀ : Digest} {m₀ : D.More}
    {T : LayoutsByPublicReading (D.input Z c₀ m₀)} {pair : Digest → D.More → T.D}
    (onto : ∀ d, ∃ c m, d = pair c m) (eq : ∀ c m, T.at (pair c m) = D.input Z c m)
    {Q : InnerCompilerInput → Prop} (h : ∀ c m, Q (D.input Z c m)) (d : T.D) : Q (T.at d) := by
  obtain ⟨c, m, rfl⟩ := onto d
  rw [eq c m]
  exact h c m

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.at_input_star
#print axioms OnBytes.FrontRoad.hasFamily_description
#print axioms OnBytes.FrontRoad.forall_at
