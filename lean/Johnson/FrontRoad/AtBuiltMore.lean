-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/AtBuiltMore.lean: the family of inputs at the description that the release's goal
statements use (atSecondHashFunction theDescription), with all that the steps of this folder require of a family
and its public reading.
Terms and the limits that go with any quote: Spec.lean.

What this file proves. AtBuilt.lean has the family with the equation of inputs and the four premises
on the reading. Completeness and the count of queries at the shell frontAt (Complete.lean,
Within.lean) require three things more.
  FamilyLaws D Z c₀ m₀ T pair   all of it, as one structure:
      onto, eq        pair is onto; T.at (pair c m) = D.input Z c m, as a whole.
      noCoin, asks, once, spare   the four premises on the reading.
      reads           what VerifierAndGoals.verify reads off a hash function, paired, is the value of the
                      family's reading at that function.
      total           every key with a told part has a code.
      eight           the reading makes at most eight queries.
  familyLaws_star     FamilyLaws for a description made by descriptionOfFields and the library's family
                      layoutsByPublicReadingAtDescriptionOfFields.
  HasFamilyLaws, hasFamilyLaws_description   "there are c₀, m₀, T, pair with FamilyLaws"; it holds
        at atSecondHashFunction theDescription, at every Z.
That the two verifiers decide alike follows from eq (fits_of_eq, FitsOf.lean).

Limits. Those of AtBuilt.lean: nothing on soundness, completeness or hiding is said here. No bound
on the blocks of a typed answer under the coding at d is proved here; it is proved in Blocks.lean
(blocks_le).

Notes. eq is at_input_star (AtBuilt.lean), and onto holds by unfolding. The other fields are lemmas
of Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean (told_...T) and Johnson/Flat/Told/Dec/LayoutsAtDescriptionOfFields.lean (reads_descriptionOfFields),
and pub8_queries (Johnson/Top/KeyTree.lean).
-/
import Johnson.FrontRoad.AtBuilt
import Johnson.Top.KeyTree

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace OnBytes.FrontRoad
open VerifierAndGoals FlashProve FlashProve VerifiableInference VerifiableInference.OnPublicFiles Rom
open TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop (Dig)

/-- All that the steps of this folder require of a family T over D.input Z c₀ m₀, its map pair and
its public reading. The head says what each field is. -/
structure FamilyLaws (D : Description) (Z : PublicFiles) (c₀ : Digest) (m₀ : D.More)
    (T : LayoutsByPublicReading (D.input Z c₀ m₀)) (pair : Digest → D.More → T.D) : Prop where
  onto : ∀ d, ∃ c m, d = pair c m
  eq : ∀ c m, T.at (pair c m) = D.input Z c m
  noCoin : T.Pub.NoCoin
  asks : T.Pub.AsksIn fun _ s => T.Pt s
  once : NoRepeat T.Pub
  spare : ∀ d s, T.Pt s → IsOther (T.m d) s
  reads : ∀ hash : Hash,
    (VerifierAndGoals.Fit.readBoth D Z c₀ m₀ T pair).evaluate hash = T.Pub.det fun _ => hash
  total : ∀ ck, ∃ code, T.encT ck = some code
  eight : T.Pub.QueryBound 8

/-- FamilyLaws holds for a description made by descriptionOfFields, at the library's family layoutsByPublicReadingAtDescriptionOfFields and
pair := Prod.mk. -/
theorem familyLaws_star (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (H : CommitterProverFormAndParser fun Z => (S Z).toDescriptionFields)
    (c₀ : Digest) (m₀ : List (Dig 256)) (Z : PublicFiles) :
    FamilyLaws (descriptionOfFields (fun Z => (S Z).toDescriptionFields) H) Z c₀ m₀ (layoutsByPublicReadingAtDescriptionOfFields S H c₀ m₀ Z) Prod.mk where
  onto := fun d => ⟨d.1, d.2, rfl⟩
  eq := at_input_star S H c₀ m₀ Z
  noCoin := layoutsByPublicReading_noCoin (S Z) c₀ m₀
  asks := layoutsByPublicReading_asks (S Z) c₀ m₀
  once := layoutsByPublicReading_once (S Z) c₀ m₀
  spare := layoutsByPublicReading_spare (S Z) c₀ m₀
  reads := reads_descriptionOfFields S H c₀ m₀ Z
  total := fun ck => Option.ne_none_iff_exists'.1 (layoutsByPublicReading_total (S Z) c₀ m₀ ck)
  eight := pub8_queries _ _ _ _

/-- There are c₀, m₀, a family T and a map pair with FamilyLaws. -/
def HasFamilyLaws (D : Description) (Z : PublicFiles) : Prop :=
  ∃ (c₀ : Digest) (m₀ : D.More) (T : LayoutsByPublicReading (D.input Z c₀ m₀)) (pair : Digest → D.More → T.D),
    FamilyLaws D Z c₀ m₀ T pair

/-- HasFamilyLaws holds at the description that the release's goal statements use, atSecondHashFunction
theDescription, at every Z. -/
theorem hasFamilyLaws_description (Z : PublicFiles) : HasFamilyLaws (atSecondHashFunction theDescription) Z :=
  ofBuilt (Q := fun D => HasFamilyLaws D Z)
    ⟨fun _ => false, [], _, _, familyLaws_star (dataAtFiles flashProveData) _ (fun _ => false) [] Z⟩

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.familyLaws_star
#print axioms OnBytes.FrontRoad.hasFamilyLaws_description
