-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/WithSampler.lean: THE DESCRIPTION theCpp (Johnson/Bind/Cpp/Defs.lean) WITH ANY
SAMPLER OF THE COMMITTER's RANDOMNESS, and the two types of coins side by side. Definitions, and
theorems by calls: NO STATEMENT OF Johnson/Bind/Cpp/OfTie.lean ON BINDING OR ON SOUNDNESS READS THE
SAMPLER.
NOTHING HERE SAYS THAT A COMMITMENT OF THE RELEASE'S COMMITTING PROGRAM CAN BE OPENED ONLY TO THE
EXTRACTOR'S WEIGHTS, OR THAT THE EXTRACTOR GIVES THE WEIGHTS THAT THE PROGRAM COMMITTED TO.
"Binding" in this file is the opening form, BindsWith (VerifiableInference/MoreStatements.lean):
nobody opens a commitment, by naming weights and randomness from which the committer gives it, to
weights that the extractor does not give; at fixed randomness it yields that the extractor gives the
committed weights back (BindsWith.atRandomness). It is not the index binding of ZKCP/Defs.lean's
HasIndexBinding: the half on soundness has that form, for the claim "meets the policy" (the tie is
typed at exact match: sound_iff, VerifiableInference/Agreement.lean), and speaks of every
commitment, whoever made it.

Why. theCpp's sampler draws a seed. Completeness and index privacy may want a sampler that draws the
coins themselves. Defs.lean does not turn: the wider description stands beside it.

Main names (namespace Bind.Cpp).
  cppSideWith smp T prove, theCppWith smp T prove: the honest side and the description with the
    sampler smp. seedSampler: the sampler of theCpp. **theCpp_eq**: theCpp T prove is
    theCppWith seedSampler T prove, by definition.
  commit_isWith, cppWith_is_of_verify, g8bits_cppWith: as in OfTie.lean.
  **bindsWith_of_tieAtWith**, **bindsAtZ_cppWith**: binding at one Z, from the tie and the count.
  toTwin, ofTwin: the maps between Bind.Cpp.Coins and Bind.Twin.Coins, field for field, each the
    other's inverse by definition.
Limits. Those of OfTie.lean. Nothing is said of any sampler's distribution. Nothing on index
privacy. THE ONE DESCRIPTION THAT A PAGE NAMES IS theCpp: theCppWith stands beside it for whoever
writes a prover.
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.OfTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

open scoped ENNReal

noncomputable section

namespace Bind.Cpp
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open Bind.Twin (Shape Table)

/-- The honest side with any sampler. -/
def cppSideWith (smp : RandomizedAlgorithm Rand) (T : Letters)
    (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm flashProveDescription.Form) : HonestSide flashProveDescription.Form :=
  { cppSide T prove with sample := smp }

/-- The description with any sampler. -/
def theCppWith (smp : RandomizedAlgorithm Rand) (T : Letters)
    (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm flashProveDescription.Form) : SecondHashFunctionType → Description :=
  fun _ => flashProveDescription.withHonest (cppSideWith smp T prove)

/-- The sampler of theCpp: a seed, uniformly; it asks the hash function nothing. -/
def seedSampler : RandomizedAlgorithm Rand := .sample (2 ^ 256 - 1) fun t => .done (.inl t)

variable (smp : RandomizedAlgorithm Rand) (T : Letters)
  (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm flashProveDescription.Form)

/-- **theCpp is theCppWith at the seed's sampler.** -/
theorem theCpp_eq : theCpp T prove = theCppWith seedSampler T prove := rfl

theorem commit_isWith (o : SecondHashFunctionType) (Z : PublicFiles) (s : IntegerTransformer.Settings) (w : ModelWeights s)
    (ρ : Rand) :
    (theCppWith smp T prove o).commit Z s w ρ = T.commitAt shapeFull Z (entryOf s w) ρ := rfl

/-! ## The two types of coins -/

/-- To the running committer's own type of coins. -/
def toTwin (x : Coins) : Bind.Twin.Coins := ⟨x.tail, x.pad, x.salt⟩

/-- And back. -/
def ofTwin (x : Bind.Twin.Coins) : Coins := ⟨x.tail, x.pad, x.salt⟩

theorem ofTwin_toTwin (x : Coins) : ofTwin (toTwin x) = x := rfl

theorem toTwin_ofTwin (x : Bind.Twin.Coins) : toTwin (ofTwin x) = x := rfl

/- From here on Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF riDigits fieldRows descriptionOfDataOnBytes T₀
  FlashProve.thePlan FlashProve.theItem LayoutsByPublicReading.commitAtCoins

/-- It has the verifier and the extractor of the description of the theorem on soundness. -/
theorem cppWith_is_of_verify (o : SecondHashFunctionType) :
    atSecondHashFunction theDescription = flashProveDescription ∧
      (∀ (Z : PublicFiles) (Form : Type) (parse : Parser flashProveDescription Z Form),
        verify (theCppWith smp T prove o) Z parse = verify flashProveDescription Z parse) ∧
      (theCppWith smp T prove o).extractor = (atSecondHashFunction theDescription).extractor :=
  ⟨VerifierAndGoals.AtTheName.the_description_is, fun _ _ _ => rfl,
    VerifierAndGoals.AtTheName.the_description_is ▸ rfl⟩

/-- G8bits: no hypothesis, at every sampler. -/
theorem g8bits_cppWith : G8bits (theCppWith smp T prove) := by
  have h := VerifierAndGoals.AtTheName.g8bits_of_verify
  unfold G8bits at h
  rw [VerifierAndGoals.AtTheName.the_description_is] at h
  exact ⟨verifierWithin_withHonest (cppSideWith smp T prove) h.1,
    soundUnderPolicyAt_withHonest (cppSideWith smp T prove) soundnessErrorInQueries h.2⟩

/-- **Binding at one Z, from the tie there, at the square form, at every sampler.** -/
theorem bindsWith_of_tieAtWith (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (tie : TieAt T Z) :
    BindsWith (systemOfRecord (atSecondHashFunction (theCppWith smp T prove)) Z (settingsOfRead pp))
      ((atSecondHashFunction (theCppWith smp T prove)).extractor Z (settingsOfRead pp))
      fun t => epsBind honestBudget (t + 2) := by
  have h0 := bindsWith_plain_law Z pp hr (placeHolderNumberCoins.b₀ Z)
    (.done (coins₀_nonempty Z).some)
    (fun w _ p o => prove Z (settingsOfRead pp) w (.inl 0) p o)
  have h1 := BindsWith.ofCommit _
    (systemOfRecord (atSecondHashFunction (theCppWith smp T prove)) Z (settingsOfRead pp))
    _ _ h0 some id (coinsAlg T Z) 2 (coinsAlg_within T Z) (fun _ => rfl)
    (fun w ρ hash => by
      cases ρ with
      | inl seed => exact (tie (settingsOfRead pp) w _ _ hash).symm
      | inr x => exact (tie (settingsOfRead pp) w x _ hash).symm)
  exact (extractor_fold Z (settingsOfRead pp)) ▸ h1

/-- **The body of G9bits at one Z, at every sampler.** -/
theorem bindsAtZ_cppWith (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (tie : TieAt T Z) (cnt : CountAt T Z) :
    (∀ w ρ, ((atSecondHashFunction (theCppWith smp T prove)).commit Z (settingsOfRead pp) w
        ρ).toRandomized.QueryBound honestBudget) ∧
      BindsWith (systemOfRecord (atSecondHashFunction (theCppWith smp T prove)) Z (settingsOfRead pp))
        ((atSecondHashFunction (theCppWith smp T prove)).extractor Z (settingsOfRead pp)) bindingErrorInQueries :=
  ⟨fun w ρ => commit_within T Z cnt (settingsOfRead pp) w ρ,
    bindsWith_bits_of_square 2 (by norm_num) (bindsWith_of_tieAtWith smp T prove Z pp hr tie)⟩

end Bind.Cpp

end

#print axioms Bind.Cpp.theCpp_eq
#print axioms Bind.Cpp.commit_isWith
#print axioms Bind.Cpp.ofTwin_toTwin
#print axioms Bind.Cpp.toTwin_ofTwin
#print axioms Bind.Cpp.cppWith_is_of_verify
#print axioms Bind.Cpp.g8bits_cppWith
#print axioms Bind.Cpp.bindsWith_of_tieAtWith
#print axioms Bind.Cpp.bindsAtZ_cppWith
