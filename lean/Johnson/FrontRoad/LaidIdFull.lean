-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/LaidIdFull.lean: the statement of index privacy of the scheme laidId
(Johnson/FrontRoad/LaidIdSpec.lean) at the stored full-size public files, with no premise left, and
with two placeholder provers, which send fixed messages.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has.
idLaidFull: at the stored full-size public files storedPublicFiles (Ladder/Stored.lean), at one copy, 256
sampled bits in a leaf's salt, search limits of 2 ^ 40 (2 ^ 40 + 1 attempts), the picked enumeration
and up to 688127 requests, the scheme laidId has index privacy in the stronger form with the
simulator laidIdSim. With these placeholder provers the simulator's error is at most 2 ^ -135 (one
copy, one request, fewer than 2 ^ 64 hash queries). In the statement that is: for t + 1 ≤ 2 ^ 64. It
has no premise: that storedPublicFiles is in scope is the theorem VerifierAndGoals.filesRead
(Johnson/Goal/Files/FilesReadProof.lean).

  Spec.idLaidFull   the statement, as a proposition with a name.
  params_exist   the three types over which the statement quantifies without a premise, beside
      numbers and functions, have members at all public files: the type LeafBody of what a query's body
      may hold beside, the type of indices and the type of instances.
  weights_exist_full   at the settings that are read off storedPublicFiles there are model weights, so "at all
      weights" is not vacuous there (VerifierAndGoals.fixedFacts, Ladder/Ties.lean, which gives two sets of
      weights with different outputs).
  relTaken_one   the relation relTaken holds, at all weights, of the request with the prompt [0] and
      the output [1].

How it fits. A check that Spec.idLaidNumber is not vacuous at the stored full-size public files. One
copy, 256 sampled bits and search limits of 2 ^ 40 are this statement's choice, tied to no program.
Not one of the release's goal statements.

Limits. Those of Johnson/FrontRoad/LaidIdSpec.lean: above all, two of the scheme's three provers are
placeholder provers, which send fixed messages, there is no completeness, and the settings s are a
variable (for the files' own settings see Spec.idLaidOwn, Johnson/FrontRoad/LaidBesideSpec.lean).
The request of relTaken_one is in the relation, but its output need not be the model's. storedPublicFiles is the
term of Ladder/Stored.lean; that its bytes are those of the package's example folder is not said.
-/
import Johnson.FrontRoad.LaidId
import Johnson.Goal.Files.FilesReadProof
import Ladder.Ties

set_option autoImplicit false
set_option maxRecDepth 100000

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open AtPublicFiles.ZetaAt AtPublicFiles.LinkLaid VerifiableInference VerifiableInference.OnPublicFiles
open VerifierAndGoals (PublicFiles InScope storedPublicFiles)
open FlashProve (homeR flashProveDescription fillB allZeroDigest)

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem
  FlashProve.riDigits FlashProve.fieldRows VerifierAndGoals.storedPublicFiles

/-- Statement only; proved as idLaidFull below. Spec.idLaidNumber at the stored full-size public
files and up to 688127 requests, with no premise. -/
def Spec.idLaidFull : Prop :=
  ∀ (b : PublicFiles → ℕ) (b₀ : (homeR b storedPublicFiles).LeafBody) (ℓr : ℕ) (i₀ : (homeR b storedPublicFiles).Index)
    (s : IntegerTransformer.Settings) (x₀ : (homeR b storedPublicFiles).Instance) (Form : Type)
    (parse : VerifierAndGoals.Parser (flashProveDescription.reBound b) storedPublicFiles Form)
    (encF : VerifierAndGoals.TypedProof ((flashProveDescription.reBound b).F storedPublicFiles) ((flashProveDescription.reBound b).P storedPublicFiles) → Form),
    ZKCP.HasStrongIndexPrivacyWith (relTaken s)
        (laidId b storedPublicFiles b₀ 0 256 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
          (pickBits b storedPublicFiles b₀ 0 256 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) fun _ => 2 ^ 40) s x₀
          Form parse encF)
        (laidIdSim b storedPublicFiles b₀ 0 688127 256 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
          (pickBits b storedPublicFiles b₀ 0 256 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) fun _ => 2 ^ 40) i₀ x₀
          Form encF)
        (fun t N => upTo 688127 (boundZ (9 + 2 ^ 40 + 2 ^ 40 + 2 ^ 40) 0) (t + 1) N) ∧
      ∀ t, t + 1 ≤ 2 ^ 64 →
        upTo 688127 (boundZ (9 + 2 ^ 40 + 2 ^ 40 + 2 ^ 40) 0) (t + 1) 1 ≤ (2⁻¹ : ℝ≥0∞) ^ 135

/-- **At the stored full-size public files, with no premise**, and with two placeholder provers,
which send fixed messages. Proves Spec.idLaidFull. -/
theorem idLaidFull : Spec.idLaidFull :=
  fun b b₀ ℓr i₀ s x₀ Form parse encF =>
    have h := idLaidNumber b storedPublicFiles b₀ 688127 ℓr i₀ s x₀ Form parse encF VerifierAndGoals.filesRead.full.1
      le_rfl
    ⟨h.1, h.2 (by norm_num)⟩

/-- relTaken holds, at all weights, of the request with the prompt [0] and the output [1]. -/
theorem relTaken_one (s : IntegerTransformer.Settings) (w : ModelWeights s) :
    (relTaken s).rel w ([0], [1]) () :=
  relTaken_some s w [⟨0, by decide⟩] [⟨1, by decide⟩] Nat.one_pos Nat.one_pos (by decide)

/-- The type LeafBody of what a query's body may hold beside, the type of indices and the type of
instances have members, at all public files. -/
theorem params_exist (b : PublicFiles → ℕ) (Z : PublicFiles) :
    Nonempty (homeR b Z).LeafBody ∧ Nonempty (homeR b Z).Index ∧ Nonempty (homeR b Z).Instance :=
  ⟨⟨fillB b Z⟩,
    ⟨(Flat.matrixOf (Cm.Idx.ofIndex Inst.Model.ScalesSanity.iZero) : (flashProveDescription.input Z allZeroDigest []).Index)⟩, by
    obtain ⟨x, -⟩ := Flat.buildReq_total [⟨0, by decide⟩] [⟨1, by decide⟩] [] Nat.one_pos
      Nat.one_pos (by decide)
    exact ⟨x⟩⟩

/-- At the settings that are read off the stored full-size public files there are model weights. -/
theorem weights_exist_full :
    ∃ pp, VerifierAndGoals.readFiles storedPublicFiles = .ok pp ∧ Nonempty (ModelWeights (VerifierAndGoals.settingsOfRead pp)) := by
  obtain ⟨-, pp, hr, -⟩ := VerifierAndGoals.filesRead.full
  obtain ⟨w, -⟩ := VerifierAndGoals.fixedFacts.claim storedPublicFiles pp (Or.inl rfl) hr
  exact ⟨pp, hr, ⟨w⟩⟩

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.idLaidFull
#print axioms OnBytes.FrontRoad.relTaken_one
#print axioms OnBytes.FrontRoad.params_exist
#print axioms OnBytes.FrontRoad.weights_exist_full
