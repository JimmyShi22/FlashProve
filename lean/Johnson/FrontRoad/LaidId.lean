-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/LaidId.lean: proofs of the two statements of Johnson/FrontRoad/LaidIdSpec.lean on
index privacy of the scheme laidId, whose key is the 256-bit commitment ID alone and which has two
placeholder provers, which send fixed messages; and what else is proved of that scheme.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has.
idLaid proves Spec.idLaid, and idLaidNumber proves Spec.idLaidNumber. What the two statements say,
and their limits, is in the head of Johnson/FrontRoad/LaidIdSpec.lean.

  threeOfId_laid   the three clauses of ThreeOfId (Johnson/FrontRoad/IdAlone.lean) hold of the
      scheme: what its verifier is, bounds on the honest side's calls of the hash function, and
      index privacy. idLaid is its third clause.
  laidId_V   the verifier of laidId is the verifier of the argument system that Ladder.lean builds
      from the built description flashProveDescription, as a function of commitment, request and form. It holds by
      definition.
  laidId_reads_as_verify   laidId's committer first runs the public reading of the family homeT b Z
      and then commits at the input at the value that was read; under every hash function that value
      is the value of the two public readings of VerifierAndGoals.verify; and the input there is the input at
      which VerifierAndGoals.verify calls the compiled verifier. (The statement names VerifierAndGoals.Fit.readBoth and
      D.input; that these are the readings and the input in the text of VerifierAndGoals.verify is by reading;
      no equation with it is stated here; verify_iff (Johnson/FrontRoad/Shell.lean) names it.)
  laidId_within   the committer makes at most 8 + commitN · (K + 1) + 1 calls of the hash function
      on every path and the prover at most proveN · (K + 1), where commitN and proveN are the counts
      of typed queries of Johnson/WholeKey/Work.lean and K is the number of digests in a round's
      answer.
  tie_taken   every request that relTaken calls true builds an instance at homeR b Z, with no
      further tokens, from which backTok reads the request back (build_home,
      Johnson/Prover/At/HomeMore.lean; buildReq_reads, Johnson/Flat/BuiltOK.lean).
  relTaken_some   relTaken is not empty: for every non-empty prompt and output of tokens of the
      vocabulary, of at most ppref.T + 1 tokens together, it holds at all weights (buildReq_total).
  pickBits_ok   the picked enumeration lists each value once.

How it fits. See Johnson/FrontRoad/LaidIdSpec.lean. Not one of the release's goal statements.

Limits. Those of Johnson/FrontRoad/LaidIdSpec.lean. The counts commitN and proveN are not evaluated
to numbers here.
-/
import Johnson.FrontRoad.LaidIdSpec
import Johnson.FrontRoad.LaidAll
import Johnson.FrontRoad.AtHomeT

set_option autoImplicit false
set_option maxRecDepth 100000

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Premises AtPublicFiles.ZetaAt AtPublicFiles.LinkLaid
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.LinkSim.AtHome
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifierAndGoals (PublicFiles InScope)
open FlashProve (flashProveData homeR homeT backB flashProveDescription allZeroDigest build_home)

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem
  FlashProve.riDigits FlashProve.fieldRows

/-- relTaken is not empty: it holds, at all weights, of every non-empty prompt and output of tokens
of the vocabulary with at most ppref.T + 1 tokens together. -/
theorem relTaken_some (s : IntegerTransformer.Settings) (w : ModelWeights s)
    (prompt output : List IntegerModel.Token) (h1 : 0 < prompt.length) (h2 : 0 < output.length)
    (h3 : prompt.length + output.length ≤ Inst.Model.ppref.T + 1) :
    (relTaken s).rel w (prompt.map Fin.val, output.map Fin.val) () :=
  Flat.buildReq_total prompt output [] h1 h2 h3

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- Every request that relTaken calls true builds an instance at homeR b Z, with no further tokens,
from which backTok reads the request back. -/
theorem tie_taken (s : IntegerTransformer.Settings) (w : ModelWeights s)
    (x' : List Token × List Token) (h : (relTaken s).rel w x' ()) :
    ∃ x, (homeR b Z).buildInstance x' [] = some x ∧ True ∧ backTok b Z x = x' := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, (congrFun (congrFun (build_home b Z) x') []).trans hx, trivial, Flat.buildReq_reads hx⟩

variable (b₀ : (homeR b Z).LeafBody) (M s1 ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)

/-- The picked enumeration lists each value once. -/
theorem pickBits_ok : (pickBits b Z b₀ M ℓ ℓr capT capL capB).OK :=
  Classical.choose_spec (runBits_listed _ _ _ _ _ _ _ _)

variable (E : BitsE b Z b₀ M ℓ ℓr capT capL capB) (i₀ : (homeR b Z).Index)
  (s : IntegerTransformer.Settings) (x₀ : (homeR b Z).Instance) (Form : Type)
  (parse : VerifierAndGoals.Parser (flashProveDescription.reBound b) Z Form)
  (encF : VerifierAndGoals.TypedProof ((flashProveDescription.reBound b).F Z) ((flashProveDescription.reBound b).P Z) → Form)

/-- **The three clauses hold of the scheme**, for all public files in scope. -/
theorem threeOfId_laid (scope : InScope Z = true) (hE : E.OK) (hM : M + 1 ≤ 710324)
    (hs : s1 ≤ 688127) (hℓ : 256 ≤ ℓ) (hℓ' : ℓ ≤ (homeR b Z).compilerParameters.sMT) (CT CL CB : ℕ)
    (hT : ∀ i, capT i ≤ CT) (hL : ∀ i, capL i ≤ CL) (hB : ∀ i, capB i ≤ CB) :
    ThreeOfId (flashProveDescription.reBound b) Z allZeroDigest [] (homeT b Z)
      (laidSides b Z b₀ M s1 ℓ ℓr capT capL capB E i₀) s (backB b Z s) x₀ (backTok b Z) Form parse
      encF (relTaken s)
      (8 + commitN (homeR b Z).queryLayout (laidAt b Z b₀ M ℓ ℓr capT capL capB E).side *
        ((homeR b Z).queryLayout.K + 1) + 1)
      (proveN (homeR b Z).queryLayout (laidAt b Z b₀ M ℓ ℓr capT capL capB E).side * ((homeR b Z).queryLayout.K + 1))
      (upTo s1 (boundZ (9 + CT + CL + CB) M)) :=
  threeOfId_of_laws (flashProveDescription.reBound b) Z allZeroDigest [] (homeT b Z)
    (laidSides b Z b₀ M s1 ℓ ℓr capT capL capB E i₀) s (backB b Z s) x₀ (backTok b Z) Form parse
    encF (relTaken s) Prod.mk (familyLaws_home b Z) (fun _ _ => True) (fun _ => True)
    (upTo s1 (boundZ (9 + CT + CL + CB) M)) _ _
    (premAll_laid b Z b₀ M s1 ℓ ℓr capT capL capB E i₀ scope hM hs hℓ' hE fun _ _ => True)
    (zetaLe_laid b Z b₀ M s1 ℓ ℓr capT capL capB E i₀ scope CT CL CB hℓ hT hL hB)
    (fun _ => trivial) (tie_taken b Z s) (fun _ => le_rfl) fun _ => le_rfl

/-- The verifier of laidId is the verifier of the argument system that Ladder.lean builds from the
built description, by definition. -/
theorem laidId_V
    (prove : ModelWeights s → flashProveDescription.Rand → List Token → List Token → RandomizedAlgorithm Form) :
    (laidId b Z b₀ M ℓ ℓr capT capL capB E s x₀ Form parse encF).V =
      (VerifierAndGoals.system flashProveDescription Z s Form prove parse).uploadArgument.V := rfl

/-- **laidId reads the public digests as the verifier of Ladder.lean does.** Three clauses. Its
committer first runs the public reading of the family homeT b Z and then, at the value d that was
read, the committer of the scheme with the whole key at the input (homeT b Z).at d, over the one
hash function; the told part, the commitment ID and the re-packing follow. Under every hash function
that reading has the value of the two public readings of VerifierAndGoals.verify (readConfig, then readMore).
And the family's input at a pair (c, m) is the input at which VerifierAndGoals.verify calls the compiled
verifier when it has read c and m. The statement names VerifierAndGoals.Fit.readBoth and D.input, which are
the two readings and the input in the text of VerifierAndGoals.verify; no equation with VerifierAndGoals.verify itself
is stated here (verify_iff, Johnson/FrontRoad/Shell.lean, is the theorem that names it). -/
theorem laidId_reads_as_verify :
    (∀ w, (laidId b Z b₀ M ℓ ℓr capT capL capB E s x₀ Form parse encF).C w =
      (Rom.ofRom ((homeT b Z).Pub.bind fun d =>
        ((((wholeKeySchemeOverTypedOracles ((homeT b Z).at d) (laidAt b Z b₀ M ℓ ℓr capT capL capB E).side).C
          (backB b Z s w)).overOne ((homeT b Z).m d)).bind fun k =>
            Rom.OComp.pure (((homeT b Z).part d, k.1), k.2)).bind fun k =>
              Rom.OComp.pure (k.1, (d, k.2)))).bind fun keys =>
        (ZKCP.keyDigest (fun ck : KeyT (homeR b Z) => (homeT b Z).encT (ck.1, lowKey ck.2))
          keys.1).mapO fun dg => (dg, (keys.1.2, keys.2))) ∧
      (∀ hash : Hash, (VerifierAndGoals.Fit.readBoth (flashProveDescription.reBound b) Z allZeroDigest [] (homeT b Z) Prod.mk).evaluate
        hash = (homeT b Z).Pub.det fun _ => hash) ∧
      ∀ c m, (homeT b Z).at (c, m) = (flashProveDescription.reBound b).input Z c m :=
  ⟨fun _ => rfl, (familyLaws_home b Z).reads, (familyLaws_home b Z).eq⟩

/-- Bounds on the honest side's calls of the hash function, on every path. -/
theorem laidId_within (scope : InScope Z = true) (hE : E.OK) (hM : M + 1 ≤ 710324)
    (hℓ' : ℓ ≤ (homeR b Z).compilerParameters.sMT) :
    (∀ w, ((laidId b Z b₀ M ℓ ℓr capT capL capB E s x₀ Form parse encF).C w).QueryBound
        (8 + commitN (homeR b Z).queryLayout (laidAt b Z b₀ M ℓ ℓr capT capL capB E).side *
          ((homeR b Z).queryLayout.K + 1) + 1)) ∧
      ∀ isk x', ((laidId b Z b₀ M ℓ ℓr capT capL capB E s x₀ Form parse encF).P isk x'
        ()).QueryBound
          (proveN (homeR b Z).queryLayout (laidAt b Z b₀ M ℓ ℓr capT capL capB E).side *
            ((homeR b Z).queryLayout.K + 1)) := by
  unfold laidId frontId
  exact ⟨queryBound_frontKC (homeT b Z) (fun _ => (laidAt b Z b₀ M ℓ ℓr capT capL capB E).side)
      (backB b Z s) x₀ _ _ _ 8 ((homeR b Z).queryLayout.K + 1) _ (familyLaws_home b Z).eight
      (fun d o => blocks_le ((homeT b Z).m d) (by norm_num) o) fun d i =>
      work_commitW (AtPublicFiles.LinkLaid.Told.premW_laid_told b Z d b₀ M 0 ℓ ℓr capT capL capB E scope hM
        (Nat.zero_le _) hℓ' hE fun _ _ => True) i,
    queryBound_frontKP (homeT b Z) (fun _ => (laidAt b Z b₀ M ℓ ℓr capT capL capB E).side)
      (backB b Z s) x₀ _ _ _ ((homeR b Z).queryLayout.K + 1) _
      (fun d o => blocks_le ((homeT b Z).m d) (by norm_num) o) fun d isk l =>
      work_proveW (AtPublicFiles.LinkLaid.Told.premW_laid_told b Z d b₀ M 0 ℓ ℓr capT capL capB E scope hM
        (Nat.zero_le _) hℓ' hE fun _ _ => True) (homeR b Z).fixedSample isk l⟩

end OnBytes.FrontRoad

namespace OnBytes.FrontRoad
open AtPublicFiles.ZetaAt AtPublicFiles.LinkLaid

/-- **Index privacy of the scheme whose key is the commitment ID alone**, at the honest side whose
link prover is the explicit one and whose other two provers are placeholder provers, which send
fixed messages. Proves Spec.idLaid. -/
theorem idLaid : Spec.idLaid :=
  fun b Z b₀ M s1 ℓ ℓr CT CL CB capT capL capB E i₀ s x₀ Form parse encF scope hE hM hs hℓ hℓ' hT
      hL hB =>
    (threeOfId_laid b Z b₀ M s1 ℓ ℓr capT capL capB E i₀ s x₀ Form parse encF scope hE hM hs hℓ hℓ'
      CT CL CB hT hL hB).privacy

/-- **The same at written numbers and the picked enumeration**, with a figure for its bound, which
the statement has. Proves Spec.idLaidNumber. -/
theorem idLaidNumber : Spec.idLaidNumber :=
  fun b Z b₀ s1 ℓr i₀ s x₀ Form parse encF scope hs =>
    ⟨idLaid b Z b₀ 0 s1 256 ℓr (2 ^ 40) (2 ^ 40) (2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
        (fun _ => 2 ^ 40)
        (pickBits b Z b₀ 0 256 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) fun _ => 2 ^ 40) i₀ s x₀ Form
        parse encF scope (pickBits_ok b Z b₀ 0 256 ℓr _ _ _) (by norm_num) hs le_rfl
        (twelve_home b Z scope).sMT (fun _ => le_rfl) (fun _ => le_rfl) fun _ => le_rfl,
      fun h1 t ht => by
        rw [upTo_of_le h1]
        exact zeta_number_caps (t + 1) (2 ^ 40) (2 ^ 40) (2 ^ 40) ht le_rfl le_rfl le_rfl⟩

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.relTaken_some
#print axioms OnBytes.FrontRoad.tie_taken
#print axioms OnBytes.FrontRoad.pickBits_ok
#print axioms OnBytes.FrontRoad.threeOfId_laid
#print axioms OnBytes.FrontRoad.laidId_V
#print axioms OnBytes.FrontRoad.laidId_reads_as_verify
#print axioms OnBytes.FrontRoad.laidId_within
#print axioms OnBytes.FrontRoad.idLaid
#print axioms OnBytes.FrontRoad.idLaidNumber
