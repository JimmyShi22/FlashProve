-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ClimbAtD.lean: E2E/ClimbFiles.lean at the three files' protocols of the full size
(`threeProtocolsAtFullSize`, Johnson/Flat/Dec/WiresAtSizes.lean), of which the compiled verifier's object is
made, and at the IOP as written in Lean (the library's word: the description) that `VerifierAndGoals.verify`
is compiled from. "Entry file" is the library's word for the copy's file with its link proof.

What is shown.
  `filesPairFullD`: the three protocols at the files' data DK, DP and the link's data ds are the
    three protocols at `noWork DK`, `noWork DP`, `ds.map rd0`, with proof-of-work bits added. The
    two decisions, the link's decision and all other letters are the same on both sides.
  `keySound_fullD_iff`, `entrySound_fullD_iff`, `proofSound_fullD_iff`: each of the three conditions
    `CompilerSoundnessConditionStatements.keySound`, `entrySound`, `proofSound` at `soundnessAnalysisDataAtFullSize T` holds if and only if the
    clause without proof of work holds (E2E/ClimbFiles.lean: `KeySound0`, `EntrySound0`,
    `ProofSound0`) at `files0 T`, with the same counts and the bound T.εs * 2^b in a round with b
    bits.
  `entrySound0_at_description`: at the description, at every three public files Z, the entry file's
    clause without proof of work is a theorem: from `FlashProve.hole_entrySound`
    (Johnson/Goal/Conditions/EntrySits.lean). It is free where the description's gate on the public
    files is shut: there the link's decision never accepts. c₀ and m₀ are read by nothing in the
    clause (`files0` reads the letters in T's type alone).
  `entrySoundAt_description`: there every round of the entry file without proof of work has error at
    most 2^-128 * 2^32 = 2^-96. So the LIST is not one with which every protocol is sound.

What is not shown. The key file's and the proof file's conditions are proved nowhere here: for them
this file has the equivalences alone, and nothing here says how many bits their rounds have.
That the entry file's language leaves out
any pair (instance, tables) at this configuration. That the link accepts anything
(`link_accepts_iff`, E2E/ClimbLink.lean: without proof of work it does if and only if with). That
the written text of the IOP, rewritten at 0 bits, gives `files0 T`: the link's decision is the same
function on both sides, and the text that it is made from still declares 32 bits
(E2E/ClimbLink.lean's head). The list of counts of `entrySound0_at_description` is bound by
∃: of it one knows the bound round by round and nothing more. What `hole_entrySound` rests on and
leaves open travels with it (its file's head): soundness alone, which a decision that never accepts
meets too; mutual correlated agreement (MCA) for Reed-Solomon codes up to the Johnson bound, as Lean
states it, which it uses. Nothing on queries, completeness or zero knowledge.

"Without proof of work" is a reading of this folder's writers: the same rounds' data with the number
of proof-of-work bits set to 0, under the same decision functions. Whether that protocol may stand
for "the IOP without proof of work" is an open question, which no theorem here settles.

This file's definitions may be read as part of a goal: they fix the protocol of which the clauses of
E2E/ClimbFiles.lean are stated. They count as none.





-/
import E2E.ClimbFiles
import Johnson.Flat.Dec.TwoSizesAt
import Johnson.Goal.Conditions.EntrySits
import OnBytes.Flat.LinkAsksWorkAt

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.Climb
open Iop Prob Hiop
open OnBytes.Flat (Files relationsAndEncodingOfClaims Coding RecFull)
open OnBytes.Slice (frS frZ)
open _root_.Run.PQ (View)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize InnerCompilerInputAndAnalysisFieldsAtFullSize soundnessAnalysisDataAtFullSize)
open scoped ENNReal

theorem linkBatchPair_bits (Ck : _root_.Run.PQ.CK) (K : KitFree Ck)
    (ds : List TypedOracleCompiler.Run.PQ.RD) (a : ℕ) (xs : List _root_.Run.PQ.XO) {X : Type}
    (dec : X → _root_.Run.PQ.View → Bool) :
    (linkBatchPair Ck K ds a xs dec).pair.toPair.toEmb.Bits (bitsL Ck ds) :=
  (congrArg (fun p : Pair (_root_.Run.Twin.up (TypedOracleCompiler.Run.PQ.SOf Ck (ds.map rd0)))
        (_root_.Run.Twin.up (TypedOracleCompiler.Run.PQ.SOf Ck ds)) => p.toEmb.Bits (bitsL Ck ds))
    (linkBatchPair_toPair Ck K ds a xs dec)).mpr (pairL_bits Ck K ds)

/-- **The three protocols of the full size are the three protocols at data without proof of work,
with the bits added.** -/
def filesPairFullD {X : Type} {A : (frS.toDecR frZ 402653181).Claims X}
    (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
    (runK : RecFull → View → View → View → Bool)
    (runP : X × RecFull → View → View → View → Bool) (ds : List TypedOracleCompiler.Run.PQ.RD)
    (xs : List _root_.Run.PQ.XO) (dec : RecFull × RecFull → View → Bool) (rK rP : RecFull)
    (depthReq : ℕ) (early : X → X) (salt : ℕ) :
    FilesPair
      (threeProtocolsAtFullSize (X := X) A R (noWork DK) (noWork DP) runK runP (ds.map rd0) xs dec rK rP
        depthReq early salt)
      (threeProtocolsAtFullSize (X := X) A R DK DP runK runP ds xs dec rK rP depthReq early salt) :=
  filesPair (OnBytes.RunA.lettersAt A R) .two DK DP _ _ _ _ _ _ _ runK _ runP
    (VerifiableInference.OnPublicFiles.linkProtocolAtFullSize (ds.map rd0) xs dec salt)
    (VerifiableInference.OnPublicFiles.linkProtocolAtFullSize ds xs dec salt) (2 ^ depthReq) early none
    (linkBatchPair (ckP .two) (kitFree_ckP .two) ds _ xs dec) (bitsL (ckP .two) ds)
    (linkBatchPair_bits (ckP .two) (kitFree_ckP .two) ds _ xs dec)

/-- The three protocols without proof of work, at the letters of T. -/
def files0 {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A}
    {DK DP : WholeD} {runK : RecFull → View → View → View → Bool}
    {runP : X × RecFull → View → View → View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD}
    {xs : List _root_.Run.PQ.XO} {dec : RecFull × RecFull → View → Bool} {rK rP : RecFull}
    {depthReq : ℕ} {early : X → X} {salt K : ℕ}
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early
      salt).Provers}
    (_ : InnerCompilerInputAndAnalysisFieldsAtFullSize (X := X) A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    Files (OnBytes.Slice.DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)) :=
  threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) (noWork DK) (noWork DP) runK runP (ds.map rd0) xs dec rK rP depthReq
    early salt

/-- The pair at the letters of T. -/
def pair0 {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A}
    {DK DP : WholeD} {runK : RecFull → View → View → View → Bool}
    {runP : X × RecFull → View → View → View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD}
    {xs : List _root_.Run.PQ.XO} {dec : RecFull × RecFull → View → Bool} {rK rP : RecFull}
    {depthReq : ℕ} {early : X → X} {salt K : ℕ}
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early
      salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize (X := X) A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    FilesPair (files0 T)
      (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt) :=
  filesPairFullD (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt

/-- **The key file's condition at the full size, both ways.** -/
theorem keySound_fullD_iff {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A}
    {DK DP : WholeD} {runK : RecFull → View → View → View → Bool}
    {runP : X × RecFull → View → View → View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD}
    {xs : List _root_.Run.PQ.XO} {dec : RecFull × RecFull → View → Bool} {rK rP : RecFull}
    {depthReq : ℕ} {early : X → X} {salt K : ℕ}
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early
      salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize (X := X) A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize T) ↔
      KeySound0 (files0 T) (pair0 T).gT (2 ^ T.W.depthReqT) T.εs :=
  keySound_iff (pair0 T) P T.letters T.names

/-- **The entry file's condition at the full size, both ways.** -/
theorem entrySound_fullD_iff {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A}
    {DK DP : WholeD} {runK : RecFull → View → View → View → Bool}
    {runP : X × RecFull → View → View → View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD}
    {xs : List _root_.Run.PQ.XO} {dec : RecFull × RecFull → View → Bool} {rK rP : RecFull}
    {depthReq : ℕ} {early : X → X} {salt K : ℕ}
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early
      salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize (X := X) A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T) ↔
      EntrySound0 (files0 T) (pair0 T).gL (2 ^ T.W.depthReqL) T.εs :=
  entrySound_iff (pair0 T) P T.letters T.names

/-- **The proof file's condition at the full size, both ways.** -/
theorem proofSound_fullD_iff {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A}
    {DK DP : WholeD} {runK : RecFull → View → View → View → Bool}
    {runP : X × RecFull → View → View → View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD}
    {xs : List _root_.Run.PQ.XO} {dec : RecFull × RecFull → View → Bool} {rK rP : RecFull}
    {depthReq : ℕ} {early : X → X} {salt K : ℕ}
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early
      salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize (X := X) A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize T) ↔
      ProofSound0 (files0 T) (pair0 T).gB T.εs :=
  proofSound_iff (pair0 T) P T.letters T.names

/-- **At the description that the verifier is compiled from, the entry file's clause without proof
of work holds**, at every three public files Z and all c₀, m₀ (which nothing in the clause reads).
Where the gate on the public files is shut the link's decision never accepts, and the clause is
free. -/
theorem entrySound0_at_description (c₀ : VerifiableInference.Digest) (m₀ : List (Dig 256))
    (Z : VerifierAndGoals.PublicFiles) :
    EntrySound0 (files0 ((FlashProve.dataAtFiles FlashProve.flashProveData Z).inputFieldsAtReadings c₀ m₀))
      (pair0 ((FlashProve.dataAtFiles FlashProve.flashProveData Z).inputFieldsAtReadings c₀ m₀)).gL
      (2 ^ ((FlashProve.dataAtFiles FlashProve.flashProveData Z).inputFieldsAtReadings c₀ m₀).W.depthReqL)
      ((FlashProve.dataAtFiles FlashProve.flashProveData Z).inputFieldsAtReadings c₀ m₀).εs :=
  (entrySound_fullD_iff _).1 (FlashProve.hole_entrySound c₀ m₀ Z)

/-! ## The bound at the description -/

/-- If no round's data have more than w bits of proof of work, the chain's list of bits has none
above w. L: the rounds' numbers of bits, written out. -/
theorem bitsZ_allLe (Ck : _root_.Run.PQ.CK) (w : ℕ) :
    ∀ (ds : List TypedOracleCompiler.Run.PQ.RD) (L : List ℕ), ds.map (·.entry.work) = L →
      (∀ b ∈ L, b ≤ w) → (bitsZ Ck (z0 ds)).AllLe w
  | [], _, _, _ => trivial
  | d :: ds, [], h, _ => by
      have h' : d.entry.work :: ds.map (·.entry.work) = [] := h
      cases h'
  | d :: ds, b :: L, h, hb => by
      have h' : d.entry.work :: ds.map (·.entry.work) = b :: L := h
      injection h' with h1 h2
      exact ⟨le_of_eq_of_le h1 (hb b (List.Mem.head L)),
        bitsZ_allLe Ck w ds L h2 fun c hc => hb c (List.Mem.tail b hc)⟩

/-- At the letters of T: the entry file's condition gives, without proof of work, one bound for all
rounds of the entry file: T.εs * 2^w, if no round of the link has more than w bits. -/
theorem entrySound_fullD_at_most {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A}
    {DK DP : WholeD} {runK : RecFull → View → View → View → Bool}
    {runP : X × RecFull → View → View → View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD}
    {xs : List _root_.Run.PQ.XO} {dec : RecFull × RecFull → View → Bool} {rK rP : RecFull}
    {depthReq : ℕ} {early : X → X} {salt K : ℕ}
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early
      salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize (X := X) A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (L : List ℕ) (hL : ds.map (·.entry.work) = L) (w : ℕ) (hw : ∀ b ∈ L, b ≤ w)
    (h : VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T)) :
    EntrySoundAt (files0 T) (T.εs * 2 ^ w) :=
  ((entrySound_fullD_iff T).1 h).at_most
    (_root_.Run.Twin.allLo_eq (TypedOracleCompiler.Run.PQ.SOf (ckP .two) (ds.map rd0))) w
    ⟨Nat.zero_le w, bitsZ_allLe (ckP .two) w ds L hL hw⟩

/-- **At the description, without proof of work, every round of the entry file has error at most
2^-128 * 2^32**, that is 2^-96: six of the link's 41 rounds have 32 bits of proof of work, the
others none (`works_full`, OnBytes/Flat/LinkAsksWorkAt.lean), and the stated bound with proof of
work is 2^-128. So no count of the list is as large as its round: the lists with which every
protocol is sound are shut out. -/
theorem entrySoundAt_description (c₀ : VerifiableInference.Digest) (m₀ : List (Dig 256))
    (Z : VerifierAndGoals.PublicFiles) :
    EntrySoundAt (files0 ((FlashProve.dataAtFiles FlashProve.flashProveData Z).inputFieldsAtReadings c₀ m₀))
      ((2 : ℝ≥0∞)⁻¹ ^ 128 * 2 ^ 32) :=
  entrySound_fullD_at_most ((FlashProve.dataAtFiles FlashProve.flashProveData Z).inputFieldsAtReadings c₀ m₀) _
    OnBytes.Flat.Work.works_full 32 (by decide) (FlashProve.hole_entrySound c₀ m₀ Z)

end AtPublicFiles.Climb

#print axioms AtPublicFiles.Climb.entrySoundAt_description
#print axioms AtPublicFiles.Climb.filesPairFullD
#print axioms AtPublicFiles.Climb.keySound_fullD_iff
#print axioms AtPublicFiles.Climb.entrySound_fullD_iff
#print axioms AtPublicFiles.Climb.proofSound_fullD_iff
#print axioms AtPublicFiles.Climb.entrySound0_at_description
