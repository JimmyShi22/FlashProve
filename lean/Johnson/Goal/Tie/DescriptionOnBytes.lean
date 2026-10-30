-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Tie/DescriptionOnBytes.lean: D* at a form and a decoder, and at the bytes of the five parsed
files.
`parserWithDecoder`: one query, for c; then the decoder at c's bytes; where it refuses, a fixed form is laid.
`descriptionWithDecoder`, `verify_descriptionWithDecoder`: the description and the goals' verify at it, at a form that the
decoder takes. `FormBytes`: the parsed files as they lie on disk, and the further tokens. `decodeD`:
the three decoders (Johnson/Top/Fire/Code/FileInOf.lean, Johnson/PV/EntryInKey.lean) as one
function; it hashes nothing. `descriptionOnBytes`, `verify_descriptionOnBytes`: at these.
Limits. The bytes are an outside parser's form of the prover's files: untrusted for the proof. What
the user claims does not pass through the decoders.

-/
import Johnson.Goal.Tie.DescriptionOnDecodedProof
import Johnson.PV.EntryInKey
import Johnson.Top.Fire.Code.FileInOf

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.Tie
open _root_.Run
open _root_.Iop (Dig)
open PV.Head (cThru sevenThru)

/-- The honest side's letters, at a form. -/
structure CommitterAndProver (Form : Type) where
  Shown : Type
  shown : (s : IntegerTransformer.Settings) → ModelWeights s → Shown
  Rand : Type
  sample : RandomizedAlgorithm Rand
  commit : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand →
    DeterministicAlgorithm Commitment
  prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm Form

variable (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) {Form : Type} (Hn : CommitterAndProver Form)
  (dec : ByteArray → Form → Option DecodedProof) (f₀ : DecodedProof)

/-- The parser: one query: c; the decoder at c's bytes; the typed proof. -/
def parserWithDecoder (Z : PublicFiles) (_ _ : List Token) (B : Form) : DeterministicAlgorithm
    (TypedProof (threeProtocolsAtFullSize (S Z).toDescriptionFields.A (relationsAndEncodingOfClaims (S Z).toDescriptionFields.A (S Z).toDescriptionFields.E) (S Z).toDescriptionFields.DK (S
                                                                                                  Z).toDescriptionFields.DP
      (S Z).toDescriptionFields.runK (S Z).toDescriptionFields.runP (S Z).toDescriptionFields.ds (S Z).toDescriptionFields.xs (S Z).toDescriptionFields.dec (S
                                                                                Z).toDescriptionFields.rK (S Z).toDescriptionFields.rP (S Z).toDescriptionFields.depthReq (S Z).toDescriptionFields.early
      (S Z).toDescriptionFields.salt) (S Z).toDescriptionFields.P) :=
  .query (configString Z) fun c =>
    .done ((S Z).typedOf (digToBytes c) ((dec (digToBytes c) B).getD f₀))

def committerAndProverWithParser : CommitterProverFormAndParser fun Z => (S Z).toDescriptionFields where
  Shown := Hn.Shown
  shown := Hn.shown
  Rand := Hn.Rand
  sample := Hn.sample
  commit := Hn.commit
  Form := Form
  parse := parserWithDecoder S dec f₀
  prove := Hn.prove

/-- **D* at a form and a decoder.** -/
def descriptionWithDecoder : Description := descriptionOfFields (fun Z => (S Z).toDescriptionFields) (committerAndProverWithParser S Hn dec f₀)

/-- The same at a further public reading that is a letter. -/
def descriptionWithDecoderAndReading (more : PublicFiles → Digest → DeterministicAlgorithm (List (Dig 256))) : Description :=
  descriptionOfFieldsWithReading (fun Z => (S Z).toDescriptionFields) (committerAndProverWithParser S Hn dec f₀) more

theorem parseDec_within (Z : PublicFiles) : Parser.Within ((descriptionWithDecoder S Hn dec f₀).parse Z) 1 :=
  fun _ _ _ _ => trivial

theorem parseDec_honest (Z : PublicFiles) : Parser.Within ((descriptionWithDecoder S Hn dec f₀).parse Z) honestBudget :=
  fun _ _ _ _ => trivial

theorem proofAt_parseDec (Z : PublicFiles) (O : ByteArray → ByteArray) (hO : (cThru O (asDescriptionFiles Z)).size =
            32)
    (prompt output : List Token) (B : Form) (f : DecodedProof) (hdec : dec (cThru O (asDescriptionFiles Z)) B =
            some f) :
    (parserWithDecoder S dec f₀ Z prompt output B).evaluate (hashOf O) = (S Z).typedOf (cThru O (asDescriptionFiles Z))
        f := by
  show (S Z).typedOf (digToBytes (cAt Z (hashOf O))) ((dec (digToBytes (cAt Z (hashOf O))) B).getD
      f₀) = _
  rw [cAt_hashOf, digToBytes_bytesToDig _ hO, hdec]
  rfl

/-- **THE GOALS' verify AT D* AT A FORM THAT THE DECODER TAKES.** -/
theorem verify_descriptionWithDecoder (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true) (O : ByteArray → ByteArray)
    (hO : (cThru O (asDescriptionFiles Z)).size = 32)
    (h7 : ∀ b ∈ sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z)), b.size = 32)
    (commitment : Commitment) (prompt output : List Token) (B : Form) (f : DecodedProof)
    (hdec : dec (cThru O (asDescriptionFiles Z)) B = some f) :
    (VerifierAndGoals.verify (descriptionWithDecoder S Hn dec f₀) Z ((descriptionWithDecoder S Hn dec f₀).parse Z) commitment prompt
        output B).evaluate
        (hashOf O) =
      (innerCompiledVerifier
        (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadingsAsBytes (cThru O (asDescriptionFiles Z)) hO
                       (sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z)))))
        commitment prompt output
        ((innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadingsAsBytes (cThru O (asDescriptionFiles Z)) hO
                         (sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z))))).back
          ((S Z).proofOf (cThru O (asDescriptionFiles Z)) f))).evaluate (hashOf O) := by
  have h1 := verify_descriptionOfFields_thru (fun Z => (S Z).toDescriptionFields) (committerAndProverWithParser S Hn dec f₀) Z
    ((descriptionWithDecoder S Hn dec f₀).parse Z) scope O hO commitment prompt output B
  have h2 : proofAt ((descriptionWithDecoder S Hn dec f₀).parse Z) prompt output B (hashOf O) =
      (S Z).typedOf (cThru O (asDescriptionFiles Z)) f := proofAt_parseDec S dec f₀ Z O hO prompt output B f
          hdec
  have h3 := (S Z).verifyTwo_congr ((S Z).tOf_at _ hO _ h7) (hashOf O) commitment prompt output
    ((S Z).typedOf (cThru O (asDescriptionFiles Z)) f)
  exact (h1.trans (congrArg (fun q : (S Z).Typed =>
    (innerCompiledVerifier (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings (bytesToDig (cThru O (asDescriptionFiles Z)))
                               ((sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z))).map bytesToDig))) commitment
          prompt output
      q).evaluate (hashOf O)) h2)).trans h3

/-! ## The form is bytes -/

/-- The parsed files as they lie on disk, and the further tokens. -/
structure FormBytes where
  aux : List Token
  kb : ByteArray
  sb : ByteArray
  leaf : ByteArray
  seeds : ByteArray
  pb : ByteArray

/-- **What a run does in front of the term**, as one function: it hashes nothing. -/
def decodeD (c : ByteArray) (B : FormBytes) : Option DecodedProof :=
  match PV.EntryInOf.entryAllD c B.kb B.sb B.leaf B.seeds, LKF.FileInOf.madeKeyOf c B.kb,
    LKF.FileInOf.madeProofOf c B.pb with
  | .ok x, .ok mT, .ok mB =>
    if x.2.2.2.all (·.2) && mT.ok && mB.ok then some ⟨B.aux, x.1, x.2.1, mB.copy, mT.inD, x.2.2.1,
        mB.inD⟩
    else none
  | _, _, _ => none

variable (Hb : CommitterAndProver FormBytes)

/-- **THE VALUE: D* AT THE PARSED FILES' BYTES.** -/
def descriptionOnBytes : Description := descriptionWithDecoder S Hb decodeD f₀

/-- The same at a further public reading that is a letter. -/
def descriptionOnBytesWithReading (more : PublicFiles → Digest → DeterministicAlgorithm (List (Dig 256))) : Description :=
  descriptionWithDecoderAndReading S Hb decodeD f₀ more

theorem parseBytes_within (Z : PublicFiles) : Parser.Within ((descriptionOnBytes S f₀ Hb).parse Z) 1 :=
  parseDec_within S Hb decodeD f₀ Z

/-- **THE GOALS' verify AT D* AT THE PARSED FILES' BYTES.** -/
theorem verify_descriptionOnBytes (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true) (O : ByteArray → ByteArray)
    (hO : (cThru O (asDescriptionFiles Z)).size = 32)
    (h7 : ∀ b ∈ sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z)), b.size = 32)
    (commitment : Commitment) (prompt output : List Token) (B : FormBytes) (f : DecodedProof)
    (hdec : decodeD (cThru O (asDescriptionFiles Z)) B = some f) :
    (VerifierAndGoals.verify (descriptionOnBytes S f₀ Hb) Z ((descriptionOnBytes S f₀ Hb).parse Z) commitment prompt output
        B).evaluate
        (hashOf O) =
      (innerCompiledVerifier
        (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadingsAsBytes (cThru O (asDescriptionFiles Z)) hO
                       (sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z)))))
        commitment prompt output
        ((innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadingsAsBytes (cThru O (asDescriptionFiles Z)) hO
                         (sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z))))).back
          ((S Z).proofOf (cThru O (asDescriptionFiles Z)) f))).evaluate (hashOf O) :=
  verify_descriptionWithDecoder S Hb decodeD f₀ Z scope O hO h7 commitment prompt output B f hdec

end FlashProve
