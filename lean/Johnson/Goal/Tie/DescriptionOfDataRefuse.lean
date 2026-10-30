-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Tie/DescriptionOfDataRefuse.lean: where D* says no.
`buildReq_auxNo`: at the further tokens `auxNo` the builder builds nothing. `innerCompiledVerifier_no_build`:
where no instance is built, `innerCompiledVerifier` says no (by `innerCompiledVerifier_eq`,
Johnson/Top/InnerCompiledVerifierSide.lean). `verify_descriptionOfDataOnBytes_refused`: where the decoders refuse, the goals'
verify at the built D* is false, at every L.

-/
import Johnson.Goal.Tie.DescriptionOfData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.Tie OnBytes.RunA
open _root_.Run
open TypedOracleCompiler.Compile.Batch.Cms
open PV.Head (cThru sevenThru)

theorem vocabularyTokens_auxNo : vocabularyTokens auxNo = none := by
  show (if h : Inst.Model.ppref.V < Inst.Model.ppref.V then
    (vocabularyTokens []).map (⟨Inst.Model.ppref.V, h⟩ :: ·) else none) = none
  rw [dif_neg (Nat.lt_irrefl _)]

theorem requestOfTokens_auxNo (x : List Token × List Token) : requestOfTokens x auxNo = none := by
  unfold requestOfTokens
  rw [vocabularyTokens_auxNo]
  cases vocabularyTokens x.1 <;> cases vocabularyTokens x.2 <;> rfl

/-- At these further tokens the program's builder builds nothing. -/
theorem buildReq_auxNo (x : List Token × List Token) : Flat.buildReq x auxNo = none := by
  unfold Flat.buildReq
  rw [requestOfTokens_auxNo]
  rfl

/-- **Where no instance is built innerCompiledVerifier says no.** -/
theorem innerCompiledVerifier_no_build (r : InnerCompilerInput) (hash : VerifiableInference.Hash) (commitment :
                          Commitment)
    (prompt output : List Token) (q : List Token × (KeyRoot 256 r.protocol × OfflineLinkOnlineProof 256 r.protocol r.offlineRoundSplits r.linkRoundSplits))
    (h : r.buildInstance (prompt, output) q.1 = none) :
    (innerCompiledVerifier r commitment prompt output q).evaluate hash = false := by
  -- `verifyV` at `r.toInputV` is reached by `innerCompiledVerifier_eq` (Johnson/Top/InnerCompiledVerifierSide.lean)
  have h' : r.toInputV.build (prompt, output) (q.1, q.2.1.v, q.2.2.v).1 = none := h
  rw [innerCompiledVerifier_eq]
  unfold verifyV ZKCP.verifyBuilt
  simp only [h']
  rfl

/-- The right side at a form with these further tokens. -/
theorem DescriptionDataAtFiles.innerCompiledVerifierAnswerOnDecodedProof_refuses {Zk : OnBytes.K.Pub} (s : DescriptionDataAtFiles Zk) (c : ByteArray) (hc : c.size = 32)
    (seven : List ByteArray) (hash : VerifiableInference.Hash) (commitment : Commitment)
    (prompt output : List Token) (f : DecodedProof) (hf : f.aux = auxNo) :
    s.innerCompiledVerifierAnswerOnDecodedProof c hc seven hash commitment prompt output f = false :=
  innerCompiledVerifier_no_build _ hash commitment prompt output _
    (show Flat.buildReq (prompt, output) f.aux = none by rw [hf]; exact buildReq_auxNo _)

variable (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) {Form : Type} (Hn : CommitterAndProver Form)
  (dec : ByteArray → Form → Option DecodedProof) (f₀ : DecodedProof)

/-- verify_descriptionWithDecoder at every form: the right side at what the parser lays. -/
theorem verify_descriptionWithDecoder_any (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true) (O : ByteArray → ByteArray)
    (hO : (cThru O (asDescriptionFiles Z)).size = 32)
    (h7 : ∀ b ∈ sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z)), b.size = 32)
    (commitment : Commitment) (prompt output : List Token) (B : Form) :
    (VerifierAndGoals.verify (descriptionWithDecoder S Hn dec f₀) Z ((descriptionWithDecoder S Hn dec f₀).parse Z) commitment prompt
        output B).evaluate
        (hashOf O) =
      (S Z).innerCompiledVerifierAnswerOnDecodedProof (cThru O (asDescriptionFiles Z)) hO (sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles
                                                                      Z))) (hashOf O)
        commitment prompt output ((dec (cThru O (asDescriptionFiles Z)) B).getD f₀) := by
  cases hd : dec (cThru O (asDescriptionFiles Z)) B with
  | some f => exact verify_descriptionWithDecoder S Hn dec f₀ Z scope O hO h7 commitment prompt output B f hd
  | none =>
    -- the same description at the decoder that always takes: pointwise the same parser's value
    have h1 := verify_descriptionOfFields_thru (fun Z => (S Z).toDescriptionFields) (committerAndProverWithParser S Hn dec f₀) Z
      ((descriptionWithDecoder S Hn dec f₀).parse Z) scope O hO commitment prompt output B
    have h2 : proofAt ((descriptionWithDecoder S Hn dec f₀).parse Z) prompt output B (hashOf O) =
        (S Z).typedOf (cThru O (asDescriptionFiles Z)) f₀ := by
      show (S Z).typedOf (digToBytes (cAt Z (hashOf O))) ((dec (digToBytes (cAt Z (hashOf O)))
          B).getD f₀) = _
      rw [cAt_hashOf, digToBytes_bytesToDig _ hO, hd]
      rfl
    have h3 := (S Z).verifyTwo_congr ((S Z).tOf_at _ hO _ h7) (hashOf O) commitment prompt output
      ((S Z).typedOf (cThru O (asDescriptionFiles Z)) f₀)
    exact (h1.trans (congrArg (fun q : (S Z).Typed =>
      (innerCompiledVerifier (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings (bytesToDig (cThru O (asDescriptionFiles Z)))
                                 ((sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z))).map bytesToDig))) commitment
            prompt output
        q).evaluate (hashOf O)) h2)).trans h3

/-- **WHERE THE DECODERS REFUSE, THE GOALS' verify AT THE BUILT DSAYS no.** (`roundsDataFit` is not asked:
  it holds at both branches of `dataAtFiles`.) -/
theorem verify_descriptionOfDataOnBytes_refused (L : DescriptionData) (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (O : ByteArray → ByteArray) (hO : (cThru O (asDescriptionFiles Z)).size = 32)
    (h7 : ∀ b ∈ sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z)), b.size = 32)
    (commitment : Commitment) (prompt output : List Token) (B : FormBytes)
    (hdec : decodeD (cThru O (asDescriptionFiles Z)) B = none) :
    (VerifierAndGoals.verify (descriptionOfDataOnBytes L) Z ((descriptionOfDataOnBytes L).parse Z) commitment prompt output B).evaluate
        (hashOf O) = false := by
  have h1 := verify_descriptionWithDecoder_any (dataAtFiles L) L.honest decodeD L.f₀ Z scope O hO h7 commitment prompt
      output B
  rw [hdec] at h1
  exact h1.trans ((dataAtFiles L Z).innerCompiledVerifierAnswerOnDecodedProof_refuses _ hO _ (hashOf O) commitment prompt output L.f₀ L.hf₀)

end FlashProve
