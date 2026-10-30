-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Tie/PadBeyond.lean: what the builder does with the further tokens (the padding).
`requestOf_pad_beyond`: where the prompt and the output fill the window, `IntegerModel.requestOf`
does not turn with the padding. `requestOfTokens_pad_beyond`, `buildReq_pad_beyond`: the like for
the two builders on numbers, at every padding of tokens of the vocabulary. `innerCompiledVerifier_aux`: general
in the input: `innerCompiledVerifier` reads the proof's further tokens through `buildInstance` alone.
`DescriptionDataAtFiles.innerCompiledVerifierAnswerOnDecodedProof_pad_beyond`: so at a full window the tie's right side does not turn with them.
So a proof is malleable in its further tokens. Not shown here: that no false claim on the prompt and
the output can be accepted. `promptOf_requestOf` and `replyOf_requestOf`
(VerifiableInference/RequestOfTokens.lean) say that the built request's prompt and checked tokens
are the given ones at every padding.

-/
import Johnson.Goal.Tie.DescriptionOfDataRefuse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat TypedOracleCompiler.Compile.Batch.Cms
open Inst.Model

/-- A full window reads no padding. -/
theorem requestOf_pad_beyond (prompt output padding : List IntegerModel.Token)
    (h : ppref.T ≤ prompt.length + output.length) :
    IntegerModel.requestOf prompt output padding = IntegerModel.requestOf prompt output [] := by
  have key : ∀ t : ℕ, t < ppref.T → (prompt ++ output ++ padding).getD t IntegerModel.tokenZero =
      (prompt ++ output ++ []).getD t IntegerModel.tokenZero := by
    intro t ht
    have hl : t < (prompt ++ output).length := by rw [List.length_append]; exact lt_of_lt_of_le ht h
    rw [IntegerModel.getD_app_left (prompt ++ output) padding IntegerModel.tokenZero t hl,
      IntegerModel.getD_app_left (prompt ++ output) [] IntegerModel.tokenZero t hl]
  unfold IntegerModel.requestOf
  split
  · congr 2
    funext t
    exact key t.val t.isLt
  · rfl

theorem length_vocabularyTokens : ∀ (l : List Token) (l' : List IntegerModel.Token),
    vocabularyTokens l = some l' → l'.length = l.length
  | [], l', h => by
      obtain rfl : [] = l' := Option.some.inj h
      rfl
  | t :: rest, l', h => by
      have h' : (if ht : t < ppref.V then (vocabularyTokens rest).map (⟨t, ht⟩ :: ·) else none) =
          some l' := h
      split at h'
      · cases hr : vocabularyTokens rest with
        | none => rw [hr] at h'; cases h'
        | some r =>
          rw [hr] at h'
          obtain rfl := Option.some.inj h'
          show r.length + 1 = rest.length + 1
          rw [length_vocabularyTokens rest r hr]
      · cases h'

theorem requestOfTokens_pad_beyond (x : List Token × List Token) (padding : List Token)
    (hv : (vocabularyTokens padding).isSome = true) (h : ppref.T ≤ x.1.length + x.2.length) :
    requestOfTokens x padding = requestOfTokens x [] := by
  obtain ⟨pd, hpd⟩ := Option.isSome_iff_exists.1 hv
  unfold requestOfTokens
  rw [hpd]
  show _ = (match vocabularyTokens x.1, vocabularyTokens x.2, some ([] : List IntegerModel.Token)
      with
    | some prompt, some output, some pad => IntegerModel.requestOf prompt output pad
    | _, _, _ => none)
  cases h1 : vocabularyTokens x.1 with
  | none => rfl
  | some p =>
    cases h2 : vocabularyTokens x.2 with
    | none => rfl
    | some o =>
      exact requestOf_pad_beyond p o pd
        (by rw [length_vocabularyTokens _ _ h1, length_vocabularyTokens _ _ h2]; exact h)

/-- **The program's builder at a full window.** -/
theorem buildReq_pad_beyond (x : List Token × List Token) (padding : List Token)
    (hv : (vocabularyTokens padding).isSome = true) (h : ppref.T ≤ x.1.length + x.2.length) :
    Flat.buildReq x padding = Flat.buildReq x [] := by
  unfold Flat.buildReq
  rw [requestOfTokens_pad_beyond x padding hv h]

/-- **innerCompiledVerifier reads the further tokens through the builder alone.** -/
theorem innerCompiledVerifier_aux (r : InnerCompilerInput) (hash : VerifiableInference.Hash) (commitment : Commitment)
    (prompt output aux aux' : List Token) (π : KeyRoot 256 r.protocol × OfflineLinkOnlineProof 256 r.protocol r.offlineRoundSplits r.linkRoundSplits)
    (h : r.buildInstance (prompt, output) aux = r.buildInstance (prompt, output) aux') :
    (innerCompiledVerifier r commitment prompt output (aux, π)).evaluate hash =
      (innerCompiledVerifier r commitment prompt output (aux', π)).evaluate hash := by
  have h' : r.toInputV.build (prompt, output) aux = r.toInputV.build (prompt, output) aux' := h
  rw [innerCompiledVerifier_eq, innerCompiledVerifier_eq]
  unfold verifyV ZKCP.verifyBuilt
  simp only [h']

/-- So at a full window the tie's right side does not turn with the further tokens. -/
theorem DescriptionDataAtFiles.innerCompiledVerifierAnswerOnDecodedProof_pad_beyond {Zk : OnBytes.K.Pub} (s : DescriptionDataAtFiles Zk) (c : ByteArray) (hc : c.size =
                                                                          32)
    (seven : List ByteArray) (hash : VerifiableInference.Hash) (commitment : Commitment)
    (prompt output : List Token) (f : DecodedProof) (hv : (vocabularyTokens f.aux).isSome = true)
    (h : ppref.T ≤ prompt.length + output.length) :
    s.innerCompiledVerifierAnswerOnDecodedProof c hc seven hash commitment prompt output f =
      s.innerCompiledVerifierAnswerOnDecodedProof c hc seven hash commitment prompt output { f with aux := [] } :=
  innerCompiledVerifier_aux _ hash commitment prompt output f.aux [] _
    (show Flat.buildReq (prompt, output) f.aux = Flat.buildReq (prompt, output) [] from
      buildReq_pad_beyond (prompt, output) f.aux hv h)

end FlashProve
