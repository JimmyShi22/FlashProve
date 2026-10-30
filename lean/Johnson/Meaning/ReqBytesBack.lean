-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/ReqBytesBack.lean: THE WAY BACK OF THE DECODER backReq
(Johnson/Meaning/ReqBytes.lean: the request file's bytes to the request without its reply). That
file's two laws go from a request to its bytes. Here: from an answer of the decoder to the bytes
that it was given. Three small theorems, over two lemmas alone (Johnson/Flat/LayBytes.lean:
layB_of_unlayB; Johnson/Flat/EarlyApart.lean: words32_bytesOfWords).

Main names (namespace Meaning).
  backReq_file     where backReq b = some R: the request file of R is b.
  backReq_words    so the words of b are the request's words (the tokens, then r and e).
  backReq_reply    R's reply is 0: THE DECODER DOES NOT SEE THE REPLY FILE: nobody may take R's
                   reply for the reply of a run.

Every letter under "there is": none.
What is not claimed. That the decoder answers. Nothing on the reply file. The reference sizes alone.
Nothing on soundness.
-/
import Johnson.Meaning.ReqBytes

set_option autoImplicit false

namespace Meaning

open Inst.Model
open OnBytes OnBytes.Flat OnBytes.Model.Verify
open VerifiableInference.OnPublicFiles.Flat (Req WellFormed)

/-- What the decoder's answer was laid from. -/
theorem backReq_laid {b : ByteArray} {R : Req} (h : backReq b = some R) :
    layB (P := ppref) R.val = (b, ⟨0, ppref_V_pos⟩) := by
  unfold backReq at h
  obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain rfl := Option.some.inj h
    exact layB_of_unlayB hi
  · cases h

/-- **The request file of the decoder's answer is the file that it was given.** -/
theorem backReq_file {b : ByteArray} {R : Req} (h : backReq b = some R) :
    requestBytesOf R.val = b := by
  have e := backReq_laid h
  unfold layB at e
  exact (Prod.mk.inj e).1

/-- **The words of the file are the words of the decoder's answer.** -/
theorem backReq_words {b : ByteArray} {R : Req} (h : backReq b = some R) :
    words32 b = requestWordsOf R.val := by
  rw [← backReq_file h]
  unfold requestBytesOf
  exact words32_bytesOfWords _

/-- The decoder's answer has the reply 0. -/
theorem backReq_reply {b : ByteArray} {R : Req} (h : backReq b = some R) :
    R.val.y = ⟨0, ppref_V_pos⟩ := by
  have e := backReq_laid h
  unfold layB at e
  exact (Prod.mk.inj e).2

end Meaning

#print axioms Meaning.backReq_file
#print axioms Meaning.backReq_words
#print axioms Meaning.backReq_reply
