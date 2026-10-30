-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/ReqBytes.lean: a request of the frame read back off its two files. Tools for whoever
ties a description whose instance holds the files' bytes to the frame's requests.

The frame's instances are the requests Flat.Req. A description may take the request file's and the
reply file's bytes instead (requestBytesOf, replyBytesOf, Johnson/Flat/WordsBytes.lean). Over the
library's files alone (Johnson/Flat/LayBytes.lean: layB, unlayB; Johnson/Flat/EarlyApart.lean:
words32_bytesOfWords):

  backReq           a decoder: the request file's bytes to the request WITHOUT its reply; none where
                    unlayB refuses the bytes or the instance read is not well formed.
  backReq_bytes     backReq (requestBytesOf x.val) = some (reqWithoutReply x), at every request x.
  backReq_early     the same at the early part: backReq (requestBytesOf (reqWithoutReply x).val) is
                    that too: the request file does not hang on the reply.
  asked_word        the first word of the reply file is the request's own reply:
                    ((words32 (replyBytesOf x.val)).getD 0 0).toNat = x.val.y.val.
  reply_apart       so two requests with one reply file have one reply.

What is not claimed. Nothing on a table's key or on a record. Nothing on any description's own map
from the frame's instances to its own. The reference sizes alone.
-/
import Johnson.Flat.LayBytes
import Johnson.Flat.PubReq

set_option autoImplicit false

namespace Meaning

open Inst.Model
open OnBytes OnBytes.Flat OnBytes.Model.Verify
open VerifiableInference.OnPublicFiles.Flat (Req WellFormed)

/-- The request without its reply, read off the request file's bytes. -/
def backReq (b : ByteArray) : Option Req :=
  (unlayB (P := ppref) (b, ⟨0, ppref_V_pos⟩)).bind fun i =>
    if h : WellFormed i then some ⟨i, h⟩ else none

/-- **The request file gives the request without its reply back.** -/
theorem backReq_bytes (x : Req) : backReq (requestBytesOf x.val) = some (reqWithoutReply x) := by
  have e : unlayB (P := ppref) (requestBytesOf x.val, ⟨0, ppref_V_pos⟩) =
      some (withoutReply ppref_V_pos x.val) :=
    unlayB_layB (P := ppref) (by decide) (by decide) (withoutReply ppref_V_pos x.val)
  unfold backReq
  have w : WellFormed (withoutReply ppref_V_pos x.val) := (reqWithoutReply x).property
  rw [e, Option.bind_some, dif_pos w]
  rfl

/-- The same at the early part. -/
theorem backReq_early (x : Req) :
    backReq (requestBytesOf (reqWithoutReply x).val) = some (reqWithoutReply x) :=
  backReq_bytes x

/-- **The reply file's first word is the request's own reply.** -/
theorem asked_word (x : Req) : ((words32 (replyBytesOf x.val)).getD 0 0).toNat = x.val.y.val := by
  unfold replyBytesOf
  rw [words32_bytesOfWords]
  show (UInt32.ofNat x.val.y.val).toNat = _
  rw [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.lt_trans x.val.y.isLt (by decide))

/-- Two requests with one reply file have one reply. -/
theorem reply_apart {x x' : Req} (h : replyBytesOf x.val = replyBytesOf x'.val) :
    x.val.y = x'.val.y :=
  Fin.ext (by rw [← asked_word x, ← asked_word x', h])

end Meaning

#print axioms Meaning.backReq_bytes
#print axioms Meaning.backReq_early
#print axioms Meaning.asked_word
#print axioms Meaning.reply_apart
