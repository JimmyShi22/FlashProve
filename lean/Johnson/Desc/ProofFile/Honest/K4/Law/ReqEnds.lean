-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/ReqEnds.lean: TESTS THAT CAN FAIL.

What is here. THE VERIFIER's TEST ON THE REQUEST's WORDS, TRIED AT ITS ENDS. reqOk
(Johnson/Desc/First/State.lean) is a test with code: T + 2 words; every token below the size V of
the vocabulary; the covered range r, e with r < e ≤ T. The laws on the seat of the feed-forward
layers' own rounds (sub-protocol K4) take its yes as a premise (reqFine, Law/TokensSeat.lean). Here
it is evaluated fourteen times at T = 4, at thirteen synthetic requests (one of them at two sizes
of the vocabulary): four evaluations that accept, at the ends of what it accepts, and ten negative
tests. reqOk_req: the test reads of its state the request's words alone; so the state at which it
is tried does not matter: reqFine_blank (Law/TokensSeatReady.lean) says so of reqFine.

  `reqOk_req`   two states with one request: one answer.
  `reqAt`       a synthetic request: n tokens v, then r and e, laid on the library's blank state.

Limits. Evaluations at one small T and two small V: no statement on any other. Verify.words32,
which makes the words out of a request file's bytes, is tried at no file. Nothing on the reply's
word, which reqOk does not read. That a request of the full size passes is not tried.

No property is claimed.
-/
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open VerifiableInference.Desc.First (S)

/-- Two states with one request: one answer. -/
theorem reqOk_req {s s' : S} (h : s.req = s'.req) (T V : Nat) : s.reqOk T V = s'.reqOk T V := by
  unfold S.reqOk S.tokv S.rowR S.rowE S.reqT
  rw [h]

/-- A synthetic request: n tokens v, then the first covered position r and the position e behind the
last, laid on the library's blank state. -/
def reqAt (n : Nat) (v r e : UInt32) : S := S.blank.withReq (Array.replicate n v ++ #[r, e])

/- accepted: the largest token with the first range of one position; the last such range; the
longest range -/
#guard (reqAt 4 6 0 1).reqOk 4 7
#guard (reqAt 4 0 3 4).reqOk 4 7
#guard (reqAt 4 6 0 4).reqOk 4 7
/- accepted: r and e are not held against the size of the vocabulary -/
#guard (reqAt 4 0 3 4).reqOk 4 3
/- negative tests: a token that is the size of the vocabulary: in all places; in the first, a
middle and the last alone -/
#guard !(reqAt 4 7 0 1).reqOk 4 7
#guard !(S.blank.withReq #[7, 0, 0, 0, 0, 1]).reqOk 4 7
#guard !(S.blank.withReq #[0, 0, 7, 0, 0, 1]).reqOk 4 7
#guard !(S.blank.withReq #[0, 0, 0, 7, 0, 1]).reqOk 4 7
/- negative tests: there is one length, T + 2: one word less, one word more -/
#guard !(reqAt 3 0 0 1).reqOk 4 7
#guard !(reqAt 5 0 0 1).reqOk 4 7
/- a negative test: no word at all; it is refused for its length, and its range is empty too -/
#guard !(S.blank.withReq #[]).reqOk 4 7
/- negative tests: an empty range, a range that runs backwards, a range that ends beyond T -/
#guard !(reqAt 4 0 1 1).reqOk 4 7
#guard !(reqAt 4 0 2 1).reqOk 4 7
#guard !(reqAt 4 0 0 5).reqOk 4 7

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.reqOk_req
