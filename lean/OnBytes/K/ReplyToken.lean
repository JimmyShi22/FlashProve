-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/ReplyToken.lean: the token that the prover names for the reply, against the caller's
reply: the step on values. For proofs only; the program does not import this file.

In a proof's first chain the head's link takes one plain scalar off its first message. That scalar
goes two ways. `runLinkH` (OnBytes/Model/StagesLinks.lean) hands it on as the reply as received, and
`Proof.firstBlock` (OnBytes/Proof/File.lean) compares it with the caller's reply,
`Model.ofNat so.y`. The head's check (`Head.hear`, OnBytes/Model/HeadHeard.lean) makes a token of it
(`Head.replyToken`) and lays that token, by `Head.winOf`, into the list of checked tokens.
  `tokenOf plain`: the number that `replyToken` returns where it returns.
  `replyToken_eq`: `replyToken` is two tests and then `tokenOf`.
  `token_of_reply`: if the first plain scalar is equal to `Model.ofNat y`, and y is below the
    field's prime, then `tokenOf plain` is y.
  `win_of_reply`: so, where `coveredOf` returns and the first plain scalar is equal to
    `Model.ofNat so.y`, the list of checked tokens `winOf cov T (tokenOf plain)` is the field
    `hWin`.
What is not claimed. Nothing on a run. Not shown here: that in a run of the first chain's block
which ends in a yes the comparison was made and was true (OnBytes/K/ReplyRun.lean has it under two
named hypotheses); that the list `plain` which the head's check is given is the one whose first
entry `runLinkH` hands on; that the window and the vocabulary at which the head's routine runs are
those at which the statement's positions were made. The premise that y is below the prime, a law on
the field `hOn`, and a law on values toward the window are in OnBytes/K/ReplyMore.lean.


-/
import OnBytes.K.TokensCovered

set_option autoImplicit false

namespace OnBytes.K

open OnBytes OnBytes.Model

/-- The number that `Head.replyToken` returns where it returns. -/
def tokenOf (plain : Array E) : Nat := (plain.getD 0 zeroE).c0.toNat

/-- `replyToken` is two tests and then `tokenOf`. -/
theorem replyToken_eq (plain : Array E) (V : Nat) :
    Head.replyToken plain V = (do
      Model.mustAs "header-y" (plain.size == 1)
      Model.testAs "header-y" ((plain.getD 0 zeroE).c1 == 0 && (plain.getD 0 zeroE).c2 == 0 &&
        decide ((plain.getD 0 zeroE).c0.toNat < V))
      pure (tokenOf plain) : SubM Nat) := rfl

/-- If the first plain scalar is the caller's reply, the token is the caller's. -/
theorem token_of_reply {plain : Array E} {got : E} {y : Nat} (h0 : plain[0]? = some got)
    (h1 : (got == Model.ofNat y) = true) (hy : y < pW.toNat) : tokenOf plain = y := by
  have e1 : got = Model.ofNat y := by simpa using h1
  unfold tokenOf
  rw [Array.getD_eq_getD_getElem?, h0, Option.getD_some, e1]
  show (Model.fOfNat y).toNat = y
  unfold Model.fOfNat
  rw [Nat.mod_eq_of_lt hy]
  have hp : pW.toNat < 2 ^ 64 := by decide
  show (UInt64.ofNat y).toNat = y
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.lt_trans hy hp)

/-- Where the first plain scalar is the caller's reply, the list of checked tokens is `hWin`. -/
theorem win_of_reply {so : Head.StOwn} {T V : Nat} {cov : Head.Covered} {plain : Array E} {got : E}
    (hc : Head.coveredOf so T V = .ok cov) (h0 : plain[0]? = some got)
    (h1 : (got == Model.ofNat so.y) = true) (hy : so.y < pW.toNat) :
    Head.winOf cov T (tokenOf plain) = cov.hWin := by
  rw [token_of_reply h0 h1 hy]
  exact winOf_own hc

end OnBytes.K
