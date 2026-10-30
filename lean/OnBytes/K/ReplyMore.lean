-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/ReplyMore.lean: three small laws on values that the tie of the prover's token to the
caller's reply needs beside OnBytes/K/ReplyToken.lean. For proofs only; the program does not import
this file.

  `reply_small`: the reply that the program's reader returns is below the field's prime: it is the
    value of a word of four bytes. This pays the premise of `token_of_reply` and `win_of_reply`.
  `on_of`: the field `hOn` of what `coveredOf` returns is true exactly at the positions r to e - 1.
  `sized_same`: what `coveredOf` returns at the window T passes the test `Covered.sized` at no other
    window. The head's routine makes that test at its own window (OnBytes/Model/Head.lean), so in a
    run that passes it the head's window is the one at which the statement's positions were made.
What is not claimed: nothing on a run.


-/
import OnBytes.K.ReplyToken

set_option autoImplicit false

namespace OnBytes.K

open OnBytes OnBytes.Model

/-- The reply that the reader returns is below the field's prime. -/
theorem reply_small {P Q : Array UInt32} {T : Nat} {so : Head.StOwn}
    (h : Head.stFromCall P Q T = .ok so) : so.y < pW.toNat := by
  unfold Head.stFromCall at h
  obtain ⟨_, _, h⟩ := Params.exc_bind h
  obtain ⟨_, _, h⟩ := Params.exc_bind h
  dsimp only at h
  obtain ⟨_, _, h⟩ := Params.exc_bind h
  cases h
  have h1 : (Q.getD 0 0).toNat < 2 ^ 32 := (Q.getD 0 0).toNat_lt
  have h2 : 2 ^ 32 < pW.toNat := by decide
  exact Nat.lt_trans h1 h2

/-- The field `hOn` is true exactly at the covered positions. -/
theorem on_of {so : Head.StOwn} {T V : Nat} {cov : Head.Covered}
    (hc : Head.coveredOf so T V = .ok cov) (t : Nat) :
    cov.hOn.getD t false = (decide ((so.req.getD T 0).toNat ≤ t) &&
      decide (t < (so.req.getD (T + 1) 0).toNat) && decide (t < T)) := by
  unfold Head.coveredOf at hc
  obtain ⟨_, _, hc⟩ := Params.exc_bind hc
  obtain ⟨_, _, hc⟩ := Params.exc_bind hc
  dsimp only at hc
  obtain ⟨_, _, hc⟩ := Params.exc_bind hc
  obtain ⟨_, _, hc⟩ := Params.exc_bind hc
  cases hc
  dsimp only
  by_cases ht : t < T
  · simp [Array.getD_eq_getD_getElem?, ht]
  · simp [Array.getD_eq_getD_getElem?, ht]

/-- What `coveredOf` returns at the window T is sized for no other window. -/
theorem sized_same {so : Head.StOwn} {T T' V : Nat} {cov : Head.Covered}
    (hc : Head.coveredOf so T V = .ok cov) (hs : cov.sized T' = true) : T' = T := by
  unfold Head.coveredOf at hc
  obtain ⟨_, _, hc⟩ := Params.exc_bind hc
  obtain ⟨_, _, hc⟩ := Params.exc_bind hc
  dsimp only at hc
  obtain ⟨_, _, hc⟩ := Params.exc_bind hc
  obtain ⟨_, _, hc⟩ := Params.exc_bind hc
  cases hc
  unfold Head.Covered.sized at hs
  simp only [Bool.and_eq_true, beq_iff_eq, Array.size_map, Array.size_range] at hs
  exact hs.1.1.2.symm

end OnBytes.K
