-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6Leaves.lean: AN ACCEPTING DECISION OF THE OUTPUT HEAD's OWN SUB-PROTOCOL
LEAVES THE CHAIN's STATEMENT AND ALL THAT WAS PUT OUT AS THEY WERE: it turns the open segment's part
of the verifier's state alone. Statements and proofs.

  blockAt_leaves   at the kind's sub-protocol at the seat (by Law/RowPromise.lean's
                   Came.decide_record, which writes the state behind out).
  seated_leaves    at the sub-protocol as a lot seats it (Johnson/Stored/HeadAddsAtS.lean:
                   seatedClaims), on the pattern of Law/KeepsTrees.lean's seated_trees.

USER. The field k6 of KeepShares (Johnson/P1L20R/RoomKeep.lean): the index-mask message's ledger,
the groups and that message's number are read off the statement and off what was put out.
The next token's like lies: Law/ReplyRest.lean: reply_rest.
WHAT IT IS NOT. The decision alone: nothing on the four runs of claims. Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RowPromise
import Johnson.Desc.Kinds.Law.SeatedBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)

/-- At the kind's sub-protocol at the seat. -/
theorem blockAt_leaves (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') : s'.st = s.st ∧ s'.out = s.out := by
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := Came.decide_record h iU3 work l hd
  exact ⟨rfl, rfl⟩

/-- **At the sub-protocol as a lot seats it.** -/
theorem seated_leaves {W : OnBytes.Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : b.decide s rs gs = .ok s') :
    s'.st = s.st ∧ s'.out = s.out := by
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some h
  unfold blockClaims at h0
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp h0
  have h1 := ((tested_decide _ _ _ _ _ _ _ _).1 hd).1
  exact blockAt_leaves W.hS i _ l (rs := rs) (gs := gs) h1

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.seated_leaves
