-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/SeatReply.lean: the proximity test (the kind K12) at the first chain's finish
leaves the heard reply as it was. Theorems; no code.

  atFinish_leaves_reply   `Block.Leaves` (Johnson/Desc/Sound/FoldHeard.lean) at the reading
                          `s.out.reply`, the one seat of the heard reply.
  atFinish_reply          the same written out: where the block's decision goes on from s to s',
                          `s'.out.reply = s.out.reply`.
  atFinish_claims · atFinish_after   the block has no run of claims and no run behind the batching:
                          so its decision is all of it that the fold can call.
It holds whatever the parts are: nothing of the kind's block is looked at; a block that refuses
everything meets it too. Nothing on soundness. It speaks of `atFinish p` itself, not of that block
under a fold's wrappers.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.SeatLeaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Seat
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.First (S)

/-- The test at the finish leaves the heard reply's seat. -/
theorem atFinish_leaves_reply (p : P12) : (atFinish p).Leaves (·.out.reply) :=
  atFinish_leaves _ (fun _ _ _ _ => rfl) p

/-- The same, written out. -/
theorem atFinish_reply (p : P12) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (atFinish p).decide s rs gs = .ok s') :
    s'.out.reply = s.out.reply :=
  atFinish_leaves_reply p s rs gs s' h

/-- The block has no run of claims. -/
theorem atFinish_claims (p : P12) : (atFinish p).claims = [] := rfl

/-- The block has no run behind the batching. -/
theorem atFinish_after (p : P12) : (atFinish p).after = [] := rfl

end VerifiableInference.Desc.K12.Seat

#print axioms VerifiableInference.Desc.K12.Seat.atFinish_leaves_reply
#print axioms VerifiableInference.Desc.K12.Seat.atFinish_reply
#print axioms VerifiableInference.Desc.K12.Seat.atFinish_claims
#print axioms VerifiableInference.Desc.K12.Seat.atFinish_after
