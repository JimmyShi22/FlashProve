-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ReqReached.lean: UNDER THE HEAD P5J.AtMgA: AT EVERY STATE WITHOUT A MARK THAT A
FOLD OVER THE FIRST k MEMBERS OF THE PROOF FILE's OWN FIRST CHAIN REACHES FROM THE CHAIN's OWN
START, THE STATE's OWN TEST ON THE REQUEST (S.reqOk) HOLDS, at the public part's two numbers. A
joining of laws; nothing is evaluated.

Why it holds. The chain's start (ProofFile.startS, Johnson/Desc/ProofFile/Pub.lean) lays the request's
words and asks that test; where it fails the start is the blank state, which bears a mark. No member
turns the words or takes a mark off (ReqAtHead.lean's sources: Meaning.K2.seatKeeps_req,
seatBack_req, Johnson/LTPileR/ReqSeat.lean; over several members: Meaning.K2.open_fold_all,
Johnson/IMR/OpenFlat.lean).

  `start_reqOk`: the start, where it bears no mark, passes the test.
  **`reqOk_at_fold`**: under the head, at every k, ft, instance p, rounds and columns: foldBlocks ft
    (cF.blocksInOrder.take k) (ProofFile.startS Zp p) rs cols = .ok y and y.1.failed = none: then y.1.reqOk
    Zp.p.X.T Zp.p.X.P.h.V = true.

Beside it in the library: Meaning.K2.reqOk_reached (Johnson/IMR/AtReach.lean), in the goals' scope:
from the second border on the instance's request has passed its test, mark or no mark: it speaks of
the start; this file of the state that is reached.

Limits. AT THE PUBLIC PART's OWN T AND V (Zp.p.X.T, Zp.p.X.P.h.V): that the numbers at which a
member's test asks S.reqOk, S.covered or the tokens' test are these is not shown here. Whoever holds
a reached state in another form owes the fold. That the head has a member is shown in scope, where
the reader returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these
three hold together, at two named sets of public files, in a side library. At the format's second
hash function. Nothing on soundness, completeness or hiding.

-/
import Johnson.AtFull.Shape.ReqAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- The chain's own start, where it bears no mark, passes the state's own test on the request. -/
theorem start_reqOk (Z : ProofFile.Pub) (p : ProofFile.InstPub) (h : (ProofFile.startS Z p).failed = none) :
    (ProofFile.startS Z p).reqOk Z.p.X.T Z.p.X.P.h.V = true := by
  unfold ProofFile.startS at h ⊢
  dsimp only at h ⊢
  split
  · assumption
  · rename_i hq
    rw [if_neg hq] at h
    cases h

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At every reached state without a mark the state's own test on the request holds.** -/
theorem reqOk_at_fold (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (k ft : Nat) (p : ProofFile.InstPub)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (y : S × List Fmt.RoundView × List OpenedColumn)
    (hf : foldBlocks ft (cF.blocksInOrder.take k) (ProofFile.startS Zp p) rs cols = .ok y)
    (hm : y.1.failed = none) : y.1.reqOk Zp.p.X.T Zp.p.X.P.h.V = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have q := Meaning.K2.open_fold_all Meaning.K2.seatKeeps_req Meaning.K2.seatBack_req O trivial
    (fun _ _ _ => trivial) (plans_at h) k hf
  rw [reqOk_same q.1]
  exact start_reqOk Zp p (q.2 hm)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.start_reqOk
#print axioms Johnson.AtFull.Shape.reqOk_at_fold
