-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ReplyFrame.lean: MEMBER 338 OF THE PROOF FILE's OWN FIRST CHAIN (the head's
front and the hearing of the reply) IN THE FORM THAT THE THREAD's FRAME ASKS (ProofFile.Honest.Carries |
Returns at firstZA g vals, Johnson/AtFull/Shape/FrameForm.lean). Under the head P5J.AtMgA; a joining
of laws; nothing is evaluated.
  `replyA t`: the step on the whole: replyGS t on the chain's shape (ReplyAtHead.lean); among the
    makes one group of rows more, with no row in it. `replyV V rs`: the test on values: there is one
    round, a reply can be read in it, and it is a token of the vocabulary of V entries.
  **`reply_frame`**: with Bs what the maker's own ProofFile.baseOf returns: for every g with g 338 =
    replyA (tailSh Bs.G₀.W.H.tl) and every vals with vals 338 s rs gs = replyV Bs.G₀.W.hS.V rs:
    Carries and Returns at 338.
By reply_at (ReplyAtHead.lean), carries_of_seat | returns_of_seat (FrameForm.lean).
Limits. The step g and the test vals are letters with an equation at one number: no table of all 358
is built here. replyV IS A TEST ON VALUES IN A ROUND; that there is just one round is asked by it
and not read off the member's declared rounds. UNDER THE HEAD: that it has a member is shown in
scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean);
that these three hold together, at two named sets of public files (`VerifierAndGoals.storedPublicFiles` and
`VerifierAndGoals.zGap`), in a side library (AtFullSide/Top/HeadMemberAtFull.lean, HeadMemberAtGap.lean). No
state is shown by a theorem at which the step returns. At the earlier hash OnBytes.secondHashFunction. Nothing
on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.Shape.FrameOpt
import Johnson.AtFull.Shape.ReplyAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link KindName roundsFit noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)
open ProofFile.Honest (Shape Carries Returns carries_seat returns_seat)

/-- The step of member 338 on the whole: replyGS on the chain's shape; the head's front opens one
group of rows more, with no row in it. -/
def replyA (t : TailSh) (x : ShA) : Except String ShA :=
  match replyGS t x.1 with
  | some u => .ok (u, { x.2 with groups := x.2.groups ++ [[]] })
  | none => .error "the reply's member refuses on shapes"

/-- The test on values: there is one round, a reply can be read in it, and it is a token. -/
def replyV (V : Nat) (rs : List Fmt.RoundView) : Bool :=
  match rs with
  | [q] =>
    match OnBytes.Desc.Reply.readReply q with
    | some y => OnBytes.Desc.Reply.isToken V y
    | none => false
  | _ => false

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The frame's two premises at member 338** (the head's front and the hearing of the reply). -/
theorem reply_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ Bs : ProofFile.PureBase,
      (cF.blocksInOrder[338]?).isSome = true ∧
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      ∀ (ft : Nat) g vals,
        g 338 = replyA (tailSh Bs.G₀.W.H.tl) →
        (∀ s rs gs, vals 338 s rs gs = replyV Bs.G₀.W.hS.V rs) →
        Carries cF.blocksInOrder ft (firstZA g vals) 338 ∧ Returns cF.blocksInOrder ft (firstZA g vals) 338 := by
  obtain ⟨Bs, b, e1, q, hc, hr⟩ := reply_at h
  refine ⟨Bs, by rw [q]; rfl, e1, fun ft g vals hg hv => ⟨?_, ?_⟩⟩
  · refine carries_of_seat q fun s rs gs t u _ hd hu => ?_
    rw [hg] at hu
    obtain ⟨c1, c2⟩ := hc s _ gs t hd
    unfold replyA at hu
    have c1' : replyGS (tailSh Bs.G₀.W.H.tl) (shA s).1 = some (chainSh t) := c1
    rw [c1'] at hu
    cases hu
    show (chainSh t, _) = (chainSh t, formsOf t.st)
    rw [c2]
    rfl
  · refine returns_of_seat q fun s rs gs u _ hu hvv => ?_
    rw [hg] at hu
    rw [hv] at hvv
    unfold replyA at hu
    split at hu
    · rename_i w hw
      unfold replyV at hvv
      split at hvv
      · rename_i q0 hq0
        split at hvv
        · rename_i y hy
          rw [hq0]
          exact hr s q0 y gs w hw hy hvv
        · cases hvv
      · cases hvv
    · cases hu

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.reply_frame
#print axioms Johnson.AtFull.Shape.replyA
#print axioms Johnson.AtFull.Shape.replyV
