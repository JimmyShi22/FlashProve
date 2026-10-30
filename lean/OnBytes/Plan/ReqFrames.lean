-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Plan/ReqFrames.lean: the numbers of a proof's first chain, group by group, as data; and that
the planner's list of that chain is these records' rounds, in order.

The planner's routine for the chain of links (`Params.reqPlanFrom`) walks the groups: for each it
plans the reply in plain, if the link has one; the sending of the group's oracle messages; from the
second group on the round of positions at which the group before is opened; then the link's
sub-proof with its later moments, the batching and the fold; or, where no link is left, the last
test. OnBytes/Plan/PlanListsReq.lean has that walk as a list of rounds (`reqListFrom`), with the law
that the routine adds these rounds. Here the same walk returns data: one record `FrameN` for each
group, which holds what the group's rounds are made of, in the port's own terms and with no number
written anew; `FrameN.rounds` makes the group's rounds of a record; and `reqListFrom` is the
records' rounds one after the other (`reqListFrom_frames`). With
OnBytes/Model/LinkRoundsList.lean: from a yes of `configure` at the shapes that the verifier's own
plans hand over, the plan of a proof's first chain is the list of these rounds with what follows
the links (`firstChain_frames`, `configure_frames`).

Main definitions: `FrameN`, `frameAt`, `FrameN.rounds`, `framesFrom`, `framesOf`.
Main theorems: `reqListFrom_frames`, `firstChain_frames`, `configure_frames`.

Not claimed here: soundness or hiding. That `configure` says yes. That a number of a record is the
size of a typed object of the library, or that a bound that the planner states from it is true. What
OnBytes/Plan/PlanListsReq.lean and OnBytes/Model/LinkRoundsList.lean do not claim is not claimed
here. For proofs only; no module of the program imports this file.
-/
import OnBytes.Plan.PlanListsReq
import OnBytes.Model.LinkRoundsList

set_option autoImplicit false

namespace OnBytes.Plan

open OnBytes.Params

/-- What the rounds of one group of a proof's first chain are made of. -/
structure FrameN where
  /-- the group's number, from 0 -/
  l : Nat
  /-- the group's numbers of row variables, the target of the switch into it, who was born where -/
  group : ReqGroup
  /-- the link of the group; none: the group of the last test -/
  link : Option ReqLink
  /-- the oracle messages that are members of the group: the target of the switch, the kept
  messages, the link's messages of moment 0, the fold's mask -/
  members : List OracleNotice
  /-- what is sent in the group's first prover's message: the members and, at the first group, the
  messages that belong to no link's group -/
  sent : List OracleNotice
  /-- the group by whose lists the members' samples are priced -/
  sendGroup : GroupSize
  /-- how many of the sent messages, at the end, belong to no link's group -/
  riders : Nat
  /-- how many of the sent messages have a sample -/
  sampled : Nat
  /-- the group of the link that was closed last, which is opened here; not read at the first -/
  before : GroupSize
  /-- the rows that the switch into the group leaves on it -/
  carried : Nat
  /-- the rows that the link's sub-proof leaves open -/
  openRows : Nat
  /-- the later moments of the link: how many -/
  moments : Nat
  /-- the group as it is closed -/
  closed : GroupSize

/-- The link's oracle messages. -/
def FrameN.msgs (n : FrameN) : List ReqMessage := (n.link.map (·.messages)).getD []

/-- The plain scalars that are sent before the group's first prover's message. -/
def FrameN.plain (n : FrameN) : Nat := (n.link.map (·.plain)).getD 0

/-- The rows that are batched where the link is closed. -/
def FrameN.batRows (n : FrameN) : Nat :=
  n.openRows + n.carried + sumT (n.members.map (·.shape.answers)) + momentsRows n.msgs n.moments 1

/-- The record of group number l. gs: the groups after it; links, open_: the links and the
sub-proofs' open rows from this group on; before: the group of the link that was closed last. -/
def frameAt (z : ProofSized) (l : Nat) (g : ReqGroup) (gs : List ReqGroup) (links : List ReqLink)
    (open_ : List Nat) (before : GroupSize) : FrameN :=
  let msgs := (links.head?.map (·.messages)).getD []
  let members := membersOf z l g msgs
  let sent := if l == 0 then members ++ z.request.atStart else members
  let sg := if links.head?.isSome then z.link.group else z.last.first
  let riders := if l == 0 then z.request.atStart.length else 0
  { l := l, group := g, link := links.head?, members := members, sent := sent, sendGroup := sg
    riders := riders, sampled := (reqSampled z.codes sent sg z.batch.own.first riders).length
    before := before, carried := carriedRows z l g before, openRows := open_.headD 0
    moments := (msgs.getLast?.map (·.moment + 1)).getD 0 - 1, closed := closedGroup z g gs }

/-- The rounds of one group, made of its record. L: the sub-proofs' lists. -/
def FrameN.rounds (z : ProofSized) (L : Nat → Nat → List RoundSpec) (n : FrameN) :
    List RoundSpec :=
  (if n.plain != 0 then [.silent "REPLY" (24 * n.plain) 0] else []) ++
    ((if n.l == 0 then reqSendOwn z.set z.codes n.sent n.sendGroup z.batch.own.first n.riders
      else reqSendOpen z.set z.codes n.sent n.sendGroup z.batch.own.first n.riders ++
        [locRound z.set .request n.before (24 * (z.set.samples * n.sampled)) 0
          (z.set.samples * n.sampled)]) ++
    (match n.link with
    | none =>
      ioppList z.set .request z.last.stages
        (n.carried + sumT (n.members.map (·.shape.answers))) 0 z.request.choice.masksRide
    | some _ =>
      L n.l 0 ++ (momentsList z L n.l n.msgs n.moments 1 ++
        (batRound z.set [n.closed] n.batRows :: foldList z.set n.closed 0))))

/-- The records from group number l on. Where no link is left the list ends with that group's
record, whatever groups are left. -/
def framesFrom (z : ProofSized) :
    Nat → List ReqGroup → List ReqLink → List Nat → GroupSize → List FrameN
  | _, [], _, _, _ => []
  | l, g :: gs, links, open_, before =>
    frameAt z l g gs links open_ before ::
      (match links.head? with
      | none => []
      | some _ => framesFrom z (l + 1) gs (links.drop 1) (open_.drop 1) (closedGroup z g gs))

/-- **The frame's rounds are the records' rounds, one after the other.** -/
theorem reqListFrom_frames (z : ProofSized) (L : Nat → Nat → List RoundSpec) :
    ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink) (open_ : List Nat)
      (before : GroupSize),
      reqListFrom z L l gs links open_ before =
        (framesFrom z l gs links open_ before).flatMap (FrameN.rounds z L)
  | [], _, _, _, _ => by
      unfold reqListFrom framesFrom
      rfl
  | g :: gs, l, links, open_, before => by
      unfold reqListFrom framesFrom
      rw [List.flatMap_cons]
      cases hl : links.head? with
      | none =>
        simp only [FrameN.rounds, FrameN.plain, frameAt, hl, List.flatMap_nil, List.append_nil]
      | some v =>
        have ih := reqListFrom_frames z L gs (l + 1) (links.drop 1) (open_.drop 1)
          (closedGroup z g gs)
        simp only [FrameN.rounds, FrameN.plain, FrameN.msgs, FrameN.batRows, frameAt, hl, ih,
          List.append_assoc, List.cons_append]

/-- The records of a proof's first chain. -/
def framesOf (z : ProofSized) (sub : Subproofs) : List FrameN :=
  framesFrom z 0 (reqGroups z.request).toList z.request.link sub.openRows z.link.group

/-- What follows the links in a proof's first chain. -/
def afterFrames (z : ProofSized) (sub : Subproofs) (L : Nat → Nat → List RoundSpec)
    (after : List RoundSpec) : List RoundSpec :=
  (firstChainList z sub L after).drop
    ((framesOf z sub).flatMap (FrameN.rounds z L)).length

/-- **The list of a proof's first chain begins with the records' rounds.** -/
theorem firstChain_frames (z : ProofSized) (sub : Subproofs) (L : Nat → Nat → List RoundSpec)
    (after : List RoundSpec) :
    firstChainList z sub L after =
      (framesOf z sub).flatMap (FrameN.rounds z L) ++ afterFrames z sub L after := by
  unfold afterFrames
  have h : ∃ t, firstChainList z sub L after =
      (framesOf z sub).flatMap (FrameN.rounds z L) ++ t := by
    unfold firstChainList framesOf
    rw [reqListFrom_frames]
    exact ⟨_, rfl⟩
  obtain ⟨t, ht⟩ := h
  rw [ht, List.drop_left]

/-- **From `configure`'s yes at the shapes that the verifier's own plans hand over**: the plan of a
proof's first chain is the list of the records' rounds, with the model's sub-proofs' lists between,
and of what follows the links. -/
theorem configure_frames {X : Model.Verify.Public} {links : List ReqLink} {layout : ReqLayout}
    {identifiers : List Nat} {x : Shapes}
    (hx : Model.Verify.shapesWith X links layout identifiers = .ok x)
    {l : Lines} {cfg : ByteArray} {bits : Nat} {made : Configured}
    (h : configure l x cfg bits = .ok made) :
    ∃ F S2 S3, made.proof = [F, S2, S3] ∧
      PlanIs F (settingOf l) .request
        ((framesOf made.sized.proof x.sub).flatMap
            (FrameN.rounds made.sized.proof (Model.Verify.linkList (settingOf l) .request X)) ++
          afterFrames made.sized.proof x.sub (Model.Verify.linkList (settingOf l) .request X)
            []) := by
  obtain ⟨F, S2, S3, _, hp, _, p1, _, _⟩ := Model.Verify.configure_proof_model hx h
  refine ⟨F, S2, S3, hp, ?_⟩
  rw [← firstChain_frames]
  exact p1

end OnBytes.Plan
