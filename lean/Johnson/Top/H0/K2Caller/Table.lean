-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/Table.lean: the records of Row.lean off the plan: for each group of a
proof's first chain but the first, the numbers of the code switch into it, as a pure function of the
planner's own sizes and records; and that the record's two rounds are the planner's own two rounds
at that group.

OnBytes/Plan/ReqFrames.lean has the chain group by group as data (FrameN, framesOf), with the law
that the planner's list is these records' rounds (configure_frames). Here:
  oOf z n: the planner's samples of the group's first sending (reqSampled at the record's own
      fields)
  rowOf: the record of Row.lean: set, cs: the sizes'; g := the record's «before»; rad := the
      planner's radius of that group (radiusOf); o := oOf; roots := treesOf; rider := the last of
      the group's members, which is the fold's mask (membersOf). lo, l and kept are handed in
  restOf: what follows the two rounds in the group's rounds
  specs_are: the record's two rounds ARE the planner's: FrameN.rounds at a record with l ≠ 0, whose
      count of samples is that of its samples and where treesOf gives a number, is: the round REPLY
      if the link has plain scalars; then these two; then the rest
  sampled_of_mem, specs_are_of_mem: the count of samples is so at every record of framesFrom; so the
      identity holds at every record of a chain but the first, where treesOf gives a number
  tagsOf, keptAt: which sampled message of a link stands where in the link's list; the places of the
      messages that the switch into the next group keeps
  Place, placesOf, tableOf: all rows, from the three public files, each with the planner's record
      and the tags: lo and l are the library's linkList and linkRows (Johnson/G/LinkSig.lean)
Limits: definitions, and one identity. That treesOf gives a number is a premise; where it gives none
the planner refuses the plan. tagsOf is a reading of the order of sending (Johnson/G/Sends.lean:
frameSends), typed again; it is held against the lists by a test alone. placesOf parses: Lean's
kernel does not evaluate it. Only the switches of a proof's first chain are here. Nothing on
soundness. On hiding nothing.
-/
import Johnson.Top.H0.K2Caller.Row
import OnBytes.Plan.ReqFrames
import Johnson.G.LinkSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Params OnBytes.Plan Johnson.Top.H

/-- The planner's samples of a group's first sending. -/
def oOf (z : ProofSized) (n : FrameN) : List SampleSize :=
  reqSampled z.codes n.sent n.sendGroup z.batch.own.first n.riders

/-- **The record of the switch into a group.** -/
def rowOf (z : ProofSized) (lo l : List (OracleShape × ℕ)) (kept : List ℕ) (n : FrameN) : SwRow :=
  { set := z.set, cs := z.codes, lo := lo, g := n.before, rad := radiusOf z.set n.before, l := l,
    o := oOf z n
    roots := (treesOf z.codes n.sent.toArray).getD 0, kept := kept, rider :=
        ((n.members.getLast?).map (·.shape)).getD {} }

/-- What follows the two rounds of the switch in a group's rounds. -/
def restOf (z : ProofSized) (L : ℕ → ℕ → List RoundSpec) (n : FrameN) : List RoundSpec :=
  match n.link with
  | none =>
    ioppList z.set .request z.last.stages
      (n.carried + sumT (n.members.map (·.shape.answers))) 0 z.request.choice.masksRide
  | some _ =>
    L n.l 0 ++ (momentsList z L n.l n.msgs n.moments 1 ++
      (batRound z.set [n.closed] n.batRows :: foldList z.set n.closed 0))

/-- **The record's two rounds are the planner's.** -/
theorem specs_are (z : ProofSized) (L : ℕ → ℕ → List RoundSpec) (n : FrameN) (lo l : List
    (OracleShape × ℕ)) (kept : List ℕ)
    (hl : n.l ≠ 0) (hs : n.sampled = (oOf z n).length) (ht : (treesOf z.codes n.sent.toArray).isSome
        = true) :
    FrameN.rounds z L n =
      (if n.plain != 0 then [.silent "REPLY" (24 * n.plain) 0] else []) ++ ((rowOf z lo l kept
          n).specs ++ restOf z L n) := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 ht
  have h0 : (n.l == 0) = false := beq_eq_false_iff_ne.2 hl
  have e : reqSendOpen z.set z.codes n.sent n.sendGroup z.batch.own.first n.riders = [sendSeed z.set
      (oOf z n) t] := by
    unfold reqSendOpen
    rw [ht]
    rfl
  have er : (rowOf z lo l kept n).specs =
      [sendSeed z.set (oOf z n) t,
        locRound z.set .request n.before (24 * (z.set.samples * n.sampled)) 0 (z.set.samples *
            n.sampled)] := by
    unfold SwRow.specs rowOf
    simp only [ht, Option.getD_some, hs]
  unfold FrameN.rounds
  rw [er, e, h0]
  rfl

/-- The count of samples of a chain's record is that of its samples. -/
theorem sampled_of_mem (z : ProofSized) :
    ∀ (gs : List ReqGroup) (l : ℕ) (links : List ReqLink) (open_ : List ℕ) (before : GroupSize) (n :
        FrameN),
      n ∈ framesFrom z l gs links open_ before → n.sampled = (oOf z n).length
  | [], _, _, _, _, _, h => by
      unfold framesFrom at h
      exact absurd h (List.not_mem_nil)
  | g :: gs, l, links, open_, before, n, h => by
      unfold framesFrom at h
      rcases List.mem_cons.1 h with rfl | h
      · rfl
      · cases hk : links.head? with
        | none =>
          simp only [hk] at h
          exact absurd h (List.not_mem_nil)
        | some v =>
          simp only [hk] at h
          exact sampled_of_mem z gs _ _ _ _ n h

/-- **At every record of a proof's first chain but the first**, where the number of trees follows.
-/
theorem specs_are_of_mem (z : ProofSized) (sub : Subproofs) (L : ℕ → ℕ → List RoundSpec) (n :
    FrameN) (hn : n ∈ framesOf z sub)
    (lo l : List (OracleShape × ℕ)) (kept : List ℕ) (hl : n.l ≠ 0) (ht : (treesOf z.codes
        n.sent.toArray).isSome = true) :
    FrameN.rounds z L n =
      (if n.plain != 0 then [.silent "REPLY" (24 * n.plain) 0] else []) ++ ((rowOf z lo l kept
          n).specs ++ restOf z L n) :=
  specs_are z L n lo l kept hl (sampled_of_mem z _ _ _ _ _ n hn) ht

/-- A sampled message of a link, by where it was first sent: none: the switch's target, or a message
that belongs to no link's group. -/
abbrev Tag := Option (ℕ × ℕ)

/-- The sampled messages of link k, in the order of sending, each with its tag and shape. g: the
link's group. -/
def tagsOf (z : ProofSized) (k : ℕ) (g : ReqGroup) (link : ReqLink) : List (Tag × OracleShape) :=
  let own := link.messages.zipIdx
  let at0 : List (Tag × OracleShape) :=
    (if 0 < k then [(none, g.target.shape)] else []) ++
    (g.target.kept.toList.zip g.born.toList).map (fun x => (some x.2, x.1.shape)) ++
    (own.filter fun m => m.1.moment == 0).map (fun m => (some (k, m.2), m.1.shape)) ++
    (if k == 0 then z.request.atStart.map fun a => (none, a.shape) else [])
  let later := (own.filter fun m => m.1.moment != 0).map fun m => ((some (k, m.2) : Tag), m.1.shape)
  (at0 ++ later).filter fun x => decide (0 < x.2.answers)

/-- The places, in link k's list, of the messages that the switch into the next group keeps. next:
the next group. -/
def keptAt (tags : List (Tag × OracleShape)) (next : ReqGroup) : List ℕ :=
  next.born.toList.filterMap fun b => (tags.zipIdx.find? fun t => t.1.1 == some b).map (·.2)

/-- A place of the switch: the planner's record of the group, the tags of the link in front, the
riders of the sending, the record of Row.lean. -/
structure Place where
  n : FrameN
  tags : List (Tag × OracleShape)
  /-- the messages without a sample in the group's first sending, by the library's list of sendings
  -/
  riders : List OracleShape
  row : SwRow

/-- **All places, from the three public files**, with the planner's sizes. -/
def placesOf (pol lay KL : ByteArray) : Except String (ProofSized × List Place) := do
  let p ← OnBytes.Model.Verify.planned pol KL (some lay)
  let z := p.chains.made.sized.proof
  let R ← Johnson.G.sendRowsOf pol lay KL
  let frames := framesOf z (OnBytes.Model.Verify.subproofsWith p.X z.request.link)
  let groups := (reqGroups z.request).toList
  pure (z, (frames.filter fun n => n.l != 0).map fun n =>
    let k := n.l - 1
    let tags := tagsOf z k (groups.getD k default) (z.request.link.getD k default)
    ⟨n, tags, ((Johnson.G.linkRows R n.l).head?.map (·.riders)).getD [],
      rowOf z (Johnson.G.linkList R k) (((Johnson.G.linkRows R n.l).head?.map (·.sampled)).getD [])
          (keptAt tags n.group) n⟩)

/-- **All rows.** -/
def tableOf (pol lay KL : ByteArray) : Except String (List SwRow) := do
  let x ← placesOf pol lay KL
  pure (x.2.map (·.row))

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.specs_are
#print axioms VerifiableInference.Desc.First.K2Caller.sampled_of_mem
#print axioms VerifiableInference.Desc.First.K2Caller.specs_are_of_mem
