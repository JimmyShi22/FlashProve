-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/Tw/K2/First.lean: the kind «the code switch», second file: WHAT STANDS AROUND THE
SWITCH IN A LATER LINK's FIRST CALL (the program's ReqFrame.first,
OnBytes/Iop/Req.lean:322-346, at a link that is not link 0) AND IN THE FINISH (ReqFrame.finish,
:372-377), as plain functions on data. A new group is the plain ground's newGroupP; the joins are
its joinP (joinG, Switch.lean).

  firstFront    in front of the switch: which call is due; the link's and the group's records; the
  announcements; the new group.
                After Req.lean:323-329, beginLink (:307-309) and Blk.newGroup
                (Ground.lean:1269-1275).
  firstBehind   behind the switch: as many numbers as announcements; the fresh mask's number; the
  frame's fields; the link's own messages
                of moment 0 join the group. After Req.lean:339-346 and joinOwn (:300-304) over
                Blk.join (joinG, Switch.lean).
  finishFront | finishBehind   the same around the finish's switch. After Req.lean:373-375 and :377.
NOT HERE: the plain scalars and the round «REPLY» (Req.lean:330-331): they stand between firstFront
and the switch: firstBehind takes
the scalars as an argument. Link 0's first call (:333-335). The last test (:378). ChainCheck.first |
finish's own lines
(Model/ReqChain.lean:114-117, :145-147) and runLinkH's.
No Blk, no Ctx. The frame (ReqFrame) is the program's record, carried whole. No soundness:
definitions with code.
-/
import Johnson.Top.H0.Tw.K2.Switch
import OnBytes.Iop.Req

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Tw.K2
open OnBytes
open VerifiableInference.Desc.Ground (newGroupL newGroupP)
open OnBytes.Params (ReqMessage ReqLink ReqShape)

/-- [F4-F6] a new group: the plain ground's newGroupP (its three clauses, after the program's
Iop/Ground.lean:1271-1273).        Req.lean:329 over :307-309 -/
def newGroupG (S : Statement) (code maskCode : Nat) : Except String (Statement × Nat) :=
  match newGroupP (dOf S) code maskCode with
  | some (g, d) => .ok (d.st, g)
  | none => .error ("F4-F6: L22: " ++ firstFalse (newGroupL S code maskCode))

/-- What the front hands to the switch and to firstBehind. -/
structure Front where
  st : Statement
  f : ReqFrame
  own : List ReqMessage
  others : Array OracleNotice
  T : SwitchTarget
  /-- how many plain scalars the link sends in front of its first message (the round «REPLY» takes
  them) -/
  plain : Nat

/-- **In front of a later link's switch.**
 [F1] a link's first message is due                        Req.lean:323
 [F2] the shape has the link                               Req.lean:324
 [F3] the groups' list has the link's                      Req.lean:325
 [F0] the link is not link 0 (that call is another lot's)  Req.lean:333, :336 -/
def firstFront (S : Statement) (f : ReqFrame) : Except String Front :=
  if f.next != .first then .error "F1: no first message is due"
  else if f.link == 0 then .error "F0: link 0's first call is a sending, no switch"
  else match f.shape.link[f.link]?, f.groups[f.link]? with
    | some L, some G =>
      let own := f.atMoment 0
      let others := ReqFrame.notices own ++ #[foldMaskNotice (f.foldShape f.link {})]
      match newGroupG S f.shape.code f.shape.maskCode with
      | .error e => .error e
      | .ok (S', g) =>
          .ok ⟨S', { f with group := g, moment := 1, own := #[] }, own, others, G.target, L.plain⟩
    | none, _ => .error "F2: the shape has no such link"
    | _, none => .error "F3: there is no group for the link"

/-- **Behind a later link's switch.** s: what the switch returned. plain: the link's plain scalars.
 [F7]  as many numbers came back as there were announcements          Req.lean:339
 [F8]  the fresh mask's number is among them                          Req.lean:340
 [F9]  as many own messages as numbers                                Req.lean:301
 [G17-G22] each own message joins the group, kept iff it has a life   Req.lean:302-303 over
 Ground.lean:1288-1299 (joinG) -/
def firstBehind (S : Statement) (x : Front) (s : Switched) (plain : List E) :
    Except String (Statement × ReqFrame × Array Nat) :=
  let ids := s.others
  if ids.size != x.others.size then .error "F7: not as many numbers as announcements"
  else match ids[x.own.length]? with
    | none => .error "F8: the fresh mask's number is not there"
    | some mask =>
      let f := { x.f with
        plain := plain, keptBefore := s.kept, mask := some mask,
        atStart := x.f.atStart ++ ids.extract (x.own.length + 1) ids.size }
      let mine := ids.extract 0 x.own.length
      if x.own.length != mine.size then .error "F9: not as many own messages as numbers"
      else
        match (zipT x.own mine.toList).foldlM (fun S y =>
            joinG S f.group y.2 (decide (0 < y.1.life))) S with
        | .error e => .error e
        | .ok S' => .ok (S', { f with own := f.own ++ mine, next := .laterOrClose }, mine)

/-- **In front of the finish's switch.**
 [F10] a first message is due and every link is behind     Req.lean:373
 [F3]  the groups' list has the last test's                Req.lean:374 -/
def finishFront (S : Statement) (f : ReqFrame) : Except String Front :=
  if !(f.next == .first && f.link == f.shape.link.length) then .error "F10: the finish is not due"
  else match f.groups[f.link]? with
    | none => .error "F3: there is no group for the last test"
    | some G =>
      match newGroupG S f.shape.code f.shape.maskCode with
      | .error e => .error e
      | .ok (S', g) =>
        .ok ⟨S', { f with group := g, moment := 1, own := #[] }, [],
            #[foldMaskNotice (f.foldShape f.link {})], G.target, 0⟩

/-- **Behind the finish's switch**: the fresh mask's number, for the last test.
 [F11] the switch returned the mask's number               Req.lean:377 -/
def finishBehind (s : Switched) : Except String Nat :=
  match s.others[0]? with
  | some m => .ok m
  | none => .error "F11: the fresh mask's number is not there"

end Tw.K2
