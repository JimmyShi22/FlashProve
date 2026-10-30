-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/Tw/K2/Cuts.lean: the kind «the code switch», fourth file: THE ROW CUT AS THE
PROGRAM's TEXT IS CUT STEP BY STEP, so that no guard and no write of a step lives outside the kind's
own text.
Plain functions on data; no Blk, no Ctx.
  chainFirstEW   "0.call" at a layers' | attention link that is not link 0: THE WHOLE
  ChainCheck.first (Model/ReqChain.lean:111-114): the walk's firstDue ([W0]: ReqChain.lean:112) ·
  firstEW · the walk's firstKept
                 (:114): two plain texts in a row. State: S9C: as S9, with the program's ChainCheck
                 whole in the frame's place.
  headSwitchEW   "1.call" at the head's link: THE SWITCH ALONE (Iop/Req.lean:337), at the frame that
  "0.front" has made (fr) and the frame in front of it (f0: the group's record and
                 the announcements are read there): [F3] the groups' list has the link's · the
                 announcements as in firstFront (Req.lean:326-328 at a link that is not link 0) ·
                 switchE.
  finishSwitchEW "0.call" at the finish: THE SWITCH ALONE (Req.lean:376), at the frame and the
  group's record that "0.front" has made: one announcement: the fresh mask's · switchE.
AT THE HEAD's LINK "1.quiet" (F7 · F8 · F9 and the own messages' joins) AND AT THE FINISH "0.front"
| "0.quiet" ARE NOT IN THIS FILE: they stand in K2C/Head.lean and K2C/Finish.lean.
Each returns what the step lays into the record (kept · the others' numbers | Switched), the state,
and the columns left.
No soundness: definitions with code.
-/
import Johnson.Top.H0.Tw.K2.Step
import Johnson.Desc.First.Walk.Quiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Tw.K2
open OnBytes OnBytes.Model
open Johnson.Desc.First.Walk (firstDue firstKept)

/-- What crosses the border of "0.call" at a layers' | attention link. -/
structure S9C where
  st : Statement
  book : TreeBook
  roots : Nat
  check : ChainCheck
  settled : Bool := true

/-- What crosses the border of a switch alone. -/
structure S9S where
  st : Statement
  book : TreeBook
  roots : Nat
  settled : Bool := true

def chainFirstEW (behind : SwIn → Except String SwOut) (P : Par9) (send : SendFn) (s : S9C) (rounds
    : List Fmt.RoundView)
    (cols : List Col) : Except String (S9C × List Col) :=
  if !firstDue s.check then .error "W0: no link's first call is due (lot L20's firstDue)"
  else do
    let (t, left) ← firstEW behind P send ⟨s.st, s.book, s.roots, s.check.frame, [],
        s.settled⟩ rounds cols
    -- the program hands firstKept the numbers that ReqFrame.first returns («mine»:
    -- Model/ReqChain.lean:113-114): t.frame.own IS that array: the new group's frame has own := #[]
    -- and firstBehind appends «mine» to it
    pure (⟨t.st, t.book, t.roots, firstKept s.check t.frame t.frame.own, t.settled⟩, left)

def switchAloneEW (behind : SwIn → Except String SwOut) (P : Par9) (send : SendFn) (s : S9S) (x :
    Front)
    (rounds : List Fmt.RoundView) (cols : List Col) : Except String (Switched × S9S × List Col) :=
  match rounds with
  | [rS, rL] => do
    let (w, roots) ← switchE behind P send ⟨s.st, s.book, s.roots, x.f, [], s.settled⟩ x rS rL cols
    pure (w.out, ⟨w.st, w.book, roots, P.eLoc.rows == 0⟩, w.opened)
  | _ => .error "S1: the stretch has not two rounds"

def headSwitchEW (behind : SwIn → Except String SwOut) (P : Par9) (send : SendFn) (s : S9S) (f0 fr :
    ReqFrame)
    (rounds : List Fmt.RoundView) (cols : List Col) : Except String (Switched × S9S × List Col) :=
  match f0.groups[f0.link]? with
  | none => .error "F3: there is no group for the link"
  | some G =>
    let own := f0.atMoment 0
    switchAloneEW behind P send s
      ⟨s.st, fr, own, ReqFrame.notices own ++ #[foldMaskNotice (f0.foldShape f0.link {})], G.target,
          0⟩ rounds cols

def finishSwitchEW (behind : SwIn → Except String SwOut) (P : Par9) (send : SendFn) (s : S9S) (fr :
    ReqFrame)
    (T : SwitchTarget) (rounds : List Fmt.RoundView) (cols : List Col) : Except String (Switched × S9S ×
               List Col) :=
  switchAloneEW behind P send s ⟨s.st, fr, [], #[foldMaskNotice (fr.foldShape fr.link {})], T,
      0⟩ rounds cols

end Tw.K2
