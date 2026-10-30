-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameLot.lean: the link's frame as one value that can be handed to a fold over
blocks: a list, one record a link, of the frame's three functions at that link's letters.

  LinkFrame   link; steps: the steps of verify-on-bytes that the frame takes at that link, by
              their full names; plan: the tests on the plan alone of "opened" (a block's planOk;
              lay and clear have none: without this field the frame's tests on the plan would be
              asked nowhere); lay, opened, clear; last: the piece of the link's "cleared"
  rowOf       the pending row's function: pendingRowO (Johnson/Desc/First/Pend/Row.lean), by name
  zeroAt      link 0's letters
  fvsOf       for each link of the chain: does its record leave a row
  headFrame   the frame at the head's link: lay is layFront; "opened" hands the record on (the
              head's front is the code switch's own); clear is tailHead
              (Johnson/Desc/First/Close/TailHead.lean); plan is planFlag at the head's kind.
              headFrame_lay, headFrame_clear: by rfl
  framesOf    the value: at link 0: layFront 0, openLayZero, clearWith; at every other layers' or
              attention link: layFront l, openLay or openAtt, clearWith; at the head's link:
              headFrame. It returns Except String: a link whose letters are not there refuses
              ("no plan"): it does not pass in silence

No test lives here: letters are read off the built records of the program `verify-on-bytes`'s model
(Stages.LinkH; Verify.Public, OnBytes/Model/VerifyPublic.lean; Params.First), by FrameSeat.lean and
here, and handed to Johnson/Desc/First/Walk/Frame.lean and FrameZero.lean.
last: Block.lean's Link.blocksInOrder numbers a link's blocks from 0: "laid", the hearing blocks, the
batching, the block behind it, the closing blocks, "cleared". With seven hearing blocks and three
closing blocks "cleared" is piece 13; at the head's link, with nine hearing blocks, 15.

-/
import Johnson.Top.H0.Walk.FrameSeat
import Johnson.Desc.First.Walk.FrameZero
import Johnson.Desc.First.Pend.Row
import Johnson.Desc.First.Close.TailHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Seat
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

/-- The frame at one link. -/
structure LinkFrame where
  link : Nat
  /-- the steps of verify-on-bytes that it takes, by their full names -/
  steps : List String
  /-- «opened»'s tests on the plan alone -/
  plan : Bool
  lay : S → Except String S
  opened : S → Except String S
  clear : S → Except String S
  /-- the piece of the link's «cleared» in the fold's own count of a link's pieces (Block.lean's
  Link.blocksInOrder: the hearing places, the closing places and three): 13 at a layers' or an attention link
  -/
  last : Nat := 13

/-- The pending row's function: pendingRowO (Johnson/Desc/First/Pend/Row.lean), by name. -/
def rowOf (W : Verify.Public) (first : Params.First) : RowFn := fun im w n os =>
  VerifiableInference.Desc.First.Pend.pendingRowO W.layers.wsLay im w n first.lin os

/-- Link 0's letters. -/
def zeroAt (built : Array Stages.LinkH) (W : Verify.Public) : Option LayPar := do
  let X ← built[0]?
  if X.kind != 0 then none
  let hp ← W.G[X.g]?
  pure ⟨pubOf X, 0, W.layers.y.h.p4, X.g, hp.Tp, hp.Fp, hp.ns, hp.tl⟩

/-- For each link of the chain: does its record leave a row. -/
def fvsOf (built : Array Stages.LinkH) : List Bool := built.toList.map (·.fv)

/-- The frame at the head's link: the front test as at every link; nothing is laid behind the first
call here; the end is tailHead (Johnson/Desc/First/Close/TailHead.lean). -/
def headFrame (X : LinkPub) (l : Nat) (first : Params.First) (W : Verify.Public) : LinkFrame :=
  { link := l, steps := [X.name ++ ".10.quiet"], plan := planFlag X 2
    lay := layFront l, opened := fun s => .ok s
    clear := VerifiableInference.Desc.First.Close.tailHead X W.layers.wsLay first.lin
    last := 15 }

theorem headFrame_lay (X : LinkPub) (l : Nat) (first : Params.First) (W : Verify.Public) :
    (headFrame X l first W).lay = layFront l := rfl

theorem headFrame_clear (X : LinkPub) (l : Nat) (first : Params.First) (W : Verify.Public) :
    (headFrame X l first W).clear = VerifiableInference.Desc.First.Close.tailHead X W.layers.wsLay
        first.lin := rfl

/-- **The frame, link by link.** -/
def framesOf (built : Array Stages.LinkH) (first : Params.First) (W : Verify.Public) : Except String
    (List LinkFrame) :=
  (List.range built.size).mapM fun l =>
    let names := fun (X : LinkPub) => [X.name ++ ".0.quiet", X.name ++ ".8.quiet"]
    if ((built[l]?).map fun X => X.kind == 2).getD false then
      match built[l]? with
      | none => .error s!"no plan: link {l}'s letters are not there"
      | some X => .ok (headFrame (pubOf X) l first W)
    else if l == 0 then
      match zeroAt built W with
      | none => .error "no plan: link 0's letters are not there"
      | some P =>
        .ok { link := 0, steps := names P.X, plan := planLayZero first.shape P
              lay := layFront 0, opened := openLayZero P (fvsOf built) first.lin.kCol
              clear := clearWith P.X (countsLay P.tl₀.NM) leftLay (rowOf W first) }
    else
      match frameAt built W l with
      | none => .error s!"no plan: link {l}'s letters are not there"
      | some (.att P nLin) =>
        .ok { link := l, steps := names P.X, plan := planAtt first.shape P
              lay := layFront l, opened := openAtt P, clear := clearWith P.X (countsAtt nLin) (fun _
                  => none) (rowOf W first) }
      | some (.lay P) =>
        .ok { link := l, steps := names P.X, plan := planLay first.shape P
              lay := layFront l, opened := openLay P, clear := clearWith P.X (countsLay P.tl₀.NM)
                  leftLay (rowOf W first) }

end Johnson.Desc.First.Walk.Seat
