-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/Tw/K2C/Head.lean: TWO QUIET STEPS AT THE HEAD's LINK, AS PLAIN FUNCTIONS AT THE
CARRIED RECORD S: "H.0.front" (the first half of the place «H:1», whose second half is the round
«REPLY») AND "H.1.quiet" (the second half of the code switch's place «H:2»).
The record enters and opens the head's link by S.enterHead? | S.openHead?, the forms that refuse at
once: a record that comes in marked is refused here, under its mark. Each refusal under its guard's
name. definitions with code; no theorem. At every other link these lines stand in the
switch's own step and in the walk's «opened»; at the head's link the round «REPLY» parts them.
  headFrontQ  [B0] the record stands between the links · [W0] a link's first call is due (the walk's
  firstDue; Model/ReqChain.lean:112) · [F1] [F0] [F2] [F3] and the new group [F4-F6: the plain
  ground's newGroupP]: firstFront (Iop/Req.lean:323-325, :307-309) ·
              the record enters the head's link, with the plan's tail tl (a letter), and holds the
              frame behind the new group
  headOpenQ   THREE TEXTS MEET IN THIS STEP:
    (the switch's)  [Q0] the link is not opened yet · [Q1] it is not link 0 (whose index masks are
    not treated here) · firstBehind: [F7] [F8] [F9] and the own messages' joins [G17-G22: the plain
    ground's joinP]      Iop/Req.lean:339-345 over :301-303
    (the walk's)    THE HEARD REPLY HAS ONE SEAT, S.out.reply, laid by the block of the round
    «REPLY» at «H:1»: this step READS it (s.out.reply.toList goes into the frame as the link's plain
    scalars) and leaves S.out as it was · firstKept: the end of ChainCheck.first · front: [W1] one
    plain scalar was heard (a reply lies in the seat) · it lays the same reply back · [W2] the walk
    stands at the record's link · the link's context   Model/ReqChain.lean:113-116 ·
    Model/StagesLinks.lean:566-570
    (the reply's)   [Y0] just one plain scalar · [Y1] «header-y»: it lies in the base field and is
    an entry of the vocabulary (Model/HeadHeard.lean:63-67: replyToken, WRITTEN ANEW: three lines) ·
    the fork from which the sub-proof starts (the walk's weightsAtZero |
               emptySlots at the record's planned arrays) · (the token that is checked at each
               covered position is no field of the record: whoever checks it makes it of
               the covered positions and the reply's seat)
  headPlanOk  THE TESTS ON THE PLAN ALONE that the program asks at this place (Model/Head.lean:
  runForkHidH2's head): [P1] the plan that is handed is the record's (handedOk, this file's own
  text) · [P2] the last layers' group's plan has
              a stream's table, and its last key is the border's · [P3] the head's plan has its
              third index: THE BLOCK's planOk: A FUNCTION OF THE LETTERS, IN THIS FILE.
  THE COVERED POSITIONS ARE NO LETTER: they are read off the record (S.covered: of the request's
  public words and THE HEARD REPLY): [C1] they can be made · [C0] their arrays have the length T
  (sizedOk, this file's own text; behind [C1] it cannot fail: S.covered makes its arrays at that
  very T).
No round, no column. No Blk, no Ctx, no SubM, no LinkM in any type of this file. No soundness.

-/
import Johnson.Top.H0.Tw.K2C.Kind
import Johnson.Desc.First.Walk.FirstQuiet
import OnBytes.Model.HeadHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block roundlessBlock)
open Johnson.Desc.First.Walk (LinkPub front firstDue firstKept weightsAtZero emptySlots)

/-- What of a planned array is compared: its name, rows, columns and number of virtual rows. -/
def arraySig (X : HTree) : String × Nat × Nat × Nat := (X.name, X.R, X.K, X.rows.size)

/-- [P1] What is handed to the head's sub-proof agrees with the plan hp: the list of arrays is
closed and has hp's records, and the arrays are, one by one and in order, hp's by name, rows,
columns and number of virtual rows. -/
def handedOk (hp : Head.HPlanH2) (list : Tail2) (F : Fork) : Bool :=
  list.planned && list.nt == hp.Tp.nt && F.trees.map arraySig == hp.Fp.trees.map arraySig

/-- [C0] Each of the four arrays of the covered positions has one entry for each of T positions. -/
def sizedOk (c : Head.Covered) (T : Nat) : Bool :=
  c.tokv.size == T && c.hOn.size == T && c.hWin.size == T && c.hOnC.size == T

/-- **"H.0.front".** -/
def headFrontQ (tl : HTailF2) (s : S) : Except String S :=
  if !s.atBetween then .error "B0: the record does not stand between the links"
  else if !firstDue s.check then .error "W0: no link's first call is due (lot L20's firstDue)"
  else (_root_.Tw.K2.firstFront s.st s.check.frame).bind fun x =>
    (s.enterHead? tl).bind fun s₁ =>
      match s₁.here with
      | .head a => .ok { s₁ with st := x.st, here := .head { a with fr := x.f } }
      | _ => .error "B3: the record has not entered the head's link"

/-- The plan's letters for the head's link. -/
structure HeadPar where
  X : LinkPub
  /-- the link's number -/
  l : Nat
  /-- the vocabulary's size · the number of positions -/
  V : Nat
  T : Nat
  /-- the head's plan (its number of slots: hp.ns) -/
  hp : Head.HPlanH2
  /-- the plan of the last group of layers -/
  O : Head.Owner
  /-- the border's key of the stream's table -/
  kxb : Nat

/-- THE TESTS ON THE PLAN ALONE at "H.1.quiet", each with its name. -/
def headPlanTests (P : HeadPar) : List (String × Bool) :=
  [("P1: the plan that is handed is not the record's", handedOk P.hp P.X.Tp P.X.Fp),
   ("P2: the last layers' group's plan has no stream's table, or its last key is not the border's",
       !P.O.tl.ix.TX.isEmpty && P.O.tl.kTX.back? == some P.kxb),
   ("P3: the head's plan has no third index", (P.hp.tl.ix.U.getD 2 none).isSome)]

def headPlanOk (P : HeadPar) : Bool := (headPlanTests P).all (·.2)

/-- **"H.1.quiet".** -/
def headOpenQ (P : HeadPar) (s : S) : Except String S :=
  match s.here with
  | .head a =>
    if a.opened then .error "Q0: the link counts as opened already"
    else if P.l == 0 then .error "Q1: link 0's index masks are another lot's" else
    let f0 := s.check.frame
    let own := f0.atMoment 0
    -- the last two (the target; the number of plain scalars) are never read by firstBehind: dead
    let x : _root_.Tw.K2.Front :=
        ⟨s.st, a.fr, own, ReqFrame.notices own ++ #[foldMaskNotice (f0.foldShape f0.link {})],
            default, 0⟩
    (_root_.Tw.K2.firstBehind s.st x { (default : Switched) with kept := a.kept,
                                                                 others :=
                                                                     a.ids }
                                                                         s.out.reply.toList).bind
                                                                             fun (st, f, mine) =>
      let check := firstKept s.check f mine
      (front P.X P.l check s.out).bind fun (L, out) =>
        match s.out.reply with
        | some y =>
          if !(y.c1 == 0 && y.c2 == 0 && Decidable.decide (y.c0.toNat < P.V)) then
              .error "Y1: header-y: the plain scalar is no entry of the vocabulary" else
          match ({ s with out := out } : S).covered P.T P.V with
          | .error e => .error ("C1: the covered positions cannot be made: " ++ e)
          | .ok cov =>
            if !sizedOk cov P.T then
                .error "C0: the covered positions' arrays have not the length T" else
            s.openHead?.bind fun s₁ =>
            match s₁.here with
            | .head b =>
              .ok { s₁ with
                st := st, check := check, out := out
                here := .head { b with
                  L := L, F := emptySlots (weightsAtZero { trees := P.X.Fp.trees }) P.hp.ns } }
            | _ => .error "B2: the record stands at another sort of place than the block"
        | none => .error "Y0: no reply lies in the seat"
  | _ => .error "B2: the record stands at another sort of place than the block"

/-- «H:2»'s second half as a block without a round. -/
def headOpened {Cl : Type} (name : String) (place : VerifiableInference.Desc.Place) (P : HeadPar) :
    Block S Cl :=
  { roundlessBlock (name ++ ": opened") place.chain place.link place.piece (headOpenQ P) with
      planOk := headPlanOk P }

end VerifiableInference.Desc.First.K2
