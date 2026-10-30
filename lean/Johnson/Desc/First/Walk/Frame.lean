-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Walk/Frame.lean: the link's frame at the one carried record: what the fold over
blocks does itself at a link's two ends, as plain functions S → Except String S over Quiet.lean and
FirstQuiet.lean, in the form of Johnson/Desc/Block.lean's Link: lay, clear; and one quiet block
between.

Why three and not two. Link.blocksInOrder lays "laid" in front of the link's first place. The program
`verify-on-bytes` lays the link's part behind the link's first call: so nothing can be laid in
front. lay asks what can be asked there; "opened" lays. "opened" is the second half of the link's
first place, by Block.andThen.

  layFront l            in front of the first call: tests alone: no link is open in the record [B];
                        no link runs and one is still to come [W0]; the chain stands at this link
                        [W2: the first call does not turn that number: OnBytes/Iop/Req.lean:322-346]
  openAtt | openLay     behind the first call: the whole steps attFirstQuiet | layFirstQuiet at S:
                        they read check and out and lay the link's part
  planAtt | planLay     the tests on the plan alone that stand in these steps: W1 in its public form
                        (behind a true first call the number of plain scalars is the request's
                        shape's: Req.lean:324, :330), Q0, G1, G2; and planFlag: the record's kind
                        is the link's, and its flag "a row is left" fits the kind
  countsLay | countsAtt the kinds' own counts that that verifier asks in front of the frame's
                        closing lines: the batching's and attention's ground, not the frame's:
                        typed here after its text (Layer: the three tests behind doorH;
                        Attention.countsHeld, OnBytes/Model/Attention.lean:155-161;
                        Fork.kapAllTakenF, Hide.lean:341; HTailF2.foldAllTakenF, Tail.lean:790;
                        groupsRun, :344 written out)
  clearWith             behind the closing: the counts; back [W3, W4, W5]; the pending row laid on
                        the pile; the link's part dropped, the live state of the calls taken back

Each guard refuses under its own name. A refusal of Quiet.lean's or FirstQuiet.lean's text (W1 ...
W5, G1, G2, Q0) goes on under that text's own words; the frame's own tests are named B (a link is
open where none may be), A, W0, W2, N (no link with its fork is open where one must be); each count
C0 ... C6; a refusal of the pending row's function under "ROW: " and its own word. The entering and
the leaving go by State.lean's forms that refuse at once (enterAtt?, enterLay?, leaveLink?): where
the record bears a mark, or the function would lay one, the block refuses under the mark's own
name.

Two tests that that verifier has by the order of its lines and by its local variables, and that a
record's blank would else forgive:
  [A]  "opened": the link's first call has run: the state of the calls stands in a link, at its
       first moment (StagesLinks.lean:560 stands in front of :566)
  [C0] the counts at a layers' link: the smallness test's record has the number of matrices of the
       plan's record tl₀, which the entering lays (Layer.lean:594 makes it of the plan's). Of a
       record without a matrix C3 asks nothing.

Limits.
What the sub-proof left for its row is there only when it has been laid (an Option): so leftLay can
have nothing, and W5 can speak at a layers' link: seen at a toy alone; not run on a proof. A blank
value left for the row is refused by the row's own test ("ROW: link-claim-count":
Johnson/Desc/First/Pend/Row.lean).
This text (the forms that refuse at once; tl₀; the Option) has not run on a proof.
Every guard is on public numbers or on marks of the order of steps.
No round, no column. No Blk, no Ctx, no SubM, no LinkM in any type of this file; on the records'
homes see Quiet.lean's head.
No soundness: definitions with code.

-/
import Johnson.Desc.First.Walk.FirstQuiet
import Johnson.Desc.First.State
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block roundlessBlock need)
open VerifiableInference.Desc.First (S)

/-- The plan's letters for an attention link. -/
structure AttPar where
  X : LinkPub
  /-- the link's number -/
  l : Nat
  /-- the plan's number of slots -/
  ns : Nat
  /-- the plan's record of the smallness test -/
  tl₀ : HTailF2

/-- The plan's letters for a layers' link. -/
structure LayPar where
  X : LinkPub
  l : Nat
  /-- attention links stand between the layers' -/
  p4 : Bool
  /-- the group -/
  g : Nat
  /-- the sub-proof's plan: its list, its planned fork, its number of slots -/
  Tp : Tail2
  Fp : Fork
  ns : Nat
  /-- the plan's record of the smallness test, its list of tables open -/
  tl₀ : HTailF2

/-- **Link.lay.** In front of the link's first call: tests alone. -/
def layFront (l : Nat) (s : S) : Except String S := do
  need "B: a link is open in the record" s.atBetween
  need "W0: no link's first call is due" (firstDue s.check)
  need "W2: the chain does not stand at this link" (s.check.frame.link == l)
  pure s

/-- The link's first call has run.                                                ReqChain.lean:114
  (what ChainCheck.first writes) -/
def firstRun (c : ChainCheck) : Bool := c.inLink && c.moments == 1

/-- Behind an attention link's first call. -/
def openAtt (P : AttPar) (s : S) : Except String S := do
  need "B: a link is open in the record" s.atBetween
  need "A: the link's first call has not run" (firstRun s.check)
  let a ← attFirstQuiet P.X P.l P.ns P.tl₀ s.check s.out
  S.enterAtt? { s with out := a.out } a.L a.F a.tl

/-- Behind a layers' link's first call. -/
def openLay (P : LayPar) (s : S) : Except String S := do
  need "B: a link is open in the record" s.atBetween
  need "A: the link's first call has not run" (firstRun s.check)
  let a ← layFirstQuiet P.X P.l P.p4 P.g P.Tp P.Fp P.ns s.check s.out
  S.enterLay? { s with out := a.out } a.L a.F P.tl₀

/-- W1 as a test on the plan: the request's shape sends one plain scalar at the head's link, none at
  any other. -/
def planPlain (shape : Params.ReqShape) (X : LinkPub) (l : Nat) : Bool :=
  (shape.link[l]?).map (·.plain) == some (if X.kind == 2 then 1 else 0)

/-- The record is of the kind of the link at which it is used (0: layers; 1: attention; 2: the
  head), and its flag "a row is left" fits the kind: every link but an attention link leaves a row.
  WHY: "cleared" lays the link's pending row where the flag says so. At a layers' record whose flag
  said no, it would leave the link and lay no row, in silence: what the sub-proof has left for the
  weights would be dropped. -/
def planFlag (X : LinkPub) (kind : Nat) : Bool := X.kind == kind && X.fv == (kind != 1)

/-- The tests on the plan alone at an attention link. -/
def planAtt (shape : Params.ReqShape) (P : AttPar) : Bool :=
  P.l != 0 && planPlain shape P.X P.l && planFlag P.X 1

/-- The tests on the plan alone at a layers' link behind link 0. -/
def planLay (shape : Params.ReqShape) (P : LayPar) : Bool :=
  P.l != 0 && planPlain shape P.X P.l && P.l == (if P.p4 then 2 * P.g else P.g) &&
    P.X.Tp.nt == P.Tp.nt && sizes P.X.Fp == sizes P.Fp && planFlag P.X 0

/-- «‹link›: opened» as a block without a round. -/
def openedBlock {Cl : Type} (name : String) (l piece : Nat) (plan : Bool) (f : S → Except String S)
    : Block S Cl :=
  { roundlessBlock (name ++ ": opened") 1 (some l) piece f with planOk := plan }

/-- Every claim of the plan has had its weight handed out.                       after
  Fork.kapAllTakenF, Hide.lean:341-342 -/
def weightsOut (F : Fork) : Bool := F.kapMapF.size == F.planClaimsF && F.kapMapF.all id

/-- Every matrix has had its call of the fold's sums.                             after
  HTailF2.foldAllTakenF, Tail.lean:790-791 -/
def foldsOut (tl : HTailF2) : Bool := tl.foldTakenF.size == tl.NM && tl.foldTakenF.all id

/-- The counts at a layers' link's end.                                           the three tests in
  front of the frame's lines -/
def countsLay (NM : Nat) (s : S) : Except String Unit :=
  match s.here with
  | .lay a => do
    need "C0: the smallness test's record has not the plan's number of matrices" (a.tl.NM == NM)
    need "C1: the claims added are not as many as the plan's" (a.F.nClaim == a.F.planClaimsF)
    need "C2: a claim's weight has not been handed out" (weightsOut a.F)
    need "C3: a matrix has not had its call of the fold's sums" (foldsOut a.tl)
  | _ => .error "N: no layers' link is open in the record"

/-- The counts at an attention link's end. nLin: the plan's number of claims.     after
  Attention.countsHeld, Attention.lean:155-161 -/
def countsAtt (nLin : Nat) (s : S) : Except String Unit :=
  match s.here with
  | .att a => do
    need "C1: the claims added are not as many as the plan's" (a.F.nClaim == a.F.planClaimsF)
    need "C2: a claim's weight has not been handed out" (weightsOut a.F)
    need "C3: a matrix has not had its call of the fold's sums" (foldsOut a.tl)
    need "C4: the claims added are not attention's number" (a.F.nClaim == nLin)
    need "C5: not just one matrix was drawn" (a.tl.foldDrawn == 1)
    need "C6: the lookup on the digits has not run" a.tl.heard.isSome
  | _ => .error "N: no attention link is open in the record"

/-- What a layers' sub-proof left for its row. -/
def leftLay (s : S) : Option WsForkOut :=
  match s.here with
  | .lay a => a.own.map (·.wo)
  | _ => none

/-- **Link.clear.** Behind the closing. counts: the kind's own counts in front of the frame's lines.
  left: what the sub-proof left for its row. row:
the pending row's function. -/
def clearWith (X : LinkPub) (counts : S → Except String Unit) (left : S → Option WsForkOut) (row :
    RowFn) (s : S) : Except String S :=
  match s.link?, s.fork? with
  | some C, some F => do
    counts s
    match ← back X (left s) C F with
    | (_, none) => s.leaveLink?
    | (_, some w) =>
      match row s.out.indexMasks w X.NCL s.st.oracles with
      | .error e => .error ("ROW: " ++ e)
      | .ok (r, os) => ({ s with out := pendingKept s.out r, st := { s.st with oracles := os } } :
          S).leaveLink?
  | _, _ => .error "N: no link with its fork is open in the record"

end Johnson.Desc.First.Walk
