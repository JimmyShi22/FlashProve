-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6DueSplit.lean: THE STRUCTURE OF PREMISES K6DueMg (in
Law/K6LawAtMgAll.lean) CUT IN FOUR, field for field, in its own
words: K6PaidMg: the 14 fields that Law/K06AtConst.lean's paid_at_const shows at the closed
term for the composed meaning's parameters · K6RowMg: the 3 on the maker's piece and the list of
sub-protocols (paid in Law/K06Kind.lean by Law/RowAtConst.lean) · K6StateMg: the 9 on
reached states and on the chain's segment 24 (paid in Law/K06AtHead.lean by
Law/K6StateAtHead.lean) · K6LeftMg: the other 9. Nothing is proved here but that the four give the
whole.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  K6PaidMg: seg · sorts · ns · hid · head · wt · readers · laid · place · lay · uH · treesB · blind
      · roomC.
  K6RowMg: more · blocks · cap.
  K6StateMg: runs3 · reach · back3 · back2 · start · runsObj · back · bare · runs2.
  K6LeftMg: planC · callsC · maskC · tokSmall · seatsC · book · fenceT · numbers · namedC.
  due_of_split: the four give K6DueMg.

The fields' texts and their lines of words are cut by program out of K6DueMg's; Lean holds the texts
against it in due_of_split.
What it does not say. That any part can be met. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K6LawAtMgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Params (ReqLayout ReqShape)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning pubFit pubOfItems bookFit fenceFit)
open VerifiableInference.Desc.Sound (Piece Frame Mem MsgT onQ strsOf openQ pubQ extQAt linksFull
  head_full namedOnce SeatsNamed GroupsSeated KindTiedR PieceMore toldOf out_behind MgData mgAll)
open _root_.Iop (Err)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (c₀ : Fin rows → Fin cols → GE)
  (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ)
  (tokV : Tok → Fin Inst.Model.ppref.V) (req : P × P5J.TS → P5J.TReq)
  (dec : P × P5J.TS → Strs → Option (Fin rows → Fin cols → GE))
  (hN : SeatsNamed D.arr D.N (Meaning.sizesOf Wp) (seatLay Wp lay6 num)) (hG : GroupsSeated D.ms
      D.N) (tab : ℕ → ℕ)
  (tokH : P × P5J.TS → Fin Inst.Model.ppref.V) (Fr : Frame) (tokOf : P × S → Tok)
  (piece6 : ℕ) (Lk : Link S Claim) (small : S → Option K9.Read)
  (x : First.Look.Place) (Rch : ℕ → (P × S) × Fr.E.Str → Prop) (Lp : K12.Door.Laid)
  (Mm : List OracleShape)

set_option quotPrecheck false in
/-- The composed meaning. -/
local notation "MGA" => mgAll D Mg

/-- The driver's list of places, at the full chain. -/
local notation "PS" => First.flatPlacesOf linksFull true

/-- **The fields that fall at the closed term.** -/
structure K6PaidMg : Prop where
  /-- on the public parameters: the head's segment has the number 24 -/
  seg : VerifiableInference.OnPublicFiles.headLink Wp = 24
  /-- the chain's sort of segment 24 is the head's (it gives the map of names at five names) -/
  sorts : D.links[24]? = some .head
  /-- the plan's number of slots at segment 24 is the public parameters' -/
  ns : D.pubD.nsOf 24 = some Wp.H.ns
  /-- the hidden values are the reading at the seats off the layout -/
  hid : D.H = P5J.hidAtSeat Wp D.cs D.arr D.ms D.N (Meaning.sizesOf Wp) (seatLay Wp lay6 num)
    tokV req dec hN hG
  /-- the head's part of the model's relation is headPartK6 -/
  head : D.headPart = headPartK6 D.cs D.arr D.ms D.N (Meaning.sizesOf Wp) (seatLay Wp lay6 num)
    Wp (plAt (num 24 0) 0) tab D.put (Sound.oneDec D.decT D.H) tokH
  /-- the sentence on the claim on the weights is wtK6, under the guard (Law/WtK6.lean) -/
  wt : D.wt = wtK6 D.cs D.arr D.ms D.N Wp lay6 num (num 24 0) 0
  /-- the runs' readers at segment 24 are the link's, with the silent reader in the hole -/
  readers : D.Rd 24 = K9.readersOfLink ⟨small, k6Silent (p8K6 Wp 24) (K9.statesOfLink Lk)⟩ Lk
  /-- a test with code: every element of every matrix is laid -/
  laid : Meaning.laidThere Wp (Meaning.sizesOf Wp) lay6 = true
  /-- x is the place of the lookup on the head's calls -/
  place : headAt Wp = some x
  /-- lay6 is the composed meaning's layout -/
  lay : D.layout = lay6
  /-- the head's arm of the stated data is laid -/
  uH : D.uH 24 = uHeadK6 Wp 24
  /-- the built links' trees at segment 24 are the public parameters' looks -/
  treesB : First.FillSent.treesAt D.built 24 = First.FillSent.looksOf Wp.H.Fp
  /-- the reader of samples and the decoder do not read where the chain stands -/
  blind : Blind D.cs D.smp D.decT
  /-- a test with code (Law/ReadsEntInT.lean): the layout's array of the reads has
      room -/
  roomC : readsRoomC Wp lay6 (D.sent.arrayOf.getD 24 #[]) = true

/-- **The fields on the maker's piece and the list of sub-protocols.** -/
structure K6RowMg (numD : Fmt.TreeSource → Nat) (bs : List (Block (P × S) Claim))
    (q : Piece (_root_.Run.ckP .two) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT)) :
    Prop where
  /-- the maker's piece: its sub-protocol, no rounds behind, the declared rounds, its base -/
  more : PieceMore numD 0 bs 341 q
  /-- a test with code on the sub-protocols -/
  blocks : blocksOk bs = true
  /-- the piece's error is the cap at 128 bits -/
  cap : q.err = Err.cap 128 (uLT (_root_.Run.ckP .two) q.ds)

/-- **The fields on reached states and on the chain's segment 24.** -/
structure K6StateMg : Prop where
  /-- the driver's sub-protocol number 3 of segment 24 states the kind's four runs -/
  runs3 : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) 24 piece6 (K9.statesOfLink Lk) 3
  /-- under Rch alone: no tables are laid; the merge has not laid its end value (see
      Law/K6Reached.lean) -/
  reach : ∀ a, Rch 341 a → a.1.2.failed = none → AtFold.K6Reached a.1.2
  /-- the way back at the driver's sub-protocol number 3 -/
  back3 : K6Back Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) 24 piece6 (K9.statesOfLink Lk) 3
  /-- the way back at the driver's sub-protocol number 2, on the planes -/
  back2 : PlanesBack (readsOf Wp) Wp.hS.lmbH (K9.statesOfLink Lk) 2
  /-- on the state in front: every slot of the leaves' starting form is filled (the lookup's
      LeavesFilled) -/
  start : ∀ a, onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a → Rch 341 a →
    a.1.2.failed = none → VerifiableInference.OnPublicFiles.LeavesFilled a.1.2
  /-- the driver's sub-protocol number 2 states the runs on the objects -/
  runsObj : ObjectsStates (K9.statesOfLink Lk) 2
  /-- the way back at the driver's sub-protocol number 2, on the objects -/
  back : ObjectsBack (K9.statesOfLink Lk) 2
  /-- on the state in front: the rows that the lookup heard name no entry of a read -/
  bare : ∀ a, onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a → Rch 341 a →
    a.1.2.failed = none → ∀ g, a.1.2.lookHeard? = some g → ∀ f ∈ g.rows.toList, f.ents = #[]
  /-- the driver's sub-protocol number 2 states the lookup's run on the planes -/
  runs2 : PlanesStates (readsOf Wp) Wp.hS.lmbH (K9.statesOfLink Lk) 2

/-- **The fields that are left.** -/
structure K6LeftMg (bs : List (Block (P × S) Claim)) : Prop where
  /-- a test with code, by blocks: each of the head's matrices and the mask row sit in one pinned
      member's ranges -/
  planC : OffPad.planK6C D.cs D.arr D.ms D.N Wp lay6 num (num 24 0) 0 = true
  /-- a test with code (Law/K6CallsTest.lean): the matrices that the lookup on the
      head's calls reads sit as planned -/
  callsC : AtFold.callsSeatedC D.arr D.ms D.N Wp lay6 num D.sent D.l3.rad x.link
    (D.l3.seat x.link false) = true
  /-- a test with code (the same file): the mask row sits as planned -/
  maskC : AtFold.maskMeetsC D.arr D.ms D.N D.sent D.l3.rad x.link (D.l3.seat x.link false)
    (num 24 0) Wp.H.ns = true
  /-- on the state in front: what is heard as the reply is an entry of the vocabulary -/
  tokSmall : ∀ a, onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a → Rch 341 a → a.1.2.failed
      = none →
    TokSmall Wp.hS.V a.1.2
  /-- a test with code (Law/K6SeatsTest.lean): the eight matrices, the mask row and
      the array of the reads sit as planned -/
  seatsC : AtFold.seatsK6C D.arr D.N Wp lay6 num (num 24 0) 0 D.cs D.shape D.pubD.dS Lp Mm
    (D.sent.arrayOf.getD 24 #[]) (D.N.msgsAt PS[341]?) = true
  /-- a test with code: the table's numbers against what the sub-protocols tell -/
  book : bookFit D.N PS (toldOf bs) = true
  /-- a test with code: the table's fences -/
  fenceT : fenceFit D.N linksFull PS = true
  /-- the piece sends nothing: the numbers of trees and of messages stay -/
  numbers : D.N.treesAt PS[341 + 1]? = D.N.treesAt PS[341]? ∧
    D.N.msgsAt PS[341 + 1]? = D.N.msgsAt PS[341]?
  /-- a test with code (Law/PlanK6Planes.lean): the planes' matrix's message is named
      once -/
  namedC : OffPad.namedAtC D.arr D.N Wp lay6 num (Wp.hS.NHf + 2) = true

/-- **The four give the whole.** -/
theorem due_of_split (bS : Block S Claim) (numD : Fmt.TreeSource → Nat)
    (bs : List (Block (P × S) Claim))
    (q : Piece (_root_.Run.ckP .two) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT))
    (A : K6PaidMg D lay6 num tokV req dec hN hG tab tokH Lk small x)
    (R : K6RowMg Fr numD bs q)
    (T : K6StateMg D Mg Fr piece6 Lk Rch)
    (L : K6LeftMg D Mg lay6 num Fr x Rch Lp Mm bs) :
    K6DueMg D Mg lay6 num tokV req dec hN hG tab tokH Fr piece6 Lk small x Rch Lp Mm bS numD bs q :=
  { seg := A.seg
    sorts := A.sorts
    ns := A.ns
    hid := A.hid
    head := A.head
    wt := A.wt
    readers := A.readers
    laid := A.laid
    planC := L.planC
    runs3 := T.runs3
    place := A.place
    lay := A.lay
    callsC := L.callsC
    maskC := L.maskC
    tokSmall := L.tokSmall
    seatsC := L.seatsC
    uH := A.uH
    reach := T.reach
    treesB := A.treesB
    more := R.more
    blocks := R.blocks
    book := L.book
    fenceT := L.fenceT
    numbers := L.numbers
    blind := A.blind
    roomC := A.roomC
    back3 := T.back3
    back2 := T.back2
    start := T.start
    cap := R.cap
    runsObj := T.runsObj
    back := T.back
    bare := T.bare
    namedC := L.namedC
    runs2 := T.runs2 }

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.due_of_split
