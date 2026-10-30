-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/U3Fit/SeatsAtHead.lean

Definitions and theorems on the seats of the arrays "U3" and "BZ" ("seatsOf",
Johnson/HonestTrace/SeatOf.lean) and on the public test "u3AllFit"
(Johnson/HonestTrace/U3Rows.lean). Public data alone: the table of steps, the codes, a request's
shape and its layout. A SegVals is carried whole; its field vec, a function that awaits the trace's
cells, is applied nowhere here.

Terms, for every file of this folder. "The head" is the premise h : "P5J.AtMgA OnBytes.secondHashFunction W D r
Zp Np cF x" (Johnson/P5J/MgAtAll.lean); G is a ground with hG : "ProofFile.blankBy ProofFile.pureRoad.links Zp =
some G"; under the head there is one ("ProofFile.Honest.K6.head_ground_at_head",
Johnson/Desc/ProofFile/Honest/K6/Law/RowsSeated.lean). The model's last part is "the output head".

Main definitions:
* "seatBy", "seatsBy": the text of "seatOf" and "seatsOf" typed a second time, as functions of five
  public values, so that Lean's kernel can evaluate them; "seatsW": at the five written values.
* "seatHalf", "valsHalf": the two halves of "u3Fits"; "valsHalf" is the one that asks "valsAt".
  "u3SeatsFit": every segment seated, no two seats of one address, "seatHalf" at each seat.
* "addrsAgree", "laterSeated": two tests, on the seats' addresses and on the later messages.

Main theorems:
* "seatsOf_by" (no head): where "spotsOf Z.cuts" returns, "seatsOf" is "seatsBy" at Z's and G's own.
* "seats_at_head": under the head "seatsOf Zp G name = seatsW name", for every name.
* "u3AllFit_halves" (no head): "u3AllFit" is "u3SeatsFit" and "valsHalf" at every seat.
* "u3SeatsFit_at_head", "addrsAgree_at_head", "laterSeated_at_head": under the head each says yes.

Limits. The head is a premise: the full size and the format's second hash function ("OnBytes.secondHashFunction") alone.
It has a member at the stored full-size files ("AtFullSide.Top.headMember_zFull",
AtFullSide/Top/HeadMemberAtFull.lean; see that file's limits). Six closed facts (three tests at
written values, and a control for each, "…_can_fail") are shown by "decide +kernel", each under
"set_option maxRecDepth 1000000", which raises the elaborator's depth of recursion. A control shows
that its test can say no; it need not turn every clause: four clauses of "seatsFitBy" are turned by
none: the one that bars a shared address, and "seatFits", "layFits", "msgFits". "addrsAgree" and
"laterSeated" test this file's own text: no lemma ties the frame that "addrsAgree" builds to the one
with which the places of the kind K2 are made, and no other file of this folder calls the two.
Not claimed: anything on "valsAt", so "u3AllFit = true" does not follow; anything on the messages of
moment 0 or on what a message holds. No property of a release, of a verifier or of a prover is
claimed.
-/
import Johnson.HonestTrace.U3Rows
import Johnson.AtFull.Desc.SpotsWritten
import Johnson.Desc.First.Att.Row.K5FrontOne
import Johnson.HB.LLHARD.PlanInScope
import Johnson.Desc.K1.Law.PinsAtHead
import Johnson.IMR.ArraysOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.U3.Fit

open OnBytes OnBytes.Model
open ProofFile (Pub Ground Spot spotsOf)
open ProofFile.Honest (MsgAddr msgFits layFits)
open ProofFile.Honest.K2 (sendersOf addrOf)
open OnBytes.Params (ReqArray ReqLayout ReqShape)
open VerifiableInference.Desc.First (Cut)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (codesFull2 layoutFull)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Desc (spotsWritten)
open P5J (AtMgA TS)

/-! ## 1 The seats as a function of five public values -/

/-- "seatOf" of the reader of the rounds in front of a step, the places, the codes, the shape and the
layout. -/
def seatBy (before : String → Option Nat) (sps : List Spot) (codes : OnBytes.Codes) (shape : ReqShape)
    (lay : ReqLayout) (name : String) (seg : Nat) : Option Seat := do
  let layout := lay.link.getD seg []
  let a ← layout.find? fun a => a.name == name
  let L ← shape.link[seg]?
  let M ← L.messages[a.message]?
  let x ← inSending L a.message
  let code ← codes.base[M.shape.code]?
  if x.1 == 0 then none
  else
    let pl ← (sendersOf sps seg)[x.1]?
    let sp ← sps.find? fun sp => sp.place == pl
    let c ← sp.cuts.head?
    let n ← before c.look
    pure ⟨seg, L, layout, a, M.shape, code.ell, ⟨⟨pl, 0⟩, x.2⟩, n⟩

/-- "seatsOf", the like, at places that are handed in. -/
def seatsBy (before : String → Option Nat) (sps : List Spot) (codes : OnBytes.Codes)
    (shape : ReqShape) (lay : ReqLayout) (name : String) : List Seat :=
  (List.range shape.link.length).filterMap (seatBy before sps codes shape lay name)

/-- **GENERAL: where the table's places are sps, the seats are "seatsBy" at Z's own reader of the rounds in
front, sps, and the ground's codes, shape and layout.** -/
theorem seatsOf_by {Z : Pub} {G : Ground} {sps : List Spot} (hs : spotsOf Z.cuts = some sps)
    (name : String) :
    seatsOf Z G name =
      seatsBy Z.roundsBefore? sps G.first.codes G.first.shape G.first.layout name := by
  have e : seatOf Z G sps name =
      seatBy Z.roundsBefore? sps G.first.codes G.first.shape G.first.layout name := by
    funext seg
    rfl
  unfold seatsOf seatsBy
  rw [hs]
  show List.filterMap (seatOf Z G sps name) _ = _
  rw [e]

/-! ## 2 Under the head the five are the written ones -/

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head the table of steps is the written one. -/
theorem cuts_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) : Zp.cuts = cutWritten := 
  H2K5.Row.cuts_made h.laid.pub
    (VerifiableInference.PlanWritten.Joined.proof_plans_in_scope h.scope h.laid.pub (VerifiableInference.Desc.K1.pin1_atAll h))

/-- So its reader of the rounds in front of a step is the library's "roundsBy" at the written table's pairs
(Johnson/Desc/First/Att/Row/K5RowTwins.lean, K5BeforeClosed.lean). -/
theorem before_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) :
    Zp.roundsBefore? = H2K5.Row.roundsBy H2K5.Row.cutPairsW := by
  funext look
  rw [H2K5.Row.roundsBefore_by, cuts_at_head h]
  rfl

/-- So its places are the written ones. -/
theorem spots_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) :
    spotsOf Zp.cuts = some spotsWritten := by
  rw [cuts_at_head h]
  exact Johnson.AtFull.Desc.spots_written

/-- Under the head a blank ground's codes, shape and layout are the written ones. -/
theorem first_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) :
    G.first.codes = codesFull2 ∧ G.first.shape = proofSizedFull.request ∧
      G.first.layout = layoutFull := by
  have hF := VerifiableInference.Desc.K13.Law.likeFull_in_scope h.scope h.laid.pub (VerifiableInference.Desc.K1.pin1_atAll h)
  have hL := VerifiableInference.PlanWritten.Joined.layout_in_scope h.scope h.laid.pub (VerifiableInference.Desc.K1.pin1_atAll h)
  rw [Meaning.K2.blank_first hG]
  exact ⟨hF.codes, hF.shape, hL⟩

/-- The seats of the array of a name at the five written values. -/
def seatsW (name : String) : List Seat :=
  seatsBy (H2K5.Row.roundsBy H2K5.Row.cutPairsW) spotsWritten codesFull2 proofSizedFull.request layoutFull
    name

/-- **UNDER THE HEAD THE SEATS OF EVERY NAME ARE THE WRITTEN VALUES' SEATS.** -/
theorem seats_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (name : String) :
    seatsOf Zp G name = seatsW name := by
  obtain ⟨e1, e2, e3⟩ := first_at_head h hG
  rw [seatsOf_by (spots_at_head h) name, before_at_head h, e1, e2, e3]
  rfl

/-! ## 3 "u3AllFit" in two halves -/

/-- Of "u3Fits": what reads the seat, the codes, the shape and the layout alone. -/
def seatHalf (codes : OnBytes.Codes) (shape : ReqShape) (lay : ReqLayout) (s : Seat) : Bool :=
  seatFits s && layFits shape lay && msgFits codes shape lay s.seg s.array.message &&
    s.array.sizeI == 1 && s.shape.mainDeg == 3

/-- Of "u3Fits": the segment's maker returns; its rounds end where the sending begins; its number of
reads is the array's columns. -/
def valsHalf (Z : Pub) (G : Ground) (cov : Head.Covered) (s : Seat) : Bool :=
  match valsAt Z G cov s.seg with
  | .ok V => V.front == s.heard && s.array.sizeC == V.n
  | .error _ => false

/-- A helper: a step that cannot reject, behind x, rejects where x does. -/
theorem isNone_then_pure {α β : Type} (x : Except String α) (v : β) :
    (errOf (x >>= fun _ => (pure v : Except String β))).isNone = (errOf x).isNone := by
  cases x <;> rfl

/-- A helper: "seatAsks" accepts just where its four tests do. -/
theorem seatAsks_isNone (s : Seat) (V : SegVals) :
    (errOf (seatAsks s V)).isNone =
      (V.front == s.heard && s.array.sizeI == 1 && s.array.sizeC == V.n &&
        s.shape.mainDeg == 3) := by
  unfold seatAsks
  cases V.front == s.heard <;> cases s.array.sizeI == 1 <;> cases s.array.sizeC == V.n <;>
    cases s.shape.mainDeg == 3 <;> rfl

/-- **GENERAL: the test at a seat is its two halves.** -/
theorem u3Fits_halves (Z : Pub) (G : Ground) (cov : Head.Covered) (s : Seat) :
    u3Fits Z G cov s =
      (seatHalf G.first.codes G.first.shape G.first.layout s && valsHalf Z G cov s) := by
  unfold u3Fits u3FitsWhy seated seatHalf valsHalf seatFits
  cases seatWhy s with
  | some e => rfl
  | none =>
    cases layFits G.first.shape G.first.layout with
    | false => rfl
    | true =>
      cases msgFits G.first.codes G.first.shape G.first.layout s.seg s.array.message with
      | false => rfl
      | true =>
        cases valsAt Z G cov s.seg with
        | error e => cases s.array.sizeI == 1 <;> cases s.shape.mainDeg == 3 <;> rfl
        | ok V =>
          show (errOf (seatAsks s V >>= fun _ => (pure V : Except String SegVals))).isNone =
            (true && true && true && (s.array.sizeI == 1) && (s.shape.mainDeg == 3) &&
              (V.front == s.heard && s.array.sizeC == V.n))
          rw [isNone_then_pure, seatAsks_isNone]
          cases V.front == s.heard <;> cases s.array.sizeI == 1 <;>
            cases s.array.sizeC == V.n <;> cases s.shape.mainDeg == 3 <;> rfl

/-- A helper: a test of two halves at every member. -/
theorem all_both {α : Type} (l : List α) (p q : α → Bool) :
    (l.all fun a => p a && q a) = (l.all p && l.all q) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, ih]
    cases p a <;> cases q a <;> cases l.all p <;> cases l.all q <;> rfl

/-- Each segment of the shape has a seat, in order; no two seats have one address; "seatHalf" at
every seat. -/
def seatsFitBy (codes : OnBytes.Codes) (shape : ReqShape) (lay : ReqLayout) (seats : List Seat) :
    Bool :=
  allSeated shape.link.length seats && pairwise (fun s t => s.addr != t.addr) seats &&
    seats.all (seatHalf codes shape lay)

/-- **THE HALF OF "u3AllFit" THAT READS NO PLAN OF A SEGMENT.** -/
def u3SeatsFit (Z : Pub) (G : Ground) : Bool :=
  seatsFitBy G.first.codes G.first.shape G.first.layout (u3Seats Z G)

/-- **GENERAL: "u3AllFit" is that half, and "valsHalf" at every seat.** -/
theorem u3AllFit_halves (Z : Pub) (G : Ground) (cov : Head.Covered) :
    u3AllFit Z G cov = (u3SeatsFit Z G && (u3Seats Z G).all (valsHalf Z G cov)) := by
  have e : u3Fits Z G cov = fun s =>
      seatHalf G.first.codes G.first.shape G.first.layout s && valsHalf Z G cov s :=
    funext (u3Fits_halves Z G cov)
  unfold u3AllFit u3SeatsFit seatsFitBy
  rw [e, all_both, Bool.and_assoc, Bool.and_assoc, Bool.and_assoc]

/-! ## 4 The first half holds under the head -/

set_option maxRecDepth 1000000 in
/-- The first half at the written values. -/
theorem seatsFitW :
    seatsFitBy codesFull2 proofSizedFull.request layoutFull (seatsW "U3") = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: the test says no at the seats of "M0" and at those of "BZ". (Why, by the written
layout's text and not by this fact: "M0" is an array of moment 0 and has no seat; "BZ" has 32 rows,
over the base field.) -/
theorem seatsFitW_can_fail :
    (seatsFitBy codesFull2 proofSizedFull.request layoutFull (seatsW "M0") ||
      seatsFitBy codesFull2 proofSizedFull.request layoutFull (seatsW "BZ")) = false := by decide +kernel

/-- **UNDER THE HEAD: THE HALF OF "u3AllFit" THAT READS NO PLAN OF A SEGMENT SAYS YES.** -/
theorem u3SeatsFit_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) : u3SeatsFit Zp G = true := by
  obtain ⟨e1, e2, e3⟩ := first_at_head h hG
  unfold u3SeatsFit u3Seats
  rw [seats_at_head h hG, e1, e2, e3]
  exact seatsFitW

/-! ## 5 Two tests, on the seats' addresses and on the later messages -/

/-- Each seat's address is K2's own "addrOf" at the seat's segment and its array's message, at the
frame made of the shape and its groups. (That K2's places are made with this frame is K2's text: no
lemma here holds it.) -/
def addrsAgree (sps : List Spot) (shape : ReqShape) (seats : List Seat) : Bool :=
  seats.all fun s =>
    addrOf { shape := shape, groups := OnBytes.reqGroups shape } sps s.seg s.array.message ==
      some s.addr

/-- Each message of a later moment than 0 is the message of its segment's seat in u3, and the layout
lays "U3" alone into it, or the message of its segment's seat in bz. -/
def laterSeated (shape : ReqShape) (lay : ReqLayout) (u3 bz : List Seat) : Bool :=
  shape.link.zipIdx.all fun L =>
    L.1.messages.zipIdx.all fun M =>
      M.1.moment == 0 ||
        ((u3.any fun s => s.seg == L.2 && s.array.message == M.2) &&
          ((lay.link.getD L.2 []).filter fun a => a.message == M.2).map (·.name) == ["U3"]) ||
        bz.any fun s => s.seg == L.2 && s.array.message == M.2

set_option maxRecDepth 1000000 in
/-- The addresses agree at the written values, for "U3" and for "BZ". -/
theorem addrsAgreeW :
    (addrsAgree spotsWritten proofSizedFull.request (seatsW "U3") &&
      addrsAgree spotsWritten proofSizedFull.request (seatsW "BZ")) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with each array's message raised by one the test says no. -/
theorem addrsAgreeW_can_fail :
    addrsAgree spotsWritten proofSizedFull.request
      ((seatsW "U3").map fun s => { s with array := { s.array with message := s.array.message + 1 } })
      = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The later messages at the written values. -/
theorem laterSeatedW :
    laterSeated proofSizedFull.request layoutFull (seatsW "U3") (seatsW "BZ") = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Controls: without the seats of "U3"; without those of "BZ"; with the two lists exchanged (the
message of "BZ" does not hold "U3" alone): the test says no. -/
theorem laterSeatedW_can_fail :
    (laterSeated proofSizedFull.request layoutFull [] (seatsW "BZ") ||
      laterSeated proofSizedFull.request layoutFull (seatsW "U3") [] ||
      laterSeated proofSizedFull.request layoutFull (seatsW "BZ") (seatsW "U3")) = false := by decide +kernel

/-- **UNDER THE HEAD "addrsAgree" SAYS YES**, for "U3" and for "BZ": at the frame that "addrsAgree"
builds, which no lemma ties to the one of K2's places, and at the written places. -/
theorem addrsAgree_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) :
    addrsAgree spotsWritten G.first.shape (seatsOf Zp G "U3") = true ∧
      addrsAgree spotsWritten G.first.shape (seatsOf Zp G "BZ") = true := by
  obtain ⟨-, e2, -⟩ := first_at_head h hG
  have k := addrsAgreeW
  rw [Bool.and_eq_true] at k
  rw [seats_at_head h hG, seats_at_head h hG, e2]
  exact k

/-- **UNDER THE HEAD: EACH MESSAGE OF A LATER MOMENT IS THE READS', WITH "U3" ALONE IN IT, OR THE
DIGITS'.** -/
theorem laterSeated_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) :
    laterSeated G.first.shape G.first.layout (seatsOf Zp G "U3") (seatsOf Zp G "BZ") = true := by
  obtain ⟨-, e2, e3⟩ := first_at_head h hG
  rw [seats_at_head h hG, seats_at_head h hG, e2, e3]
  exact laterSeatedW

end OnBytes.HonestTrace.U3.Fit

-- Lean's own words on each theorem of this file: its statement, and the axioms that it rests on: each line
-- «depends on axioms» should name no more than propext, Classical.choice and Quot.sound.
#check @OnBytes.HonestTrace.U3.Fit.seatsOf_by
#check @OnBytes.HonestTrace.U3.Fit.cuts_at_head
#check @OnBytes.HonestTrace.U3.Fit.before_at_head
#check @OnBytes.HonestTrace.U3.Fit.spots_at_head
#check @OnBytes.HonestTrace.U3.Fit.first_at_head
#check @OnBytes.HonestTrace.U3.Fit.seats_at_head
#check @OnBytes.HonestTrace.U3.Fit.isNone_then_pure
#check @OnBytes.HonestTrace.U3.Fit.seatAsks_isNone
#check @OnBytes.HonestTrace.U3.Fit.u3Fits_halves
#check @OnBytes.HonestTrace.U3.Fit.all_both
#check @OnBytes.HonestTrace.U3.Fit.u3AllFit_halves
#check @OnBytes.HonestTrace.U3.Fit.seatsFitW
#check @OnBytes.HonestTrace.U3.Fit.seatsFitW_can_fail
#check @OnBytes.HonestTrace.U3.Fit.u3SeatsFit_at_head
#check @OnBytes.HonestTrace.U3.Fit.addrsAgreeW
#check @OnBytes.HonestTrace.U3.Fit.addrsAgreeW_can_fail
#check @OnBytes.HonestTrace.U3.Fit.laterSeatedW
#check @OnBytes.HonestTrace.U3.Fit.laterSeatedW_can_fail
#check @OnBytes.HonestTrace.U3.Fit.addrsAgree_at_head
#check @OnBytes.HonestTrace.U3.Fit.laterSeated_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.seatsOf_by
#print axioms OnBytes.HonestTrace.U3.Fit.cuts_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.before_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.spots_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.first_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.seats_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.isNone_then_pure
#print axioms OnBytes.HonestTrace.U3.Fit.seatAsks_isNone
#print axioms OnBytes.HonestTrace.U3.Fit.u3Fits_halves
#print axioms OnBytes.HonestTrace.U3.Fit.all_both
#print axioms OnBytes.HonestTrace.U3.Fit.u3AllFit_halves
#print axioms OnBytes.HonestTrace.U3.Fit.seatsFitW
#print axioms OnBytes.HonestTrace.U3.Fit.seatsFitW_can_fail
#print axioms OnBytes.HonestTrace.U3.Fit.u3SeatsFit_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.addrsAgreeW
#print axioms OnBytes.HonestTrace.U3.Fit.addrsAgreeW_can_fail
#print axioms OnBytes.HonestTrace.U3.Fit.laterSeatedW
#print axioms OnBytes.HonestTrace.U3.Fit.laterSeatedW_can_fail
#print axioms OnBytes.HonestTrace.U3.Fit.addrsAgree_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.laterSeated_at_head
