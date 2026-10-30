-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6LeftSeven.lean: K6LeftMg (Law/K6DueSplit.lean:
nine fields) CUT IN TWO, field for field, in its own words: planC and tokSmall, which
K06AtHeadSeven.lean pays at the head AtMgA (P5J/MgAtAll.lean) · K6LeftSeven: the other seven. A new
file beside: no byte of K6DueSplit turns. Nothing is proved here but that the parts give the whole.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  K6LeftSeven: callsC · maskC · seatsC · book · fenceT · numbers · namedC.
  left_of_seven: planC, tokSmall and K6LeftSeven give K6LeftMg.

The fields' texts and their lines of words are cut by program out of K6LeftMg's; Lean holds the
texts against it in left_of_seven.
What it does not say. That any part can be met. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K6DueSplit

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

/-- **The seven fields that are left.** -/
structure K6LeftSeven (bs : List (Block (P × S) Claim)) : Prop where
  /-- a test with code (Law/K6CallsTest.lean): the matrices that the lookup on the
      head's calls reads sit as planned -/
  callsC : AtFold.callsSeatedC D.arr D.ms D.N Wp lay6 num D.sent D.l3.rad x.link
    (D.l3.seat x.link false) = true
  /-- a test with code (the same file): the mask row sits as planned -/
  maskC : AtFold.maskMeetsC D.arr D.ms D.N D.sent D.l3.rad x.link (D.l3.seat x.link false)
    (num 24 0) Wp.H.ns = true
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

/-- **The parts give the whole.** -/
theorem left_of_seven (bs : List (Block (P × S) Claim))
    (planC : OffPad.planK6C D.cs D.arr D.ms D.N Wp lay6 num (num 24 0) 0 = true)
    (tokSmall : ∀ a, onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a → Rch 341 a →
        a.1.2.failed
      = none →
    TokSmall Wp.hS.V a.1.2)
    (L : K6LeftSeven D lay6 num x Lp Mm bs) :
    K6LeftMg D Mg lay6 num Fr x Rch Lp Mm bs :=
  { planC := planC
    callsC := L.callsC
    maskC := L.maskC
    tokSmall := tokSmall
    seatsC := L.seatsC
    book := L.book
    fenceT := L.fenceT
    numbers := L.numbers
    namedC := L.namedC }

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.left_of_seven
