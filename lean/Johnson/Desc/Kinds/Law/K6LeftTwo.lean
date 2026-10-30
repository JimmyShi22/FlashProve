-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6LeftTwo.lean: K6LeftSeven (Law/K6LeftSeven.lean) CUT IN TWO, field for
field, in its own words: seatsC, book, fenceT, numbers, namedC, which Law/K06AtHeadTwo.lean pays at
the head AtMgA (P5J/MgAtAll.lean) by calls · K6LeftTwo: the other two. A new file beside:
no byte of K6LeftSeven turns. Nothing is proved here but that the parts give the whole.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  K6LeftTwo: callsC · maskC.
  seven_of_two: the five and K6LeftTwo give K6LeftSeven.

The fields' texts and their lines of words are cut by program out of K6LeftSeven's; Lean holds the
texts against it in seven_of_two.
What it does not say. That any part can be met. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K6LeftSeven

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

/-- **The two fields that are left.** -/
structure K6LeftTwo : Prop where
  /-- a test with code (Law/K6CallsTest.lean): the matrices that the lookup on the
      head's calls reads sit as planned -/
  callsC : AtFold.callsSeatedC D.arr D.ms D.N Wp lay6 num D.sent D.l3.rad x.link
    (D.l3.seat x.link false) = true
  /-- a test with code (the same file): the mask row sits as planned -/
  maskC : AtFold.maskMeetsC D.arr D.ms D.N D.sent D.l3.rad x.link (D.l3.seat x.link false)
    (num 24 0) Wp.H.ns = true

/-- **The parts give the whole.** -/
theorem seven_of_two (bs : List (Block (P × S) Claim))
    (seatsC : AtFold.seatsK6C D.arr D.N Wp lay6 num (num 24 0) 0 D.cs D.shape D.pubD.dS Lp Mm
    (D.sent.arrayOf.getD 24 #[]) (D.N.msgsAt PS[341]?) = true)
    (book : bookFit D.N PS (toldOf bs) = true)
    (fenceT : fenceFit D.N linksFull PS = true)
    (numbers : D.N.treesAt PS[341 + 1]? = D.N.treesAt PS[341]? ∧
    D.N.msgsAt PS[341 + 1]? = D.N.msgsAt PS[341]?)
    (namedC : OffPad.namedAtC D.arr D.N Wp lay6 num (Wp.hS.NHf + 2) = true)
    (L : K6LeftTwo D lay6 num x) :
    K6LeftSeven D lay6 num x Lp Mm bs :=
  { callsC := L.callsC
    maskC := L.maskC
    seatsC := seatsC
    book := book
    fenceT := fenceT
    numbers := numbers
    namedC := namedC }

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.seven_of_two
