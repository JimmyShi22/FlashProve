-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstLenAt.lean: THE FIRST CHAIN HAS AS MANY SUB-PROTOCOLS AS THE FIRST
TABLE's WALK HAS PLACES. Theorems.

WHY. The step of the promise over the joint of the first and the shared chain (Sh.on_zero_at,
Johnson/Desc/K14/Law/SharedConstZeroAt.lean) asks hlen : 1 + T.l₁.length = (Sh.ps A O).length: the
first row of pieces is as long as the list of places along which the first table's promise is
walked. Here that is had BY MAKE.
  len_of_ofDesc    where the pieces hold the sub-protocols of the IOP as written in Lean (OfDesc,
                   Johnson/Desc/Sound/DescThree.lean): 1 + T.l₁.length = F.first.blocksInOrder.length.
  len_of_places    a chain whose flat list stands at the driver's places is as long as the table's
                   walk First.flatPlaces true links true.
  hlen_of          the two together, general in the IOP.
  hlen_at_seat     **hlen at the seat**, at the constant's own letters: from: the first chain is one
                   that ProofFile.chainBy returns (hc; then ProofFile.Law.chainBy_places,
                   Johnson/Desc/ProofFile/Law/OrderCovered.lean) · a sub-protocol of the kind K13
                   is among its base (hsev) · the open letter links is the public part's own list
                   (hlk) · OfDesc.
  hlen_at_seat'    the same of atDesc F T, the filling that is meant: its first row is T's.
  hlen_at_seat_open   hlen at the seat FROM THE OPENED SEAT (IM.Open, which "onlineDescription returns"
                   gives: Johnson/Desc/K14/Law/FirstLenOfOpen.lean): hc and hsev fall; hlk and
                   OfDesc stay.
What is not claimed. hc, hsev, hlk, OfDesc at the verifier's own value: other files'. No number:
that the length is 358 at the full size is not said here. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.SharedConstOpenAt
import Johnson.Desc.Sound.DescThree
import Johnson.Desc.ProofFile.Law.OrderCovered
import Johnson.Desc.K14.Law.FirstLenOfOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)
open Johnson.Desc.First.Walk.Tied (EndAt₁ RchAt₂)
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First (flatPlaces flatPlacesOf)

namespace Sh

/-- The first row of pieces is as long as the first chain's flat list. -/
theorem len_of_ofDesc {C : CK} {D : WholeD} {all : List LeftT} {Xi X₁ X₂ W : Type}
    (F : FileDescription Xi) (T : ThreeAt C D all F X₁ X₂ W) (hO : OfDesc F T) :
    1 + T.l₁.length = F.first.blocksInOrder.length := by
  have h := congrArg List.length hO.b₁
  simp only [List.length_map, List.length_cons] at h
  omega

/-- A chain at the driver's places is as long as the table's walk. -/
theorem len_of_places {S Cl : Type} (c : Chain S Cl) (links : List ModelPart)
    (h : c.blocksInOrder.map (·.place) = flatPlacesOf links true) :
    c.blocksInOrder.length = (flatPlaces true links true).length := by
  have h' := congrArg List.length h
  rw [List.length_map] at h'
  exact h'

/-- **The two together.** -/
theorem hlen_of {C : CK} {D : WholeD} {all : List LeftT} {Xi X₁ X₂ W : Type} (F : FileDescription Xi)
    (T : ThreeAt C D all F X₁ X₂ W) (hO : OfDesc F T) (links : List ModelPart)
    (hp : F.first.blocksInOrder.map (·.place) = flatPlacesOf links true) :
    1 + T.l₁.length = (flatPlaces true links true).length :=
  (len_of_ofDesc F T hO).trans (len_of_places _ links hp)

section
variable {Cells Tok X₁ X₂ : Type} (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (N : H2U.Places4)
  (B' : ProofFile.SecondSeat) (cF : Chain First.S ProofFile.Cl) (c₀ : Cells) (matC : Cells → Nat → Nat → GE)
  (held : ((ixOf2 (planAt Z N (seatF o Z N B' cF)).Q.par.S.fold 0 2852142980
      (rankLib (planAt Z N (seatF o Z N B' cF)).Q.par.S.fold)).Row ×
      Fin (planAt Z N (seatF o Z N B' cF)).Q.par.S.fold.index.code.ell → GE) → Option Cells)
  (O₁ : Open₁ Cells Tok (planAt Z N (seatF o Z N B' cF)).Q) (D : WholeD) (all : List LeftT)
  (T : ThreeAt (ckP .two) D all (seatF o Z N B' cF) X₁ X₂ (Wit Cells Tok MsgT))

/-- **hlen at the seat.** -/
theorem hlen_at_seat {base : List (Block First.S ProofFile.Cl)}
    {fr : List (ProofFile.FrameRole × Block First.S ProofFile.Cl)} {road : ProofFile.Gather First.S ProofFile.Cl}
    (hc : ProofFile.chainBy Z base fr road = .ok cF)
    (hsev : (base.any fun b => b.place.kind == KindName.K13) = true)
    (hlk : O₁.links = ProofFile.subsOf Z) (hO : OfDesc (seatF o Z N B' cF) T) :
    1 + T.l₁.length =
      (ps (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁)).length := by
  show 1 + T.l₁.length = (flatPlaces true O₁.links true).length
  rw [hlk]
  refine hlen_of (seatF o Z N B' cF) T hO (ProofFile.subsOf Z) ?_
  have h := ProofFile.Law.chainBy_places hc
  rw [hsev] at h
  exact h

/-- **The same of the filling that is meant.** -/
theorem hlen_at_seat' {base : List (Block First.S ProofFile.Cl)}
    {fr : List (ProofFile.FrameRole × Block First.S ProofFile.Cl)} {road : ProofFile.Gather First.S ProofFile.Cl}
    (hc : ProofFile.chainBy Z base fr road = .ok cF)
    (hsev : (base.any fun b => b.place.kind == KindName.K13) = true)
    (hlk : O₁.links = ProofFile.subsOf Z) (hO : OfDesc (seatF o Z N B' cF) T) :
    1 + (atDesc (seatF o Z N B' cF) T).l₁.length =
      (ps (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁)).length :=
  hlen_at_seat o Z N B' cF c₀ matC held O₁ D all T hc hsev hlk hO

/-- **hlen at the seat, from the opened seat.** -/
theorem hlen_at_seat_open {pol lay KL : ByteArray} {Bs : ProofFile.PureBase}
    {base : List (Block First.S ProofFile.Cl)} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (Op : IM.Open o pol lay KL (seatF o Z N B' cF) Z Bs base cF A B)
    (hlk : O₁.links = ProofFile.subsOf Z) (hO : OfDesc (seatF o Z N B' cF) T) :
    1 + T.l₁.length =
      (ps (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁)).length := by
  show 1 + T.l₁.length = (flatPlaces true O₁.links true).length
  rw [hlk]
  exact hlen_of_open Op T hO

end

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.len_of_ofDesc
#print axioms Desc.K14.Law.Sh.len_of_places
#print axioms Desc.K14.Law.Sh.hlen_of
#print axioms Desc.K14.Law.Sh.hlen_at_seat
#print axioms Desc.K14.Law.Sh.hlen_at_seat'
#print axioms Desc.K14.Law.Sh.hlen_at_seat_open
