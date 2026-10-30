-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/Desc/AtSeats/ShJointHalvesAll.lean: THE TWO HALVES OF THE JOINT OF THE FIRST AND THE
    SHARED
CHAIN, AT THE SHARED TABLE's CONSTANT WITH ALL ITS LETTERS CLOSED (Sh.planAt, Sh.openAll), AT THE
SECOND HASH FUNCTION ITSELF, AT THE ROW OF PIECES THAT IS MADE OF THE IOP AS WRITTEN IN LEAN. Two
corollaries: no proof of their own.

  Sh.hlen_all          the first chain's pieces are as many as the table's places
  Sh.on_zero_all       the promise goes forward over the joint
  Sh.rel_end_all       the relation goes back over the joint
HOW. Sh.on_zero_seat_made | rel_end_seat_made (Johnson/Desc/K14/Law/SharedConstZeroMade.lean) called
at Sh.openAll (Johnson/Desc/K14/Law/SharedConstFirstAt.lean): hlen by Sh.hlen_at_seat_open
(SharedConstLenAt.lean) with Sh.links_in_scope (SharedConstLinksAt.lean) at the opening that the
head P5J.AtMgA bears · Sh.OneDec by Sh.oneDec_all · AtFull by
atFull_of_pubPlain.
WHAT STAYS IN FRONT: the head h (a member of it is proved at storedPublicFiles and zGap alone (at
secondHashFunction; side library AtFullSide/Top/)) · e (the two tables read one list
of codes: Sh.hcs_in_scope, under the door's two pins) · OfDesc · forward: the first table's promise
at its last border, and "reached" there at a typed instance · back: hEnd.
What is not claimed. No law. No soundness of a verifier; no level.

-/
import Johnson.Desc.AtSeats.ShOneDecAll
import Johnson.Desc.K14.Law.SharedConstZeroMade
import Johnson.Desc.K14.Law.SharedConstLenAt
import Johnson.Desc.K14.Law.SharedConstLinksAt
import Johnson.Loose.H2K12.AtFullPlain

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

open Johnson.Desc.First.Walk.Tied (RchAt EndAt₁ endAt₁_of)

open VerifiableInference.OnPublicFiles (kcReq)

namespace Sh

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **hlen at the closed letters.** -/
theorem hlen_all (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (e : P5J.At.cs Zp = (planAt Zp Np (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF)).Q.codes) {D'
                    : WholeD} {all : List LeftT} {X₁ X₂ : Type}
    (T : ThreeAt (ckP .two) D' all (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF) X₁ X₂ (Wit
                    (kcReq numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL) (P5J.At.EAt Z)).conf.I
                    P5J.At.Tok MsgT))
    (hO : OfDesc (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF) T) :
    1 + (atDesc (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF) T).l₁.length = (ps (planAt Zp Np
                    (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF)) (openAll h e)).length := by
  obtain ⟨Bs, base, Op⟩ := h.laid.opened
  exact hlen_at_seat_open OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF _ _ _ (open₁At h e) D' all T Op
    (links_in_scope h.scope Op).symm hO

/-- **The promise goes forward over the joint, at the closed letters.** -/
theorem on_zero_all (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (e : P5J.At.cs Zp = (planAt Zp Np (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF)).Q.codes) {D'
                    : WholeD} {all : List LeftT} {X₁ X₂ : Type}
    (T : ThreeAt (ckP .two) D' all (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF) X₁ X₂ (Wit
                    (kcReq numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL) (P5J.At.EAt Z)).conf.I
                    P5J.At.Tok MsgT))
    (hO : OfDesc (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF) T)
    (Q : Places D' all (ProofFile.InstPub × First.S) ((ProofFile.InstPub × First.S) × St) ((ProofFile.InstPub ×
                    First.S × St) × (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF).S₃) (Wit (kcReq numsFull
                                (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL) (P5J.At.EAt Z)).conf.I P5J.At.Tok MsgT))
    (R₀ : (ProofFile.InstPub × First.S) × (EAll D' all).Str → (Wit (kcReq numsFull
              (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL) (P5J.At.EAt Z)).conf.I P5J.At.Tok MsgT) →
        Prop)
    (b : (ProofFile.InstPub × First.S) × (EAll D' all).Str)
    (hb : (placesM (atDesc (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF) T).ft₁ (P5J.At.N Zp cF)
        (P5J.mgAtAll h) P5J.At.links (ps (planAt Zp Np (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np)
        cF)) (openAll h e)) (fun a => (a.1, a.2)) R₀ Q).on₁ (1 + (atDesc (seatF OnBytes.secondHashFunction Zp Np
        (secondAt Zp Np) cF) T).l₁.length) b)
    (hrch : RchAt (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF) (seatF OnBytes.secondHashFunction Zp Np
                    (secondAt Zp Np) cF).first.blocksInOrder.length b ∧
      ∃ z : LPFD.Full.XF × RecFull, b.1.1 = (LPFD.Full.instanceAsPlainRecord z).pub) :
    onQ₂ (nums (planAt Zp Np (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF)) (openAll h e)) (pm
                    (planAt Zp Np (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF)) (openAll h e)) (own (planAt
                                Zp Np (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF)) (openAll h e)) true (atDesc (seatF
                                            OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF) T).p₂ (atDesc (seatF OnBytes.secondHashFunction Zp Np
                                                        (secondAt Zp Np) cF) T).l₂ 0 ((b.1, (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF).start₂
                                                        b.1.1), b.2) :=
  on_zero_seat_made OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF _ _ _ (open₁At h e) D' all (atDesc
                  (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF) T) Q R₀
    (hlen_all h e T hO) (oneDec_all h e) b hb hrch (H2K.Sizes.atFull_of_pubPlain h.scope h.laid.pub)

/-- **The relation goes back over the joint, at the closed letters.** -/
theorem rel_end_all (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (e : P5J.At.cs Zp = (planAt Zp Np (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF)).Q.codes) {D'
                    : WholeD} {all : List LeftT} {X₁ X₂ : Type}
    (T : ThreeAt (ckP .two) D' all (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF) X₁ X₂ (Wit
                    (kcReq numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL) (P5J.At.EAt Z)).conf.I
                    P5J.At.Tok MsgT))
    (hO : OfDesc (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF) T)
    (Q : Places D' all (ProofFile.InstPub × First.S) ((ProofFile.InstPub × First.S) × St) ((ProofFile.InstPub ×
                    First.S × St) × (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF).S₃) (Wit (kcReq numsFull
                                (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL) (P5J.At.EAt Z)).conf.I P5J.At.Tok MsgT))
    (R₀ : (ProofFile.InstPub × First.S) × (EAll D' all).Str → (Wit (kcReq numsFull
              (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL) (P5J.At.EAt Z)).conf.I P5J.At.Tok MsgT) →
        Prop)
    (hEnd : ∀ i, openAfter (insQ P5J.At.links (ps (planAt Zp Np (seatF OnBytes.secondHashFunction Zp Np
        (secondAt Zp Np) cF)) (openAll h e))) (outsQ P5J.At.links (ps (planAt Zp Np (seatF
        OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF)) (openAll h e))) (· ∈ start P5J.At.links) (ps
                    (planAt Zp Np (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF)) (openAll h e)).length i → i
        ∈ endFirst)
    (b : (ProofFile.InstPub × First.S) × (EAll D' all).Str) (w : (Wit (kcReq numsFull
              (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL) (P5J.At.EAt Z)).conf.I P5J.At.Tok MsgT))
    (hrel : relQ₂ (nums (planAt Zp Np (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF)) (openAll h
                    e)) (mg (planAt Zp Np (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF)) (openAll h e)) true
        (atDesc (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF) T).p₂ (atDesc (seatF OnBytes.secondHashFunction
                    Zp Np (secondAt Zp Np) cF) T).l₂ 0 ((b.1, (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np)
                    cF).start₂ b.1.1), b.2) w) :
    (placesM (atDesc (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF) T).ft₁ (P5J.At.N Zp cF)
        (P5J.mgAtAll h) P5J.At.links (ps (planAt Zp Np (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np)
        cF)) (openAll h e)) (fun a => (a.1, a.2)) R₀ Q).R₁ (1 + (atDesc (seatF OnBytes.secondHashFunction Zp Np
        (secondAt Zp Np) cF) T).l₁.length) b w :=
  rel_end_seat_made OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF _ _ _ (open₁At h e) D' all (atDesc
                  (seatF OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF) T) Q R₀
    (hlen_all h e T hO) (oneDec_all h e) hEnd b w hrel

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.hlen_all
#print axioms Desc.K14.Law.Sh.on_zero_all
#print axioms Desc.K14.Law.Sh.rel_end_all
