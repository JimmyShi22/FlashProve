-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstZeroMade.lean: THE TWO HALVES OF THE JOINT OF THE FIRST AND THE
SHARED CHAIN, AT A PROOF FILE's SEAT, WITH "THE COMMITTED TABLE DECODES" AND "THE WITNESS's TABLE IS
PINNED" CARRIED OVER BY MAKE. Two corollaries: no proof of their own.

  Sh.on_zero_seat_made     the promise goes forward (Sh.on_zero_at_seat,
                       Johnson/Desc/K14/Law/SharedConstZeroAt.lean), its hdec by Sh.hdec_by_make
                       (Johnson/Desc/K14/Law/SharedConstByMake.lean)
  Sh.rel_end_seat_made     the relation goes back (Sh.rel_end_of_zero,
                       Johnson/Desc/K14/Law/SharedConstZero.lean), its hPW by Sh.hPW_by_make
WHAT STAYS, BY NAME: hlen (the first chain's pieces are as many as the table's places) · h1 :
Sh.OneDec (two equations on the first table's meaning: its decoder is made of the shared chain's) ·
forward: "reached" at the first chain's last border at a typed instance, and AtFull · back: hEnd
(what is open behind the first chain's last place).
What is not claimed. No law. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstZeroAt
import Johnson.Desc.K14.Law.SharedConstByMake

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

namespace Sh

/-- **The promise goes forward over the joint, at the seat.** -/
theorem on_zero_seat_made {S₃' Y X₁ X₂ Cells Tok : Type} (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub)
    (N : H2U.Places4) (B' : ProofFile.SecondSeat)
    (cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl) (c₀ : Cells)
    (matC : Cells → Nat → Nat → GE)
    (held : ((ixOf2 (planAt Z N (seatF o Z N B' cF)).Q.par.S.fold 0 2852142980 (rankLib (planAt Z N
        (seatF o Z N B' cF)).Q.par.S.fold)).Row × Fin (planAt Z N (seatF o Z N B'
        cF)).Q.par.S.fold.index.code.ell → GE) → Option Cells)
    (O₁ : Open₁ Cells Tok (planAt Z N (seatF o Z N B' cF)).Q) (D : WholeD) (all : List LeftT)
    (T : Three (ckP .two) D all Y (ProofFile.InstPub × First.S) ((ProofFile.InstPub × First.S) × St)
        ((ProofFile.InstPub × First.S × St) × S₃') X₁ X₂ ProofFile.Cl (Wit Cells Tok MsgT))
    (Q : Places D all (ProofFile.InstPub × First.S) ((ProofFile.InstPub × First.S) × St) ((ProofFile.InstPub × First.S
                    × St) × S₃') (Wit Cells Tok MsgT))
    (R₀ : (ProofFile.InstPub × First.S) × (EAll D all).Str → Wit Cells Tok MsgT → Prop)
    (hlen : 1 + T.l₁.length = (ps (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held
        O₁)).length)
    (h1 : OneDec (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁) (seatF o Z N
        B' cF).start₂)
    (b : (ProofFile.InstPub × First.S) × (EAll D all).Str)
    (hb : (placesM T.ft₁ O₁.N₁ O₁.Mg₁ O₁.links (ps (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N
        B' cF c₀ matC held O₁)) (fun a => (a.1, a.2)) R₀ Q).on₁ (1 + T.l₁.length) b)
    (hrch : RchAt (seatF o Z N B' cF) (seatF o Z N B' cF).first.blocksInOrder.length b ∧
      ∃ z : LPFD.Full.XF × RecFull, b.1.1 = (LPFD.Full.instanceAsPlainRecord z).pub)
    (hA : H2K.Sizes.AtFull Z.p.chains.made) :
    onQ₂ (nums (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁)) (pm (planAt Z
        N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁)) (own (planAt Z N (seatF o Z N
        B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁)) true T.p₂ T.l₂ 0 ((b.1, (seatF o Z N B'
        cF).start₂ b.1.1), b.2) :=
  on_zero_at_seat o Z N B' cF c₀ matC held O₁ D all T Q R₀ hlen b hb hrch hA
    (hdec_by_make (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁) D all
        (seatF o Z N B' cF).start₂ T (fun _ => rfl) h1 b)

/-- **The relation goes back over the joint, at the seat.** -/
theorem rel_end_seat_made {S₃' Y X₁ X₂ Cells Tok : Type} (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub)
    (N : H2U.Places4) (B' : ProofFile.SecondSeat)
    (cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl) (c₀ : Cells)
    (matC : Cells → Nat → Nat → GE)
    (held : ((ixOf2 (planAt Z N (seatF o Z N B' cF)).Q.par.S.fold 0 2852142980 (rankLib (planAt Z N
        (seatF o Z N B' cF)).Q.par.S.fold)).Row × Fin (planAt Z N (seatF o Z N B'
        cF)).Q.par.S.fold.index.code.ell → GE) → Option Cells)
    (O₁ : Open₁ Cells Tok (planAt Z N (seatF o Z N B' cF)).Q) (D : WholeD) (all : List LeftT)
    (T : Three (ckP .two) D all Y (ProofFile.InstPub × First.S) ((ProofFile.InstPub × First.S) × St)
        ((ProofFile.InstPub × First.S × St) × S₃') X₁ X₂ ProofFile.Cl (Wit Cells Tok MsgT))
    (Q : Places D all (ProofFile.InstPub × First.S) ((ProofFile.InstPub × First.S) × St) ((ProofFile.InstPub × First.S
                    × St) × S₃') (Wit Cells Tok MsgT))
    (R₀ : (ProofFile.InstPub × First.S) × (EAll D all).Str → Wit Cells Tok MsgT → Prop)
    (hlen : 1 + T.l₁.length = (ps (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held
        O₁)).length)
    (h1 : OneDec (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁) (seatF o Z N
        B' cF).start₂)
    (hEnd : ∀ i, openAfter (insQ O₁.links (ps (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF
        c₀ matC held O₁))) (outsQ O₁.links (ps (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF
        c₀ matC held O₁))) (· ∈ start O₁.links) (ps (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N
        B' cF c₀ matC held O₁)).length i → i ∈ endFirst)
    (b : (ProofFile.InstPub × First.S) × (EAll D all).Str) (w : Wit Cells Tok MsgT)
    (h : relQ₂ (nums (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁)) (mg
        (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁)) true T.p₂ T.l₂ 0
        ((b.1, (seatF o Z N B' cF).start₂ b.1.1), b.2) w) :
    (placesM T.ft₁ O₁.N₁ O₁.Mg₁ O₁.links (ps (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF
        c₀ matC held O₁)) (fun a => (a.1, a.2)) R₀ Q).R₁ (1 + T.l₁.length) b w :=
  rel_end_of_zero (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁) D all
      (seatF o Z N B' cF).start₂ T Q R₀ hlen hEnd
    (hPW_by_make (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁) D all (seatF
        o Z N B' cF).start₂ T (fun _ => rfl) h1) b w h

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.on_zero_seat_made
#print axioms Desc.K14.Law.Sh.rel_end_seat_made
