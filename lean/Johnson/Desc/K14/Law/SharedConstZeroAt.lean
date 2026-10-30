-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstZeroAt.lean: THE PROMISE GOES FORWARD OVER THE JOINT OF THE FIRST
AND THE SHARED CHAIN, AT ONE STATE, AND AT A PROOF FILE's SEAT. A first form, struck, asked of EVERY
public instance z that the shared chain's first state at z passes the book-keeping's test at border
0. That test reads the key's sizes. The seat's type of public instances (ProofFile.InstPub) holds every
key, and at the empty key the test rejects (Sh.start_can_fail): so at the seat that premise had no
member. HERE the premise is asked AT THE STATE IN HAND ALONE.

  Sh.start_can_fail    a negative test: at the empty key, where the parameters ask one answer, the
                       book-keeping's test at border 0 rejects the first state
  Sh.on_zero_at        **at one b**: the first table's promise at its last border · O.R b.1 · the
                       first state at b's own instance is K14.first at a key that passes the test ·
                       "the committed table decodes" carried over at b → the constant's promise at
                       border 0
  Sh.on_zero_at_seat   **at the seat**: the first state's form by unfolding · O.R from the
      library's
                       "reached" at the first chain's last border (endAt₁_of) at a typed instance ·
                       the test at that instance's key by promise_at_start, where the planner's
                       sizes are the full size's (AtFull)
HOW. Sh.on_zero_at is one call of onZeroAt (Johnson/Desc/Sound/OnZeroAt.lean) at the
constant's letters, the book-keeping's clause by Sh.shape_start.
WHAT STAYS, BY NAME: hlen (the first chain's pieces are as many as the table's places) · hdec.
What is not claimed. No law. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstStart
import Johnson.Desc.Sound.OnZeroAt
import Johnson.Desc.K14.Law.KeyFitsAtStart
import Johnson.Desc.K14.Law.SharedConstOpenAt
import Johnson.Top.H0.Walk.ReachLinks

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

/-- **The test at border 0 can reject a first state**: at the empty key. -/
theorem start_can_fail (p : Par) (codes : Codes) (P : PromMeaning St)
    (ha : p.S.fold.index.answers = 1) : (pmZ p P).shape 0 (first codes {}) = false := by
  have h : shape1 p (first codes {}) = false := by
    show ({} : TableKey).fits p.S.fold.index = false
    unfold TableKey.fits
    simp [ha]
  show (shape1 p (first codes {}) && !notedU (first codes {})) = false
  rw [h]
  rfl

section
variable {Xi P₀ P S₁' S₃' Y X₁ X₂ Cl Cells Tok : Type} (A : ShPlan Xi)
  (O : ShOpen P₀ (P × S₁') Cells Tok A.Q) (D : WholeD) (all : List LeftT)
  (T : Three (ckP .two) D all Y (P × S₁') ((P × S₁') × St) ((P × S₁' × St) × S₃') X₁ X₂ Cl
    (Wit Cells Tok MsgT))
  (Q : Places D all (P × S₁') ((P × S₁') × St) ((P × S₁' × St) × S₃') (Wit Cells Tok MsgT))
  (R₀ : (P × S₁') × (EAll D all).Str → Wit Cells Tok MsgT → Prop)
  (hlen : 1 + T.l₁.length = (ps A O).length)

include hlen in
/-- **The promise goes forward over the joint, at one state.** -/
theorem on_zero_at (start₂ : P → St) (b : (P × S₁') × (EAll D all).Str)
    (hb : (placesM T.ft₁ O.N₁ O.Mg₁ O.links (ps A O) O.get R₀ Q).on₁ (1 + T.l₁.length) b)
    (hr : O.R b.1) (key : TableKey) (hs : start₂ b.1.1 = first A.Q.codes key)
    (hk : (pmZ A.Q.par idleP).shape 0 (first A.Q.codes key) = true)
    (hdec : O.Mg₁.decodes (O.get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) →
      decodesOf (decT₂ A O) (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
        ((actQ (nums A O) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2)))) :
    onQ₂ (nums A O) (pm A O) (own A O) true T.p₂ T.l₂ 0 ((b.1, start₂ b.1.1), b.2) := by
  exact onZeroAt (ckP .two) D all Y P P₀ S₁' St S₃' X₁ X₂ Cl _ start₂ T Q O.get O.N₁ O.Mg₁ O.links
    (ps A O) R₀ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0)) (pm A O) true O.R hlen b hb hdec
    (by rw [hs]; exact shape_start A O key hk) hr

end

/-- **At the seat.** -/
theorem on_zero_at_seat {S₃' Y X₁ X₂ Cells Tok : Type} (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub)
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
    (b : (ProofFile.InstPub × First.S) × (EAll D all).Str)
    (hb : (placesM T.ft₁ O₁.N₁ O₁.Mg₁ O₁.links (ps (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N
        B' cF c₀ matC held O₁)) (fun a => (a.1, a.2)) R₀ Q).on₁ (1 + T.l₁.length) b)
    (hrch : RchAt (seatF o Z N B' cF) (seatF o Z N B' cF).first.blocksInOrder.length b ∧
      ∃ z : LPFD.Full.XF × RecFull, b.1.1 = (LPFD.Full.instanceAsPlainRecord z).pub)
    (hA : H2K.Sizes.AtFull Z.p.chains.made)
    (hdec : O₁.Mg₁.decodes (b.1.1, b.1.2) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) →
      decodesOf (decT₂ (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁))
          ((seatF o Z N B' cF).start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂) ((actQ (nums
          (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁)) T.p₂ T.l₂ 0).2
          ((b.1, (seatF o Z N B' cF).start₂ b.1.1), b.2)))) :
    onQ₂ (nums (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁)) (pm (planAt Z
        N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁)) (own (planAt Z N (seatF o Z N
        B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁)) true T.p₂ T.l₂ 0 ((b.1, (seatF o Z N B'
        cF).start₂ b.1.1), b.2) := by
  obtain ⟨hr, z, hz⟩ := hrch
  refine on_zero_at (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁) D all T
    Q R₀ hlen (seatF o Z N B' cF).start₂ b hb ⟨endAt₁_of hr, z, hz⟩ b.1.1.key rfl ?_ hdec
  rw [hz]
  exact promise_at_start z hA _ idleP

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.start_can_fail
#print axioms Desc.K14.Law.Sh.on_zero_at
#print axioms Desc.K14.Law.Sh.on_zero_at_seat
