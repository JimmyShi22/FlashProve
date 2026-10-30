-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstTopAt.lean: THE JOIN's ONE PREMISE ON THE PIECES, AT THE SEAT. The
step from the ledger's end to the law at the shared table's constant (Sh.law_of_top,
Johnson/Desc/K14/Law/SharedConstTop.lean) asks hXD: inside the constant's promise each piece's yes
hands on the tests for the last chain's door. Sh.xd_of_steps has it from "each piece's yes is an
accepting step of the sub-protocol at its number of the list". HERE that premise and the chain's
form are paid at the row of pieces that is made of the IOP as written in Lean itself.

  Sh.steps_of_desc     kind-free: under OfDesc F T the piece number i of the shared chain's row
      holds
                       the sub-protocol number i of F's flat list in the wrap, and its yes is an
                       accepting step of it (held_at, piece_step_below)
  Sh.xd_at_seat        **hXD at F := seatF …, f :: l := T.p₂ :: T.l₂, under OfDesc F T**: in front:
      the
                       named tests on the parameters · that the places name a second proximity test
                       · the six facts on the two proximity tests' parameters
  Sh.descAt …          the maker's own text (ProofFile.fileDescBy) at a shared seat spelled field by
      field,
                       whose chain is chainOf ch Q tests K12.Seat.last: the ledger's tops' own form
  Sh.chainOk_descAt    its test's yes gives Sh.chainOkAt's sentence (for Sh.tests_at)
  Sh.xd_at_field       **hXD at F := descAt …**, general in its letters, where the tests are the two
                       proximity tests
  Sh.xd_in_scope       **the same in the goals' scope, at the value that is laid**: nothing in front
      but
                       OfDesc and what Sh.X_reached_in_scope has
WHAT IS NOT HERE. No law.
What is not claimed. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstTop
import Johnson.Desc.K14.Law.SharedConstChain
import Johnson.Desc.K14.Law.SharedConstScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

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

open Johnson.Desc.First.Walk.Tied
open KObj
open Johnson.G (codesFull2)
open VerifiableInference.Desc.K1 (realSized)
open H2K.JointK (descN)

namespace Sh

/-- **Each piece's yes is an accepting step of the sub-protocol at its number, in the wrap.** -/
theorem steps_of_desc {C : CK} {D : WholeD} {all : List LeftT} {Xi X₁ X₂ W : Type}
    {F : FileDescription Xi} {T : ThreeAt C D all F X₁ X₂ W} (hT : OfDesc F T) :
    ∀ (i : ℕ) (x : Piece C (frameAt D all D.key₂ T.ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl W),
      (T.p₂ :: T.l₂)[i]? = some x → ∃ B, (F.shared.blocksInOrder.map below)[i]? = some B ∧
        ∀ a (τ : Iop.Tr (uLT C x.ds)) b, x.ior.red.out a τ = some b →
          StepYes (frameAt D all D.key₂ T.ft₂).ft B a.1.2 b.1.2 := by
  intro i x hx
  obtain ⟨B, hB, hb⟩ := held_at hT.b₂ hx
  exact ⟨below B, by rw [List.getElem?_map, hB]; rfl,
    fun a τ b h => (piece_step_below x B hb a b τ h).2⟩

variable {P₀ Cells Tok : Type} (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (N : H2U.Places4)
  (B' : ProofFile.SecondSeat) (cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl)

/-- **hXD at the seat.** -/
theorem xd_at_seat (nO : H2U.PlaceNums) (hO : N.O = some nO) (hT : Tests (planAt Z N (seatF o Z N B'
    cF)))
    (heA : (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U).early = true) (ha1A : (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩
                            N.U).answers = 1)
    (hftA : (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U).nums.firstTree = (planAt Z N (seatF o Z N B'
                            cF)).Q.par.toGPar.firstTree)
    (heB : (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).early = true) (ha1B : (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩
                            nO).answers = 1)
    (hftB : (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).nums.firstTree = (planAt Z N (seatF o Z N B'
                            cF)).Q.par.toGPar.firstTree)
    (O : ShOpen P₀ (ProofFile.InstPub × First.S) Cells Tok (planAt Z N (seatF o Z N B' cF)).Q)
    {D : WholeD} {all : List LeftT} {X₁ X₂ : Type}
    (T : ThreeAt (ckP .two) D all (seatF o Z N B' cF) X₁ X₂ (Wit Cells Tok MsgT))
    (hD : OfDesc (seatF o Z N B' cF) T) :
    ∀ i x, (T.p₂ :: T.l₂)[i]? = some x → ∀ a τ b,
      onQ₂ (nums (planAt Z N (seatF o Z N B' cF)) O) (pm (planAt Z N (seatF o Z N B' cF)) O) (own
          (planAt Z N (seatF o Z N B' cF)) O) true T.p₂ T.l₂ i a →
      x.ior.red.out a τ = some b → XD (planAt Z N (seatF o Z N B' cF)).p (i + 1) b.1.2 = true := by
  have e : (seatF o Z N B' cF).shared.blocksInOrder.map below = rowOf Z.p.chains (bk (planAt Z N (seatF o Z N
               B' cF)) 0) (bk (planAt Z N (seatF o Z N B' cF)) 1)
      (bk (planAt Z N (seatF o Z N B' cF)) 2) (bk (planAt Z N (seatF o Z N B' cF)) 3) (bk (planAt Z
          N (seatF o Z N B' cF)) 4) (bk (planAt Z N (seatF o Z N B' cF)) 5) (bk (planAt Z N (seatF o
          Z N B' cF)) 6) (bk (planAt Z N (seatF o Z N B' cF)) 7)
      (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U) (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO)
          VerifiableInference.Desc.K12.Seat.last := by
    rw [← rowOf_is Z.p.chains _ _ _ _ _ _ _ _ _ _ _ (planAt Z N (seatF o Z N B' cF)).Q (tests_hbl8
        (planAt Z N (seatF o Z N B' cF)) hT),
      ← tests_two N nO hO]
    rfl
  have hq := steps_of_desc hD
  rw [e] at hq
  exact xd_of_steps (planAt Z N (seatF o Z N B' cF)) O (tests_hUw _ hT) (tests_hS _ hT) _ _ _ _ _ _
      _ _ (tests_hbl8 _ hT)
    (tests_hlU _ hT) (tests_hlO _ hT) (tests_hm _ hT) (tests_hp8 _ hT) (tests_hok _ hT)
    (tests_hC2 _ hT) (tests_hC5 _ hT) (tests_pyU _ hT) (tests_pyO _ hT) (tests_pyS _ hT) _ _ heA
    ha1A hftA heB ha1B hftB (tests_hl _ hT) (tests_hsU _ hT) _ (form_h0 Z.p.chains _ _ _ _ _ _ _ _ _
        _ _)
    (form_h8 Z.p.chains _ _ _ _ _ _ _ _ _ _ _) (form_h9 Z.p.chains _ _ _ _ _ _ _ _ _ _ _)
    (form_h10 Z.p.chains _ _ _ _ _ _ _ _ _ _ _) (form_h11 Z.p.chains _ _ _ _ _ _ _ _ _ _)
    (form_len Z.p.chains _ _ _ _ _ _ _ _ _ _ _) (tests_hpS _ hT) T.p₂ T.l₂ hq

/-- The maker's own text at a shared seat spelled field by field. -/
abbrev descAt {σ₁ : Type} (oH : ProofFile.SecondHashFunctionArgument) (mkL : ProofFile.LinksBy) (Zp : ProofFile.Pub) (lt : String)
    (st₂ : ProofFile.InstPub → St) (en₂ : St → Option OnBytes.Proof.SharedEnd) (ok₂ : ProofFile.InstPub → Bool)
    (fo₂ : Bool) (si₂ : List String) (Bs : ProofFile.SecondSeat) (getS : σ₁ → First.S)
    (startS : ProofFile.InstPub → σ₁) (cF : VerifiableInference.Desc.Chain σ₁ ProofFile.Cl)
    (ch : Model.Verify.Chains) (Q : P14) (tests : List (Block St Unit)) : FileDescription ProofFile.Inst :=
  ProofFile.fileDescBy oH mkL Zp
    { lot := lt, σ := St, start := st₂
      chain := chainOf ch Q tests VerifiableInference.Desc.K12.Seat.last, ended := en₂
      okInst := ok₂, fileOk := fo₂, standIns := si₂ } Bs getS startS cF

/-- Where the test on descAt … accepts, every sub-protocol of its shared chain passes its own test
    on
its parameters. -/
theorem chainOk_descAt {σ₁ : Type} (oH : ProofFile.SecondHashFunctionArgument) (mkL : ProofFile.LinksBy) (Zp : ProofFile.Pub)
    (lt : String) (st₂ : ProofFile.InstPub → St) (en₂ : St → Option OnBytes.Proof.SharedEnd)
    (ok₂ : ProofFile.InstPub → Bool) (fo₂ : Bool) (si₂ : List String) (Bs : ProofFile.SecondSeat)
    (getS : σ₁ → First.S) (startS : ProofFile.InstPub → σ₁)
    (cF : VerifiableInference.Desc.Chain σ₁ ProofFile.Cl) (ch : Model.Verify.Chains) (Q : P14)
    (tests : List (Block St Unit)) (hp : (descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
        ch Q tests).planOk = true) :
    VerifiableInference.Desc.blocksOk
      (chainOf ch Q tests VerifiableInference.Desc.K12.Seat.last).blocksInOrder = true :=
  (ToldDesc.blocksOk_retype (Cl' := ProofFile.Cl)
    (chainOf ch Q tests VerifiableInference.Desc.K12.Seat.last) rfl).symm.trans
    (ToldDesc.shared_ok_of_planOk (descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q
        tests) hp)

/-- **hXD at the ledger's tops' own form of the IOP as written in Lean.** -/
theorem xd_at_field {σ₁ P₀ Cells Tok : Type} (oH : ProofFile.SecondHashFunctionArgument) (mkL : ProofFile.LinksBy)
    (Zp : ProofFile.Pub) (lt : String) (st₂ : ProofFile.InstPub → St)
    (en₂ : St → Option OnBytes.Proof.SharedEnd) (ok₂ : ProofFile.InstPub → Bool) (fo₂ : Bool)
    (si₂ : List String) (Bs : ProofFile.SecondSeat) (getS : σ₁ → First.S) (startS : ProofFile.InstPub → σ₁)
    (cF : VerifiableInference.Desc.Chain σ₁ ProofFile.Cl) (ch : Model.Verify.Chains) (Q : P14)
    (tests : List (Block St Unit)) (πA πB : P12)
    (htests : tests = [Seat.onGu (proximityTestKind guardedProximityTestParts πA : Block T12 Unit),
      Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block T12 Unit)])
    (pLast : P₁₄) (rad2 rad5 : ℕ → ℕ) (Wr : Rounds) (fl : ℕ)
    (hT : Tests (ShPlan.mk Q (descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests)
        pLast rad2 rad5 Wr fl))
    (heA : πA.early = true) (ha1A : πA.answers = 1)
    (hftA : πA.nums.firstTree = Q.par.toGPar.firstTree)
    (heB : πB.early = true) (ha1B : πB.answers = 1)
    (hftB : πB.nums.firstTree = Q.par.toGPar.firstTree)
    (O : ShOpen P₀ (ProofFile.InstPub × σ₁) Cells Tok Q)
    {D : WholeD} {all : List LeftT} {X₁ X₂ : Type}
    (T : ThreeAt (ckP .two) D all (descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q
        tests) X₁ X₂ (Wit Cells Tok MsgT))
    (hD : OfDesc (descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) T) :
    ∀ i x, (T.p₂ :: T.l₂)[i]? = some x → ∀ a τ b,
      onQ₂ (nums (ShPlan.mk Q (descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests)
          pLast rad2 rad5 Wr fl) O) (pm (ShPlan.mk Q (descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs
          getS startS cF ch Q tests) pLast rad2 rad5 Wr fl) O) (own (ShPlan.mk Q (descAt oH mkL Zp
          lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) pLast rad2 rad5 Wr fl) O) true T.p₂
          T.l₂ i a →
      x.ior.red.out a τ = some b → XD pLast (i + 1) b.1.2 = true := by
  subst htests
  have e : (descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q [Seat.onGu (proximityTestKind guardedProximityTestParts
      πA : Block T12 Unit), Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block T12 Unit)]).shared.blocksInOrder.map below
      = rowOf ch (bk (ShPlan.mk Q (descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q
      [Seat.onGu (proximityTestKind guardedProximityTestParts πA : Block T12 Unit), Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block T12
                                     Unit)]) pLast rad2 rad5 Wr fl) 0) (bk (ShPlan.mk Q (descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs
                                     getS startS cF ch Q [Seat.onGu (proximityTestKind guardedProximityTestParts πA : Block T12 Unit), Seat.onGomega (proximityTestKind guardedProximityTestParts
                                                                    πB : Block T12 Unit)]) pLast rad2 rad5 Wr fl) 1) (bk (ShPlan.mk Q (descAt oH mkL Zp lt st₂ en₂
                                                                    ok₂ fo₂ si₂ Bs getS startS cF ch Q [Seat.onGu (proximityTestKind guardedProximityTestParts πA : Block T12 Unit),
                                                                    Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block T12 Unit)]) pLast rad2 rad5 Wr fl) 2) (bk (ShPlan.mk Q
                                                                                                   (descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q [Seat.onGu (proximityTestKind guardedProximityTestParts πA :
                                                                                                   Block T12 Unit), Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block T12 Unit)]) pLast rad2 rad5 Wr fl) 3)
      (bk (ShPlan.mk Q (descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q [Seat.onGu
      (proximityTestKind guardedProximityTestParts πA : Block T12 Unit), Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block T12 Unit)]) pLast
      rad2 rad5 Wr fl) 4) (bk (ShPlan.mk Q (descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS
      cF ch Q [Seat.onGu (proximityTestKind guardedProximityTestParts πA : Block T12 Unit), Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block
                                     T12 Unit)]) pLast rad2 rad5 Wr fl) 5) (bk (ShPlan.mk Q (descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂
                                     si₂ Bs getS startS cF ch Q [Seat.onGu (proximityTestKind guardedProximityTestParts πA : Block T12 Unit), Seat.onGomega (proximityTestKind
                                                                    guardedProximityTestParts πB : Block T12 Unit)]) pLast rad2 rad5 Wr fl) 6) (bk (ShPlan.mk Q (descAt oH mkL Zp
                                                                                     lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q [Seat.onGu (proximityTestKind guardedProximityTestParts πA : Block T12 Unit),
                                                                                     Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block T12 Unit)]) pLast rad2 rad5 Wr fl) 7) πA πB
      VerifiableInference.Desc.K12.Seat.last := by
    rw [← rowOf_is ch _ _ _ _ _ _ _ _ _ _ _ Q (tests_hbl8 (ShPlan.mk Q (descAt oH mkL Zp lt st₂ en₂
        ok₂ fo₂ si₂ Bs getS startS cF ch Q [Seat.onGu (proximityTestKind guardedProximityTestParts πA : Block T12 Unit),
        Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block T12 Unit)]) pLast rad2 rad5 Wr fl) hT)]
    rfl
  have hq := steps_of_desc hD
  rw [e] at hq
  exact xd_of_steps (ShPlan.mk Q (descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q
      [Seat.onGu (proximityTestKind guardedProximityTestParts πA : Block T12 Unit), Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block T12
                                     Unit)]) pLast rad2 rad5 Wr fl) O (tests_hUw _ hT) (tests_hS _ hT) _ _ _ _ _ _ _ _ (tests_hbl8
                                     _ hT)
    (tests_hlU _ hT) (tests_hlO _ hT) (tests_hm _ hT) (tests_hp8 _ hT) (tests_hok _ hT)
    (tests_hC2 _ hT) (tests_hC5 _ hT) (tests_pyU _ hT) (tests_pyO _ hT) (tests_pyS _ hT) _ _ heA
    ha1A hftA heB ha1B hftB (tests_hl _ hT) (tests_hsU _ hT) _
    (form_h0 ch _ _ _ _ _ _ _ _ _ _ _) (form_h8 ch _ _ _ _ _ _ _ _ _ _ _)
    (form_h9 ch _ _ _ _ _ _ _ _ _ _ _) (form_h10 ch _ _ _ _ _ _ _ _ _ _ _)
    (form_h11 ch _ _ _ _ _ _ _ _ _ _) (form_len ch _ _ _ _ _ _ _ _ _ _ _) (tests_hpS _ hT)
    T.p₂ T.l₂ hq

/-- **hXD in the goals' scope, at the value that is laid.** -/
theorem xd_in_scope {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles} {D' : WholeD} {r : LPFD.Full.RunPF}
    {x : LinSized} (hS : VerifierAndGoals.InScope S = true)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D', r))
    (hpins : ∀ Z, ProofFile.pureRoad.pub o S.pol S.lay S.KL = .ok Z →
      VerifiableInference.PlanWritten.sizedPinnedAt Z.p.X.P Z.p.chains.made = true ∧
        VerifiableInference.PlanWritten.firstPinnedAt Z.p.X.P Z.first = true)
    (hx : realSized = some (x, codesFull2)) :
    ∃ (Z : ProofFile.Pub) (N : H2U.Places4) (c : VerifiableInference.Desc.Chain First.S ProofFile.Cl),
      ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) ∧
      ∀ {P₀ Cells Tok : Type}
        (O : ShOpen P₀ (ProofFile.InstPub × First.S) Cells Tok (planAt Z N (descN o ProofFile.pureRoad.links
                  guardedProximityTestParts Z N c)).Q)
        {D : WholeD} {all : List LeftT} {X₁ X₂ : Type}
        (T : ThreeAt (ckP .two) D all (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) X₁ X₂ (Wit Cells
                                   Tok MsgT)),
        OfDesc (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) T →
        ∀ i x, (T.p₂ :: T.l₂)[i]? = some x → ∀ a τ b,
          onQ₂ (nums (planAt Z N (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c)) O) (pm (planAt Z N
                                     (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c)) O)
            (own (planAt Z N (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c)) O) true T.p₂ T.l₂ i a →
          x.ior.red.out a τ = some b → XD (planAt Z N (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c)).p
              (i + 1) b.1.2 = true := by
  obtain ⟨Z, N, c, nO, _, _, hF, hO, hT, _, ⟨u1, u2, u3⟩, o1, o2, o3⟩ :=
    front_in_scope hS hL hpins hx
  exact ⟨Z, N, c, hF, fun O _ _ _ _ T hD =>
    xd_at_seat o Z N (H2K.JointK.secondN guardedProximityTestParts Z N) c nO hO hT u1 u2 u3 o1 o2 o3 O T hD⟩

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.steps_of_desc
#print axioms Desc.K14.Law.Sh.xd_at_seat
#print axioms Desc.K14.Law.Sh.chainOk_descAt
#print axioms Desc.K14.Law.Sh.xd_at_field
#print axioms Desc.K14.Law.Sh.xd_in_scope
