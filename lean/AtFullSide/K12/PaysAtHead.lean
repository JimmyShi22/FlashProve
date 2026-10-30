-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/PaysAtHead.lean: under the library's head, what onlineProverFromPublicFiles returns at any filling meets
the written book and description, and the planner's four records for the proximity tests are the
written records, whole.

  fourU_written, fourO_written, fourW_written   the three records of the later chains are piUFull,
                     piOFull, piWFull at their places
  sendPub_plan       the sendings' public data have the shared chain's own parameters
  lays_at_head       laysB accepts at the public fields of the tests on G_u and G_omega, at the
                     sendings' own members, at the written book
  book_of_atPure     onlineProverFromPublicFiles's book is the book of the written description
  alike_at_atPure    onlineProverFromPublicFiles's description is alike to the written one

By what. p12_four_at_head (Johnson/AtFull/Shape/TestNumbersAtHead.lean); lays_U, lays_O
(AtFullSide/K12/LaysOnU.lean, LaysOnOmega.lean) at the typed sizes, with written_at_head and qAt_written
(K12/FitAtHead.lean); atPure_book_at_head, bookWhole_same_at_made (Honest/K14/); planAlike_at_head
(Honest/K14/WrittenAtHead.lean).

Limits.
- Conditional on the head. Where onlineProverFromPublicFiles enters, that it returns is a premise.
- All of it is public data: no job's rows, trees or state on entry are read.
- Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.PaysForm
import AtFullSide.K12.LaysAtBookW
import AtFullSide.K14.BookWholeWritten
import Johnson.AtFull.Shape.TestNumbersAtHead
import Johnson.Desc.ProofFile.Honest.K12.FitAtHead
import Johnson.Desc.ProofFile.Honest.K14.AtFilling
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.Desc.ProofFile.Honest.K14.BookForAtPure
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.Desc.ProofFile.Honest.AtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain PlanAlike)
open VerifiableInference.Desc.K12 (P12)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open H2K.Member (piUFull piOFull piWFull)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull codesFull2)
open P5J (AtMg AtMgA TS)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head the record of the test on G_u is the written one at its place.** -/
theorem fourU_written (h : AtMg o Z D r Zp Np cF) :
    (fourOf Np).U = ({ piUFull with place := placeU } : P12) := by
  have e := (Johnson.AtFull.Shape.p12_four_at_head h).2.1
  have e' : H2U.p12FoldedOfMade Zp.made 9 = (fourOf Np).U := by
    unfold H2U.p12FoldedOfMade
    rw [h.laid.places] <;> rfl
  exact e'.symm.trans e

/-- **The record of the test on G_omega.** -/
theorem fourO_written (h : AtMg o Z D r Zp Np cF) {p : P12} (hp : (fourOf Np).O = some p) :
    p = ({ piOFull with place := placeO } : P12) := by
  have e := (Johnson.AtFull.Shape.p12_four_at_head h).2.2.1
  have hp' : Np.O.map (H2U.proximityTestParametersAt placeO) = some p := hp
  have e' : H2U.p12OmegaOfMade Zp.made 10 = p := by
    unfold H2U.p12OmegaOfMade
    rw [h.laid.places]
    show (Np.O.map (H2U.proximityTestParametersAt placeO)).getD (H2U.noP12 placeO) = p
    rw [hp'] <;> rfl
  exact e'.symm.trans e

/-- **The record of the last chain's test.** -/
theorem fourW_written (h : AtMg o Z D r Zp Np cF) :
    (fourOf Np).W = ({ piWFull with place := placeW } : P12) := by
  have e := (Johnson.AtFull.Shape.p12_four_at_head h).2.2.2
  have e' : H2U.p12OwnOfMade Zp.made 2 = (fourOf Np).W := by
    unfold H2U.p12OwnOfMade
    rw [h.laid.places] <;> rfl
  exact e'.symm.trans e

/-- **The sendings' public data have the shared chain's own parameters.** -/
theorem sendPub_plan (h : AtMg o Z D r Zp Np cF) {A : ProofFile.Honest.K14.SendPub}
    (hA : sendPub Zp = some A) : A.P = VerifiableInference.Desc.K1.qAt Zp Np := by
  unfold sendPub at hA
  rw [(ProofFile.Honest.K14.readers_at Zp Np h.laid.places).1] at hA
  change Option.map _ _ = some A at hA
  obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.1 hA
  rfl

/-- The members of the test on G_u read of the sendings' data their codes and shape alone. -/
theorem membersU_plan (A : ProofFile.Honest.K14.SendPub) :
    membersU A = membersU (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S) := rfl

/-- The like at G_omega. -/
theorem membersO_plan (A : ProofFile.Honest.K14.SendPub) :
    membersO A = membersO (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S) := rfl

set_option maxRecDepth 1000000 in
/-- **laysB accepts at the two shared tests' public fields**, at the sendings' own members. -/
theorem lays_at_head (h : AtMg o Z D r Zp Np cF) {A : ProofFile.Honest.K14.SendPub}
    (eA : A.P = VerifiableInference.Desc.K1.qAt Zp Np) :
    laysB bookW 1 (bareJob ({ piUFull with place := placeU } : P12) (membersU A) freshU :
      TestJob Unit Unit) = true ∧
    laysB bookW 1 (bareJob ({ piOFull with place := placeO } : P12) (membersO A) freshO :
      TestJob Unit Unit) = true := by
  obtain ⟨y, hy, Wr⟩ := ProofFile.Honest.K12.Light.written_at_head h
  have eP := eA.trans (ProofFile.Honest.K12.Light.qAt_written Wr Np)
  have ec : A.P.codes = codesFull2 := congrArg (fun p : Desc.K14.P14 => p.codes) eP
  have eS : A.P.S = y.shape := congrArg (fun p : Desc.K14.P14 => p.S) eP
  have kU := lays_U
  have kO := lays_O
  rw [hy] at kU kO
  simp only [Option.all] at kU kO
  rw [membersU_plan A, membersO_plan A, ec, eS]
  exact ⟨kU, kO⟩

variable {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **onlineProverFromPublicFiles's book is the book of the written description.** General in the filling. -/
theorem book_of_atPure (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {B₀ : ProverCoinCounts}
    (h₀ : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B₀) : A.B = B₀ :=
  Except.ok.inj ((ProofFile.Honest.K14.atPure_book_at_head h hA).symm.trans
    (ProofFile.Honest.K14.bookWhole_same_at_made h₀ h))

/-- **onlineProverFromPublicFiles's description is alike to the written one.** General in the filling. -/
theorem alike_at_atPure (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) : PlanAlike WP A.F := by
  rw [(atPure_at_laid h.laid hA).2]
  exact ProofFile.Honest.K14.planAlike_at_head h

end AtFullSide.K12

#print axioms AtFullSide.K12.fourU_written
#print axioms AtFullSide.K12.fourO_written
#print axioms AtFullSide.K12.fourW_written
#print axioms AtFullSide.K12.sendPub_plan
#print axioms AtFullSide.K12.membersU_plan
#print axioms AtFullSide.K12.membersO_plan
#print axioms AtFullSide.K12.lays_at_head
#print axioms AtFullSide.K12.book_of_atPure
#print axioms AtFullSide.K12.alike_at_atPure
