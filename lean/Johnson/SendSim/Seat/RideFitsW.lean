-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/RideFitsW.lean: if the maker of the proof file's description returns and the
description passes its own tests on the plan, the public test wStageB accepts, so every job of
lotJobs and wJobs fits its place.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. The three theorems on the description (fits_at_lots_plan, wStage_of_plan,
beside_of_plan) have the premises IM.Open and F.planOk = true, and no other.
  fits_at_lots_plan  Every job of lotJobs and wJobs fits its place (sendFits). It is fits_at_lots
                     (Johnson/SendSim/Seat/RideFits.lean) with its premise on wStageB met.
  wStage_of_plan     wStageB Z.first.codes Z.first.lin accepts (RideFits.lean): the first stage of
                     the proximity test on the request's own group has at least one row variable (a
                     stage with k row variables has 2 ^ k main rows), no more mask row variables
                     than row variables, and a mask code that is long enough for the table of the
                     first fold's fresh mask.
  beside_of_plan     The part of the tests on the whole file that the description keeps with the
                     shared chain accepts (OkD.AtC.beside, Johnson/Desc/OnPlan/OkBesideC.lean).
  first_stage_of_ioppOk   For all codes, stages and numbers of answers: if the stages of a proximity
                     test fit together (ioppOk, OnBytes/Iop/Prox.lean), the first stage has the
                     three properties that wStageB asks.
  wStage_full, wStage_full_some   Checked by evaluation in Lean's kernel, with no premise: wStageB
                     accepts at the full-size codes and shape of the linear claims, which the
                     library states as values (proofSizedFull.codes, proofSizedFull.batch.shape,
                     Johnson/Desc/Ok/PlanWritten/SizedLit.lean), and that shape's test has a first
                     stage, so the test is not vacuous there.
  wStage_rejects_k, wStage_rejects_h, wStage_rejects_columns, wStage_accepts   Three negative tests
                     and their control, at made-up values. Each negative test fails one clause of
                     wStageB alone (by inspection, not proved): no row variable; more mask row
                     variables than row variables; a mask code that is too short for the table.

How it fits. That a job fits its place is no premise of Spec.fieldsAtLots
(Johnson/SendSim/Seat/AtDescLots.lean). But where a job does not fit, what it discloses is the error
value on both sides of both equations: exact then says nothing, and fresh speaks of the sender's
coins alone. RideFits.lean leaves one public test open, at the request's own table. Here it follows
from the premises that fits_at_lots already has. Meant as steps toward index privacy
(Johnson/WholeKey/Statement.lean); nothing in this folder derives index privacy from them. Not one
of the release's goal statements.

How it is proved. No sub-protocol's own test on the plan asks wStageB; the test on the whole file
does. F.planOk has F.fileOk among its conjuncts. F.fileOk has the shared chain's fileOk among its
conjuncts, and that has OkD.AtC.beside. One conjunct of beside, stagesW (through proximityTestKind), is ioppOk at
the stages of the test on the request's own group. That conjunct reads the shared chain's parameters
as read back. They have the first chain's codes and shape of the linear claims
(Params.ProofChains.read_codes, OnBytes/Model/VerifyRead.lean; read_lin,
OnBytes/Model/VerifyShape.lean; P2R0.read_at_pub, Johnson/P2R0R/SizedIsRead.lean). ioppOk asks for
at least two stages. So under these premises the test on the request's own group has a first stage,
and wStageB is not vacuous there (w_fold_some, RideTies.lean), and that stage is not the last.

Limits.
That F.planOk holds at given public files is not shown here (FitsAtLots.lean). At the hash function
OnBytes.secondHashFunction, at every public file in the goals' scope at which the library's gate accepts, the
maker returns and its description passes its tests on the plan (plan_of_live, ReadsAtLive.lean;
returns_of_live, AtDesc.lean). That the gate accepts is a theorem of the side library at the
stored full-size files, under both named policies and every policy within the four bounds of
VerifierAndGoals.inScope_zAt (theLive_zFull, AtFullSide/Top/LiveAtFull.lean; theLive_zGap,
theLive_zAt, LiveAtPolicies.lean
beside it).
Of the three public tests at the request's own table (the fit, the book, the queried positions),
only the fit is met here. The test on queried positions accepts, at the hash function
OnBytes.secondHashFunction, at all public files in the goals' scope at which the library's gate accepts
(reads_of_live, ReadsAtLive.lean). Of the test on the book, in scope, where the gate accepts, at the
book that the maker onlineProverFromPublicFiles returns: door_closed (AtFullSide/M1/LotsThinClosed.lean, side library).
That the proximity test which is meant to use this fresh mask folds at the first stage's k and h is
proved in Johnson/SendSim/Seat/RideTies.lean (w_member_tie), not here. That test is the
description's sub-protocol of the kind K12 on the last chain. Which message that sub-protocol takes
as its mask is a number in the verifier's state, not in the plan, and nothing ties it to the table
that is sent along.
The two lists hold the places of the kind K1 on the first chain. The chain's other sendings of new
tables, of the kinds K2 and K12, are not covered.
The two full-size values are literals that a program wrote from Lean's own print. That they are what
the planner makes of given files is not proved (SizedLit.lean, Limits). Only wStage_full and
wStage_full_some read them. wStageB is not evaluated at the stored small example set.
For all other limits see AtDescLots.lean.
-/
import Johnson.SendSim.Seat.RideFits
import Johnson.Desc.Ok.PlanWritten.SizedLit
import Johnson.P2R0R.SizedIsRead

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At
open VerifiableInference.PlanWritten (proofSizedFull)

variable {X Xi : Type}

/-! ## From the description's own tests on the plan -/

/-- If the stages of a proximity test fit together (ioppOk, OnBytes/Iop/Prox.lean), its first stage
has at least one row variable, no more mask row variables than row variables, and a mask code that
is long enough for the table of the first fold's fresh mask. -/
theorem first_stage_of_ioppOk {codes : Codes} {stages : List IoppStage} {answers : Nat}
    (h : ioppOk codes stages answers = true) :
    stages.head?.all (fun s => decide (1 ≤ s.k) && decide (s.h ≤ s.k) &&
      decide (foldMaskColumns s.k s.h ≤ (codes.mask.getD s.maskCode default).ell)) = true := by
  unfold ioppOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hl, -⟩, hs⟩ := h
  cases stages with
  | nil => rfl
  | cons s rest =>
    have hne : rest.isEmpty = false := by
      cases rest with
      | nil => simp at hl
      | cons _ _ => rfl
    unfold ioppStagesOk at hs
    rw [Bool.and_eq_true, hne] at hs
    have h1 := hs.1
    unfold ioppStageOk at h1
    split at h1
    · rename_i c zk hc hz
      simp only [Bool.and_eq_true, stageOk, decide_eq_true_eq, Bool.false_eq_true, if_false] at h1
      have hz' : codes.mask.getD s.maskCode default = zk := by
        obtain ⟨hlt, he⟩ := Array.getElem?_eq_some_iff.1 hz
        unfold Array.getD
        split
        · exact he
        · rename_i hn
          exact absurd hlt hn
      simp only [List.head?_cons, Option.all_some, Bool.and_eq_true, decide_eq_true_eq]
      rw [hz']
      exact ⟨⟨h1.1.2.1, h1.1.1.2.2⟩, h1.1.2.2⟩
    · cases h1

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- If the maker returns and the description passes its tests on the plan, the part of the tests on
the whole file that the description keeps with the shared chain accepts (OkD.AtC.beside,
Johnson/Desc/OnPlan/OkBesideC.lean). -/
theorem beside_of_plan (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) :
    VerifiableInference.OnPublicFiles.OkD.AtC.beside Z.p.X Z.p.chains = true := by
  have hA : _root_.Desc.K14.sharedSeatAt Z = some A := O.shared
  unfold _root_.Desc.K14.sharedSeatAt at hA
  cases hN : H2U.placesOfMade Z.made with
  | error e =>
    rw [hN] at hA
    cases hA
  | ok N =>
    rw [hN] at hA
    obtain rfl := Option.some.inj hA
    have e := O.desc
    subst e
    have hf := ((FileDescription.planOk_ok _).1 hp).fileOk
    simp only [ProofFile.fileDescBy, _root_.Desc.K14.sharedSeatOf, Bool.and_eq_true] at hf
    exact hf.1.1.1.2

/-- **If the maker returns and the description passes its tests on the plan, wStageB accepts.** -/
theorem wStage_of_plan (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) :
    wStageB Z.first.codes Z.first.lin = true := by
  have hb := beside_of_plan O hp
  unfold VerifiableInference.OnPublicFiles.OkD.AtC.beside VerifiableInference.OnPublicFiles.OkD.AtC.k12 at hb
  simp only [Bool.and_eq_true] at hb
  have hW : ioppOk Z.p.chains.proof.shared.codes Z.p.chains.proof.shared.lin.testOwn
      Z.p.chains.proof.second.given.plan.samples = true := hb.1.1.1.1.1.2
  have hr := P2R0.read_at_pub O.pub
  rw [Params.ProofChains.read_codes hr, Params.ProofChains.read_lin hr] at hW
  exact first_stage_of_ioppOk hW

/-- **Every job of the two lists fits its place, if the maker returns and the description passes its
tests on the plan.** -/
theorem fits_at_lots_plan (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true)
    (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) {J : SendJob (PlaceIn Xi) X}
    (hJ : J ∈ lotJobs no D Z Bs.G₀ ++ wJobs no D Z Bs.G₀) : sendFits J.P J.ride = true :=
  fits_at_lots O hp (wStage_of_plan O hp) no D hJ

end

/-! ## The test at the library's full-size values, and at made-up values -/

/-- wStageB accepts at the library's full-size codes and shape of the linear claims. -/
theorem wStage_full : wStageB proofSizedFull.codes proofSizedFull.batch.shape = true := by
  decide +kernel

/-- At that shape the proximity test on the request's own group has a first stage, so wStage_full is
not vacuous. -/
theorem wStage_full_some : proofSizedFull.batch.shape.testOwn.head?.isSome = true := by
  decide +kernel

/-- Made-up codes: no base code and one mask code of message length 4. -/
def stageCodes : Codes := ⟨#[], #[⟨3, 4, 1⟩]⟩

/-- A made-up shape whose test on the request's own group has one stage, with k row variables (2 ^ k
main rows) and h mask row variables, at mask code 0. -/
def stageShape (k h : Nat) : LinShape := { (default : LinShape) with testOwn := [⟨0, 0, k, h⟩] }

/-- A negative test: a first stage without a row variable is rejected. -/
theorem wStage_rejects_k : wStageB stageCodes (stageShape 0 0) = false := by decide +kernel

/-- A negative test: a first stage with more mask row variables than row variables is rejected. -/
theorem wStage_rejects_h : wStageB stageCodes (stageShape 1 2) = false := by decide +kernel

/-- A negative test: a first stage whose table needs 5 columns is rejected at a mask code of message
length 4. -/
theorem wStage_rejects_columns : wStageB stageCodes (stageShape 2 0) = false := by decide +kernel

/-- The control: one row variable and no mask row variable are accepted at the same codes. So the
three rejections come from the stage's numbers, not from the codes. -/
theorem wStage_accepts : wStageB stageCodes (stageShape 1 0) = true := by decide +kernel

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.wStage_full
#print axioms OnBytes.SendSim.Seat.wStage_full_some
#print axioms OnBytes.SendSim.Seat.first_stage_of_ioppOk
#print axioms OnBytes.SendSim.Seat.beside_of_plan
#print axioms OnBytes.SendSim.Seat.wStage_of_plan
#print axioms OnBytes.SendSim.Seat.fits_at_lots_plan
#print axioms OnBytes.SendSim.Seat.wStage_rejects_k
#print axioms OnBytes.SendSim.Seat.wStage_rejects_h
#print axioms OnBytes.SendSim.Seat.wStage_rejects_columns
#print axioms OnBytes.SendSim.Seat.wStage_accepts
