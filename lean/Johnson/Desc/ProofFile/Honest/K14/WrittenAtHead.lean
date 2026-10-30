-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/WrittenAtHead.lean: IN THE GOALS' SCOPE, A DESCRIPTION THAT
PASSES, AT THESE FILES' PARAMETER FILE, THE PROOF FILE's ENTRY TEST ON THE WRITTEN ROUNDS
(seatPinnedProof) DECLARES THE LIBRARY's WRITTEN DECLARED ROUNDS (declProofFull), ALL THREE LISTS
WHOLE; IF IT ALSO PASSES THE TEST ON THE CUT (cutIs) AND THE TESTS ON THE PLAN (planOk), IT IS ALIKE
(PlanAlike, Johnson/AtFull/ProofPlan/PlanAlike.lean) TO THE LIBRARY's WRITTEN DESCRIPTION WP
(Johnson/AtFull/ProofPlan/WP.lean); SO UNDER THE LIBRARY's LaidAt (Johnson/P5J/LaidOpens.lean) THE
PROOF FILE's OWN DESCRIPTION IS. Statements, each with its proof: calls alone; no definition. It
imports files of this library and Johnson/Desc/ProofFile/Honest/K14/WrittenBack.lean.

  decl_of_seat    **F.roundsDeclaredByBlocks = declProofFull**: general in the description: the entry test's yes
                  (seatPinnedProof, Johnson/Desc/Ok/PlanWritten/Test.lean) gives, in scope, that
                  writtenOf lays F's declared rounds as the written rounds dryProofFull (the
                  library's seat_in_scope, Johnson/Goal/Numbers/PlanWrittenDescScope.lean); the
                  library's written_proof (Johnson/AtFull/ProofRows/WrittenProof.lean) says the same
                  of declProofFull (two names, one term: decl_same,
                  Johnson/AtFull/ProofPlan/DeclSame.lean); writtenOf is injective where it returns
                  (writtenOf_inj, WrittenBack.lean)
  depth_of_seat   F.tableDepth = 32: seat_in_scope's second part
  planAlike_of_seat   **PlanAlike WP F**: the library's planAlike_of_cut
                  (Johnson/AtFull/ProofPlan/WrittenDesc.lean) with its ten premises met: the three
                  cuts (cutIs, Johnson/Desc/Ok/PlanWritten/CutTest.lean; cutIs_eq, CutTestLaws.lean
                  there); the declared rounds; the plans, each sub-protocol's own test and fileOk
                  (out of planOk: FileDescription.planOk_ok, Johnson/Desc/RunLaws.lean); the depth
  decl_at_laid, pub_decl_at_laid, depth_at_laid, planAlike_at_laid   the same at the proof file's
                  own description under LaidAt; the public part's declared rounds are declProofFull
                  too
  alike_shared_at_laid, alike_last_at_laid   two fields of PlanAlike: the shared and the second
                  chain's flat lists
  planAlike_at_head   the same under the library's head (P5J.AtMgA, Johnson/P5J/MgAtAll.lean)

Limits. WHICH WAY IT RUNS: planOk IS SPENT HERE, NOT SHOWN: of planAlike_of_cut's ten premises four
come out of planOk alone, five out of the two entry tests, and one, the plans, out of both. With the
library's FileDescription.planOk_alike₂ (PlanAlike.lean) and wp_planOk
(Johnson/AtFull/ProofPlan/WPPlanOk.lean) this gives back the very planOk that was put in: NOTHING IS
PAID HERE TOWARD SHOWING THAT ANY FILES MEET LaidAt. (The library shows that at its written
full-size files: theProofLaid_zFull_returns, AtFullSide/Top/LiveAtFull.lean; for the head:
headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean.) What is new is one step: the first entry
test's yes, an equation between WRITTEN rounds, becomes the equation between DECLARED rounds. The
full size alone (the goals' scope). PlanAlike says what the tests on the plan read: of a
sub-protocol: place, rounds, oracles, before, and an arrow on its own test; of the file: an arrow on
fileOk, the plans, the depth: nothing on what a sub-protocol decides. Nothing is evaluated in this
file; beneath it stand the evaluations of written_proof, of seat_in_scope's own ground and, under
LaidAt, of cutIs_of_laid's (Johnson/Goal/Skeleton/CutIsOfLaid.lean). Nothing on soundness; nothing
on what is or is not hidden; no property.

Nearest in the library. The other way round, from the declared equation to the written one:
hw_of_planOk (Johnson/AtFull/ProofRows/Hw.lean). The equations chain by chain, FROM IN FRONT OF
LaidAt, each under hypotheses of its own: decl_first_at_scope
(Johnson/Desc/ProofFile/Law/Skel/Full/DeclAtScope.lean), shared_decl
(Johnson/AtFull/Rounds/Shared.lean), and the second chain's in Johnson/AtFull/Rounds/Second.lean:
decl_at_laid has all three at once because it stands BEHIND LaidAt.
Johnson/AtFull/Top/OwedLeft2.lean's mark that F.roundsDeclaredByBlocks = declProofFull has no payer in front of LaidAt
STAYS TRUE: decl_at_laid asks for LaidAt's entry tests. entries_at and entries_all_at
(Johnson/AtFull/Rounds/EntriesW.lean) take pub_decl_at_laid's equation as their premise.
-/
import Johnson.Desc.ProofFile.Honest.K14.WrittenBack
import Johnson.AtFull.ProofPlan.DeclSame
import Johnson.Goal.Skeleton.CutIsOfLaid
import Johnson.Goal.Numbers.PlanWrittenDescScope
import Johnson.Desc.RunLaws
import Johnson.Desc.Laid.ProofAsksLaw
import Johnson.P5J.DeclIsPub
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Chain FileDescription PlanAlike Alike₂)
open VerifiableInference.PlanWritten (seatPinnedProof cutIs cutIs_eq cutFirstFull cutSharedFull
  cutSecondFull)
open P2Law.ProofPlan (WP declProofFull planAlike_of_cut)
open VerifierAndGoals (InScope)
open P5J (LaidAt F0T TS)

/-! ## General in the description -/

section
variable {Xi : Type} {F : FileDescription Xi} {Z : VerifierAndGoals.PublicFiles}

/-- **IN SCOPE, A DESCRIPTION THAT PASSES THE ENTRY TEST ON THE WRITTEN ROUNDS DECLARES THE
LIBRARY's WRITTEN DECLARED ROUNDS (declProofFull)**: all three lists, whole. -/
theorem decl_of_seat (scope : InScope Z = true) (hs : seatPinnedProof Z.pol F = true) :
    F.roundsDeclaredByBlocks = declProofFull :=
  (writtenOf_inj (VerifiableInference.PlanWritten.seat_in_scope _ F Z scope hs).1
    Johnson.AtFull.ProofRows.written_proof).trans Johnson.AtFull.ProofPlan.decl_same

/-- In scope, the depth of the stored parts of a description that passes that entry test is 32. -/
theorem depth_of_seat (scope : InScope Z = true) (hs : seatPinnedProof Z.pol F = true) :
    F.tableDepth = 32 :=
  (VerifiableInference.PlanWritten.seat_in_scope _ F Z scope hs).2.1

/-- **IN SCOPE, A DESCRIPTION THAT PASSES THAT ENTRY TEST, THE TEST ON THE CUT AND THE TESTS ON THE
PLAN IS ALIKE TO THE WRITTEN DESCRIPTION.** -/
theorem planAlike_of_seat (scope : InScope Z = true) (hs : seatPinnedProof Z.pol F = true)
    (hc : cutIs F = true) (hp : F.planOk = true) : PlanAlike WP F := by
  have c := cutIs_eq hc
  have hD := decl_of_seat scope hs
  have k := (FileDescription.planOk_ok F).1 hp
  have hP : F.plans = declProofFull :=
    (Prod.ext k.decl₁ (Prod.ext k.decl₂ k.decl₃) : F.roundsDeclaredByBlocks = F.plans).symm.trans hD
  show PlanAlike (P2Law.ProofPlan.wOf cutFirstFull cutSharedFull cutSecondFull declProofFull 32) F
  exact planAlike_of_cut c.1 c.2.1 c.2.2 hD hP (depth_of_seat scope hs)
    (fun b hb => (k.blocks₁ b hb).1) (fun b hb => (k.blocks₂ b hb).1)
    (fun b hb => (k.blocks₃ b hb).1) k.fileOk

end

/-! ## At the proof file's own description -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **IN SCOPE, UNDER LaidAt, THE DESCRIPTION's DECLARED ROUNDS ARE THE LIBRARY's WRITTEN DECLARED
ROUNDS (declProofFull).** -/
theorem decl_at_laid (scope : InScope Z = true) (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) :
    (F0T o Zp Np cF).roundsDeclaredByBlocks = declProofFull :=
  decl_of_seat scope (LPFD.asks_written L.asks)

/-- In scope, under LaidAt: so are the public part's declared rounds. -/
theorem pub_decl_at_laid (scope : InScope Z = true)
    (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) : Zp.D = declProofFull :=
  (P5J.LaidAt.decl L).symm.trans (decl_at_laid scope L)

/-- In scope, under LaidAt: the depth of the stored parts is 32. -/
theorem depth_at_laid (scope : InScope Z = true) (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) :
    (F0T o Zp Np cF).tableDepth = 32 :=
  depth_of_seat scope (LPFD.asks_written L.asks)

/-- **IN SCOPE, UNDER LaidAt, THE DESCRIPTION IS ALIKE TO THE WRITTEN DESCRIPTION.** -/
theorem planAlike_at_laid (scope : InScope Z = true)
    (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) : PlanAlike WP (F0T o Zp Np cF) :=
  planAlike_of_seat scope (LPFD.asks_written L.asks) (P5J.cutIs_of_laid scope L) L.planOk

/-- In scope, under LaidAt: the shared chains' flat lists are alike, sub-protocol by
sub-protocol. -/
theorem alike_shared_at_laid (scope : InScope Z = true)
    (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) :
    List.Forall₂ Alike₂ WP.shared.blocksInOrder (F0T o Zp Np cF).shared.blocksInOrder :=
  (planAlike_at_laid scope L).shared

/-- In scope, under LaidAt: the second chains' flat lists are alike, sub-protocol by
sub-protocol. -/
theorem alike_last_at_laid (scope : InScope Z = true)
    (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) :
    List.Forall₂ Alike₂ WP.second.blocksInOrder (F0T o Zp Np cF).second.blocksInOrder :=
  (planAlike_at_laid scope L).second

/-- **Under the library's head (P5J.AtMgA) the description is alike to the written description.** -/
theorem planAlike_at_head {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA o Z D r Zp Np cF x₀) : PlanAlike WP (F0T o Zp Np cF) :=
  planAlike_at_laid h.scope h.laid

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.decl_of_seat
#print axioms ProofFile.Honest.K14.depth_of_seat
#print axioms ProofFile.Honest.K14.planAlike_of_seat
#print axioms ProofFile.Honest.K14.decl_at_laid
#print axioms ProofFile.Honest.K14.pub_decl_at_laid
#print axioms ProofFile.Honest.K14.depth_at_laid
#print axioms ProofFile.Honest.K14.planAlike_at_laid
#print axioms ProofFile.Honest.K14.alike_shared_at_laid
#print axioms ProofFile.Honest.K14.alike_last_at_laid
#print axioms ProofFile.Honest.K14.planAlike_at_head
