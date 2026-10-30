-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WJointBook.lean: under the head, at the maker's book, the
three public premises of tree2_at_W (WJointArms.lean) on Omega's sending: hdue, hcover, hdepth.

  takes_raw            what the sending's part takes is its row of the shared chain's written rows: an
                       evaluation in Lean's kernel at the typed sizes
  takes_plan           what the part takes reads the codes and the shape alone
  omega_due_head, omega_cover_head, omega_depth_head   the three

By what. covers_head (BookLines.lean), cut_of_cover, shapes_O (TreesSentBeforeTestAtU.lean), sendTable_depth
(K12/DepthsOfText.lean).

Limits. At An.P = qAt Zp Np. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.BookLines
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TreesSentBeforeTestAtU
import Johnson.Desc.ProofFile.Honest.K12.DepthsOfText
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Members
import AtFullSide.K14.RawSmallWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K14 (SendPub jobOmega sendPlace sendingPart sendTable Ask)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K1 (realSized)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open ProofFile.Honest.K12.Light (written_at_head qAt_written)
open ProofFile.Honest.K12.AtProof (senderO)

/-- **What the sending's part takes is its written row**, at the typed sizes. -/
theorem takes_raw : (realSized.all fun q =>
    decide ((sendingPart (jobOmega (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape))).takes =
      dueAt AtFullSide.K14.rawRowsSharedW senderO)) = true := by decide +kernel

/-- What the part takes reads the codes and the shape alone. -/
theorem takes_plan (A : SendPub) : (sendingPart (jobOmega A)).takes =
    (sendingPart (jobOmega (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S))).takes := rfl

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- hdue. -/
theorem omega_due_head (h : P5J.AtMg o Z D r Zp Np cF) {An : SendPub} (hP : An.P = K1.qAt Zp Np) :
    (sendingPart (jobOmega An)).takes = dueAt AtFullSide.K14.rawRowsSharedW senderO := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have a := takes_raw
  rw [hx] at a
  simp only [Option.all_some, decide_eq_true_eq] at a
  rw [takes_plan, hP, qAt_written Wr Np]
  exact a

variable {Bk : ProverCoinCounts}

/-- The row covers what the part takes, at any number of "LIN point". -/
theorem omega_takes_cover (h : P5J.AtMg o Z D r Zp Np cF)
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk) {An : SendPub} (hP : An.P = K1.qAt Zp Np) :
    takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega An) = true := by
  obtain ⟨P, a⟩ := An
  obtain rfl : P = K1.qAt Zp Np := hP
  have c := (covers_head h hB).2.1
  unfold takesCover at c ⊢
  rw [takes_plan ⟨K1.qAt Zp Np, 0⟩] at c
  rw [takes_plan ⟨K1.qAt Zp Np, a⟩]
  exact c

/-- hcover. -/
theorem omega_cover_head (h : P5J.AtMg o Z D r Zp Np cF)
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk) {An : SendPub} (hP : An.P = K1.qAt Zp Np)
    (k : Coins Bk) : ∃ own, (k.look 1 ⟨senderO.place, 0⟩).2.cut ⟨0, 0⟩
      (sendingPart (jobOmega An)).takes = some own :=
  Option.isSome_iff_exists.1 (cut_of_cover k _ _ (omega_takes_cover h hB hP))

/-- hdepth. -/
theorem omega_depth_head {W₂ : Type} (h : P5J.AtMg o Z D r Zp Np cF)
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk) {An : SendPub} (hP : An.P = K1.qAt Zp Np)
    (wit : W₂ → Ask) (k : Coins Bk) (c : W₂) (d : List Fmt.Drawn) :
    (sendTable (jobOmega An) wit senderO.place 1 0 k c d).2.logLength = 22 := by
  obtain ⟨x₀, hx₀, Wr⟩ := written_at_head h
  have hO0 : ((VerifiableInference.Desc.Own.treesMade (jobOmega An).Q.codes
      (jobOmega An).Q.sent).getD {}).shapes.toList.map (·.logN) = [22, 13] := by
    have q := shapes_O
    rw [hx₀] at q
    simp only [Option.all_some] at q
    obtain ⟨P, a⟩ := An
    obtain rfl : P = K1.qAt Zp Np := hP
    rw [qAt_written Wr Np]
    exact beq_iff_eq.1 q
  show (sendTable (jobOmega An) wit (sendPlace 5) 1 0 k c d).2.logLength = 22
  rw [sendTable_depth _ _ _ 1 0 k c d (cut_of_cover k _ _ (omega_takes_cover h hB hP))
    (by have e := congrArg List.length hO0; simp only [List.length_map, List.length_cons, List.length_nil] at e; omega), hO0]
  rfl

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.takes_raw
#print axioms ProofFile.Honest.K12.AtFile.takes_plan
#print axioms ProofFile.Honest.K12.AtFile.omega_due_head
#print axioms ProofFile.Honest.K12.AtFile.omega_takes_cover
#print axioms ProofFile.Honest.K12.AtFile.omega_cover_head
#print axioms ProofFile.Honest.K12.AtFile.omega_depth_head
