-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/WPPlanOk.lean: THE TESTS ON THE PLAN PASS AT THE WRITTEN DESCRIPTION `WP`
(Johnson/AtFull/ProofPlan/WP.lean): `WP.planOk = true`. A joining: nothing is evaluated here.

How. Each part was asked of Lean's kernel alone, in a file of its own under
Johnson/AtFull/ProofPlan/At/; two of them (beforeOk, and the clause "inTime" of treeSharingOk) over short
tables, by the laws of Johnson/AtFull/ProofPlan/OneWalk.lean. `FileDescription.bookOk_of_clauses` and
`FileDescription.planOk_of_parts` (Johnson/AtFull/ProofPlan/PlanOkOfParts.lean) lay the answers together.

  `wp_bookOk`, `wp_planOk`: the two joinings. `planWord_at_WP`: `planWord_of_cut`
    (Johnson/AtFull/ProofPlan/WrittenDesc.lean) with its closed premise met.

WHAT IT IS NOT. A fact on written values. At `WP` every block's own test and fileOk are the literal
true: of these it says nothing. That the proof file's description is alike to `WP` is not said:
`planWord_at_WP` keeps as premises: the cut (the tenth of the proof file's entry tests), the
declared rounds, the plans and the depth at the written values, each block's own test, fileOk. No
description is shown to meet them. Each part's negative line stands under
Johnson/AtFull/ProofPlan/At/No/. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.At.FileOk
import Johnson.AtFull.ProofPlan.At.SealLast
import Johnson.AtFull.ProofPlan.At.PlacesOk
import Johnson.AtFull.ProofPlan.At.ReadsOk
import Johnson.AtFull.ProofPlan.At.LabelsOk
import Johnson.AtFull.ProofPlan.At.Depth
import Johnson.AtFull.ProofPlan.At.Decl1
import Johnson.AtFull.ProofPlan.At.Decl2
import Johnson.AtFull.ProofPlan.At.Decl3
import Johnson.AtFull.ProofPlan.At.BlocksFirst
import Johnson.AtFull.ProofPlan.At.BlocksShared
import Johnson.AtFull.ProofPlan.At.BlocksSecond
import Johnson.AtFull.ProofPlan.At.SentFit
import Johnson.AtFull.ProofPlan.At.Book.Sum
import Johnson.AtFull.ProofPlan.At.Book.Rows
import Johnson.AtFull.ProofPlan.At.Book.Told
import Johnson.AtFull.ProofPlan.At.Book.Range
import Johnson.AtFull.ProofPlan.At.Book.Alike
import Johnson.AtFull.ProofPlan.At.Book.OneGroup
import Johnson.AtFull.ProofPlan.At.Book.Once
import Johnson.AtFull.ProofPlan.At.Book.Answered
import Johnson.AtFull.ProofPlan.At.Book.AllTold
import Johnson.AtFull.ProofPlan.At.Book.InTimeL
import Johnson.AtFull.ProofPlan.At.Book.InOrder
import Johnson.AtFull.ProofPlan.At.BeforeOkL
import Johnson.AtFull.ProofPlan.PlanOkOfParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc
open VerifiableInference.PlanWritten (cutIs)

theorem wp_bookOk : WP.treeSharingOk = true :=
  FileDescription.bookOk_of_clauses WP wp_book_sum wp_book_rows wp_book_told wp_book_range wp_book_alike
    wp_book_oneGroup wp_book_once wp_book_answered wp_book_allTold wp_book_inTimeL wp_book_inOrder

/-- **The tests on the plan pass at the written description.** -/
theorem wp_planOk : WP.planOk = true :=
  FileDescription.planOk_of_parts WP wp_fileOk wp_blocks₁ wp_blocks₂ wp_blocks₃ wp_decl₁ wp_decl₂ wp_decl₃
    wp_depth wp_labelsOk wp_placesOk wp_beforeOkL wp_bookOk wp_readsOk wp_sentFit wp_sealLast

/-- **The refusal's words on the plan are none**, at a description with the written cut, rounds,
plans and depth, whose blocks pass their own tests and whose fileOk passes. -/
theorem planWord_at_WP {Xi : Type} {F : FileDescription Xi} (hC : cutIs F = true)
    (hD : F.roundsDeclaredByBlocks = declProofFull) (hP : F.plans = declProofFull) (hd : F.tableDepth = 32)
    (b₁ : ∀ b ∈ F.first.blocksInOrder, b.planOk = true) (b₂ : ∀ b ∈ F.shared.blocksInOrder, b.planOk = true)
    (b₃ : ∀ b ∈ F.second.blocksInOrder, b.planOk = true) (hF : F.fileOk = true) : F.planWord = none :=
  planWord_of_cut wp_planOk hC hD hP hd b₁ b₂ b₃ hF

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.wp_bookOk
#print axioms P2Law.ProofPlan.wp_planOk
#print axioms P2Law.ProofPlan.planWord_at_WP
