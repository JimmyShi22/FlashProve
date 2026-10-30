-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/ProofPlan/PlanOkOfParts.lean: THE TESTS ON THE PLAN OF A FILE's DESCRIPTION, PUT
TOGETHER OUT OF THEIR PARTS: `FileDescription.planOk` (Johnson/Desc/Block.lean) from its conjuncts, and
`BookPlan.allClausesHold` (Johnson/Desc/BookPlan.lean) from its clauses, each part a premise of its own in the
words of its definition. General in the description. Statements and proofs.

Why. At a large written description each part is asked of Lean's kernel alone, in a file of its own.
These two theorems lay the answers together.

  `FileDescription.planOk_of_parts`: the conjuncts of `planOkCore`, in their order, and `sealLast`.
  `BookPlan.ok_of_clauses`, `FileDescription.bookOk_of_clauses`: the clauses of `BookPlan.clauses`, in
    their order.
  `FileDescription.planOk_parts`: the other way: what a yes of `planOk` says of the first and the last
    part: so a part that fails makes the whole fail.

Limits. Bookkeeping. No description is named. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-- **The tests on the plan, out of their parts.** -/
theorem FileDescription.planOk_of_parts {Xi : Type} (F : FileDescription Xi)
    (hFileOk : F.fileOk = true) (hFirst : blocksOk F.first.blocksInOrder = true)
    (hShared : blocksOk F.shared.blocksInOrder = true) (hSecond : blocksOk F.second.blocksInOrder = true)
    (hDecl₁ : (F.roundsDeclaredByBlocks.1 == F.plans.1) = true) (hDecl₂ : (F.roundsDeclaredByBlocks.2.1 == F.plans.2.1) = true)
    (hDecl₃ : (F.roundsDeclaredByBlocks.2.2 == F.plans.2.2) = true)
    (hDepth : ((F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2).all
      (fun r => r.stored.all (·.sh.a == F.tableDepth))) = true)
    (hLabels : F.labelsOk = true) (hPlaces : F.placesOk = true) (hBefore : F.beforeOk = true)
    (hBook : F.treeSharingOk = true) (hReads : F.readsOk = true) (hSent : F.sentFit = true)
    (hSeal : F.sealLast = true) : F.planOk = true := by
  unfold FileDescription.planOk FileDescription.planOkCore
  simp only [hFileOk, hFirst, hShared, hSecond, hDecl₁, hDecl₂, hDecl₃, hDepth,
    hLabels, hPlaces, hBefore, hBook, hReads, hSent, hSeal, Bool.and_self]

/-- **The tests for the trees' tenants and openings, out of their clauses.** -/
theorem BookPlan.ok_of_clauses (D : BookPlan.DeclaredRoundsByChain) (T : BookPlan.SentOraclesByChain)
    (hSum : BookPlan.sum T = true) (hRows : BookPlan.rows T = true)
    (hTold : BookPlan.everyOpenedTreeIsListed D T = true) (hRange : BookPlan.range D = true)
    (hAlike : BookPlan.alike D T = true) (hOneGroup : BookPlan.oneGroup D T = true)
    (hOnce : BookPlan.once D T = true) (hAnswered : BookPlan.answered D T = true)
    (hAllTold : BookPlan.sentOraclesMatchEntries D T = true) (hInTime : BookPlan.inTime D T = true)
    (hInOrder : BookPlan.inOrder D = true) :
    BookPlan.allClausesHold D T = true := by
  unfold BookPlan.allClausesHold BookPlan.clauses
  simp only [List.all_cons, List.all_nil, hSum, hRows, hTold, hRange, hAlike,
    hOneGroup, hOnce, hAnswered, hAllTold, hInTime, hInOrder, Bool.and_self]

/-- The like at a description. -/
theorem FileDescription.bookOk_of_clauses {Xi : Type} (F : FileDescription Xi)
    (hSum : BookPlan.sum F.roots = true) (hRows : BookPlan.rows F.roots = true)
    (hTold : BookPlan.everyOpenedTreeIsListed F.roundsDeclaredByBlocks F.roots = true) (hRange : BookPlan.range F.roundsDeclaredByBlocks = true)
    (hAlike : BookPlan.alike F.roundsDeclaredByBlocks F.roots = true)
    (hOneGroup : BookPlan.oneGroup F.roundsDeclaredByBlocks F.roots = true)
    (hOnce : BookPlan.once F.roundsDeclaredByBlocks F.roots = true)
    (hAnswered : BookPlan.answered F.roundsDeclaredByBlocks F.roots = true)
    (hAllTold : BookPlan.sentOraclesMatchEntries F.roundsDeclaredByBlocks F.roots = true)
    (hInTime : BookPlan.inTime F.roundsDeclaredByBlocks F.roots = true) (hInOrder : BookPlan.inOrder F.roundsDeclaredByBlocks = true) :
    F.treeSharingOk = true :=
  BookPlan.ok_of_clauses F.roundsDeclaredByBlocks F.roots hSum hRows hTold hRange hAlike hOneGroup
    hOnce hAnswered hAllTold hInTime hInOrder

/-- A yes of the whole says yes at the first part and at the last. -/
theorem FileDescription.planOk_parts {Xi : Type} (F : FileDescription Xi) (h : F.planOk = true) :
    F.fileOk = true ∧ F.sealLast = true := by
  unfold FileDescription.planOk FileDescription.planOkCore at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1.1.1.1.1, h.2⟩

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.FileDescription.planOk_of_parts
#print axioms VerifiableInference.Desc.BookPlan.ok_of_clauses
#print axioms VerifiableInference.Desc.FileDescription.bookOk_of_clauses
#print axioms VerifiableInference.Desc.FileDescription.planOk_parts
