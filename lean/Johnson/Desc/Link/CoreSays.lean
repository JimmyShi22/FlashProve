-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Link/CoreSays.lean: what a yes of the tests on the plan of a one-chain description
holds, CLAUSE BY NAME: so that no proof counts «.1»s into FileDescription.planOkCore's conjunction (such
proofs break when the
clauses move). Each lemma finds its clause by `tauto`, wherever it stands.
-/
import Johnson.Desc.Link.OneChainFileDescription
import Mathlib.Tactic.Tauto

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
variable {Xi : Type}

theorem OneChainFileDescription.planOk_fileOk (F : OneChainFileDescription Xi) (h : F.planOk = true) : F.asFile.fileOk = true := by
  unfold OneChainFileDescription.planOk FileDescription.planOkCore at h
  simp only [Bool.and_eq_true] at h
  tauto

theorem OneChainFileDescription.planOk_blocks (F : OneChainFileDescription Xi) (h : F.planOk = true) : blocksOk F.asFile.first.blocksInOrder
    = true := by
  unfold OneChainFileDescription.planOk FileDescription.planOkCore at h
  simp only [Bool.and_eq_true] at h
  tauto

theorem OneChainFileDescription.planOk_decl (F : OneChainFileDescription Xi) (h : F.planOk = true) :
    (F.asFile.roundsDeclaredByBlocks.1 == F.asFile.plans.1) = true := by
  unfold OneChainFileDescription.planOk FileDescription.planOkCore at h
  simp only [Bool.and_eq_true] at h
  tauto

theorem OneChainFileDescription.planWord_none (F : OneChainFileDescription Xi) (h : F.planWord = none) : F.planOk = true := by
  unfold OneChainFileDescription.planWord at h
  split at h
  · assumption
  · cases h

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.OneChainFileDescription.planOk_fileOk
#print axioms VerifiableInference.Desc.OneChainFileDescription.planOk_blocks
#print axioms VerifiableInference.Desc.OneChainFileDescription.planOk_decl
#print axioms VerifiableInference.Desc.OneChainFileDescription.planWord_none
