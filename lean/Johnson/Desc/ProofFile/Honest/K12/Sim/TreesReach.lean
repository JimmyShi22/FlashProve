-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/TreesReach.lean: which places of a proximity test the law at
several first trees (Sim/TreesLaw.lean) can reach at all: its premises on public numbers as one test
with code on the place, with its law; and that test at the library's closed places. Public numbers
alone: no input, no random value, no challenge's value. No property is claimed.

  `reachTL`, `reachTB`, `reachTNo`   the clauses of `reachL` (Sim/Reach.lean) without "the first
                 reading round opens one tree" and "of the first stage's depth"
  `reach_gives_trees`   "true" gives the law's premises on the stages, on h ≤ k and on the sizes, at
                 every family of challenges that samples the declared counts
  `reachTB_of_reachB`   where `reachB` says "true", so does this one
  `reachT_U_full` ... `reachT_KW_full`   "true" at the tests on the folded row's group and at the
                 request's own test: the proof file's at both sizes, the key file's at the full size
  `reachT_O_full`, `reachT_O_small`, `reachT_KO_full`   at Omega's test just one clause fails: the
                 first fold sends its own table

By what. The proofs are those of Sim/Reach.lean; the nine closed facts are the kernel's own
evaluation.

Limits. Those of Sim/Reach.lean and Sim/ReachAt.lean: a "true" counts nothing by itself: the law's
other premises are not touched; no converse is proved for a "false". The places are closed terms
that a program made off the print of a run: that they are the places of a file is no theorem. The
clause on the sizes still holds the first reading round's count against the first stage's two tails,
which the law at several trees may not need. Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ReachAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open H2K.Pub (sgOf)
open H2K.Member
open OnBytes.LinkSim.AtText (FitsBody)

/-- **The clauses, each under its name**: those of `reachL` (Sim/Reach.lean) but for its two on the
first opening. -/
def reachTL (p : P12) : List (String × Bool) :=
  match p.nums.stages with
  | a :: next :: nx' :: rest' =>
    [("the first fold sends no table of its own", !p.nums.ownMask),
     ("h ≤ k behind the first stage", (next :: nx' :: rest').all fun st => decide (st.h ≤ st.k)),
     ("the sizes at the declared counts", sizesB (declared p) (next :: nx' :: rest') a 1)]
  | _ => [("three stages or more", false)]

/-- All hold. -/
def reachTB (p : P12) : Bool := (reachTL p).all (·.2)

/-- The names of those that do not. -/
def reachTNo (p : P12) : List String := ((reachTL p).filter (!·.2)).map (·.1)

/-- **What the test's "true" gives.** -/
theorem reach_gives_trees (p : P12) (h : reachTB p = true) :
    ∃ a next nx' rest', p.nums.stages = a :: next :: nx' :: rest' ∧ p.nums.ownMask = false ∧
      (∀ st ∈ next :: nx' :: rest', st.h ≤ st.k) ∧
      ∀ D : ℕ → Fmt.Drawn, (∀ i, (D i).poss.length = declared p i) →
        FitsBody D (next :: nx' :: rest') a 1 := by
  unfold reachTB reachTL at h
  split at h
  · rename_i a next nx' rest' hst
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_true_eq] at h
    obtain ⟨c1, ⟨c2a, c2b, c2c⟩, c5⟩ := h
    refine ⟨a, next, nx', rest', hst, c1, ?_, fun D hD =>
      fits_of_sizesB D (declared p) hD _ _ _ c5⟩
    intro st hs
    rcases List.mem_cons.1 hs with rfl | hs
    · exact c2a
    rcases List.mem_cons.1 hs with rfl | hs
    · exact c2b
    exact of_decide_eq_true (List.all_eq_true.1 c2c st hs)
  · simp at h

/-- Where the elder test says "true", so does this one. -/
theorem reachTB_of_reachB (p : P12) (h : reachB p = true) : reachTB p = true := by
  unfold reachB reachL at h
  unfold reachTB reachTL
  split at h
  · rename_i a next nx' rest' hst
    rw [hst]
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, h.2.1, h.2.2.2.2⟩
  · simp at h

/-! ## At the library's closed places -/

theorem reachT_U_full : reachTB piUFull = true := by decide +kernel
theorem reachT_W_full : reachTB piWFull = true := by decide +kernel
theorem reachT_U_small : reachTB piU = true := by decide +kernel
theorem reachT_W_small : reachTB piW = true := by decide +kernel
theorem reachT_KU_full : reachTB piKUFull = true := by decide +kernel
theorem reachT_KW_full : reachTB piKWFull = true := by decide +kernel

theorem reachT_O_full : reachTNo piOFull = ["the first fold sends no table of its own"] := by
  decide +kernel
theorem reachT_O_small : reachTNo piO = ["the first fold sends no table of its own"] := by
  decide +kernel
theorem reachT_KO_full : reachTNo piKOFull = ["the first fold sends no table of its own"] := by
  decide +kernel

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.reachTL
#print axioms ProofFile.Honest.K12.reachTB
#print axioms ProofFile.Honest.K12.reachTNo
#print axioms ProofFile.Honest.K12.reach_gives_trees
#print axioms ProofFile.Honest.K12.reachTB_of_reachB
#print axioms ProofFile.Honest.K12.reachT_U_full
#print axioms ProofFile.Honest.K12.reachT_W_full
#print axioms ProofFile.Honest.K12.reachT_U_small
#print axioms ProofFile.Honest.K12.reachT_W_small
#print axioms ProofFile.Honest.K12.reachT_KU_full
#print axioms ProofFile.Honest.K12.reachT_KW_full
#print axioms ProofFile.Honest.K12.reachT_O_full
#print axioms ProofFile.Honest.K12.reachT_O_small
#print axioms ProofFile.Honest.K12.reachT_KO_full
