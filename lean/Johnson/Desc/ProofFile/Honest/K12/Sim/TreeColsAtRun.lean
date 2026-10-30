-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/TreeColsAtRun.lean: what the front of a part of the shared
chain lists of a tree of that chain: the columns of the table of that number among the rounds played
in front of the part, at the positions that the description's declared rounds read of the tree.
General in the description, the side and the member.

  `treeCols_shared`   at the closed form of the front: the twin, at the shared chain's cut, of
                 `treeCols_at` (Johnson/Desc/ProofFile/Honest/Law/Rule/Words.lean), which is stated
                 at the second chain's cut
  `treeCols_at_run`   at one run of `runC`, at a called part: the same of `r.run.beforeAt`

A conditional, the second: nothing here shows that `ready` or `runC` returns at any prover and book.

By what. `cols_at`, `filter_same` (Johnson/Desc/ProofFile/Honest/Law/Rule/Faith.lean);
`frame_at_run` (Sim/FrameAtRun.lean).

Limits.
- Whose table stands at that number among the rounds played, and what its columns are in terms of a
  sender's rows, is not said here.
- `none` in the list of tables stands for a root that no prover's side has sent: then no column is
  listed.
- The shared chain's own trees alone. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.FrameAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (FileDescription Block)

/-- **The columns listed of tree number j of the shared chain, in the cut for that chain.** -/
theorem treeCols_shared {Xi : Type} (F : FileDescription Xi) (ρ : Draws) (p : List Played)
    (st : List (ℕ × ℕ × List UInt64)) (j : ℕ) :
    ((ProofFile.Honest.laidOf F ρ [] p []).front 1 st).treeCols 1 j =
      ((allTabs p)[j]?).map fun T => colsOfT T (treeAsks F ρ 1 j) := by
  show (((shownBy 1 (treeAsks F ρ 1) p 0).filter fun r => r.1 == 1).flatMap
    fun r => r.2.1.cols)[j]? = _
  rw [filter_same]
  have h := cols_at 1 (treeAsks F ρ 1) p 0 j
  rw [Nat.zero_add] at h
  exact h

/-- **The same at one run's own front, at a called part.** hpl: public. hR, S: on the filling and
the book. hrun, hc: on the run. -/
theorem treeCols_at_run {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₂ F.Cl V (Common W₀ Rc Ky) X₀ Pb) (u : Member V (Common W₀ Rc Ky) X₀ Pb)
    (pre t : List (Block F.S₂ F.Cl)) (i n : ℕ)
    (S : StandsAt F.shared.blocksInOrder R.shared σ u pre t i)
    (hn : n = (pre.flatMap (·.rounds)).length + i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (st : List (ℕ × ℕ × List UInt64)) (j : ℕ) :
    (r.run.beforeAt st ⟨σ.block.place, u.number⟩).treeCols 1 j =
      ((allTabs (r.run.played.2.1.take n))[j]?).map fun T => colsOfT T (treeAsks F ρ 1 j) := by
  obtain ⟨m, -, -, -, -, -, hbf, -⟩ := frame_at_run hpl hR hrun σ u pre t i n S hn hc st
  rw [hbf]
  exact treeCols_shared F ρ _ st j

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.treeCols_shared
#print axioms ProofFile.Honest.K12.Light.treeCols_at_run
