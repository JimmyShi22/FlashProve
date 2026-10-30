-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the state on entry at a stand of a run.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/DoorStand.lean:
one function on both sides. At the front of a called part of the first chain of a run of the
frame's walking prover, cut back to the rounds in front of the test, stateFromView (DoorTrue.lean) is what
the way in makes of the state that the description's own fold reaches at the run's own columns.

  stateFromView_at_stand   the equation

Its premises hfold, hfill are what called_at_first, door_by_at_first and door_moves_at_L conclude.
Of the walk (runC). No law, no coin. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.DoorTrue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block OpenedColumn FileDescription foldBlocks Place)
open VerifiableInference.Desc.K12 (T12)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light

/-- **One function on both sides.** N: the rounds in front of the test. i: the rounds of the test in
front of the member. -/
theorem stateFromView_at_stand {Xi W₀ Rc Ky Tr X₀ Y V Pb Pq : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₁ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₁ F.Cl)) (i : ℕ)
    (S : StandsAt F.first.blocksInOrder R.first σ u pre t i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (m : Mid (Local W₀ Rc Xi Tr) Y)
    (hm : midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m))
    (s₀ s : F.S₁) (cs : List OpenedColumn)
    (hfold : foldBlocks 0 pre s₀ (m.seen.take (pre.flatMap (·.rounds)).length) cs = .ok (s, [], []))
    (hfill : fillCols (readsOf 0 0 (P.storedWords w₀ rc)
      (treeOwn (r.run.played.1.take (pre.flatMap (·.rounds)).length)) (pre.flatMap (·.rounds))
      ((m.seen.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cs)
    (start : Pq → F.S₁) (enter : F.S₁ → Except String T12) (fall : T12) (pb : Pq)
    (hstart : start pb = s₀) :
    stateFromView pre start enter fall pb
      ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
        ⟨σ.block.place, u.number⟩).cut i) = (enter s).toOption.getD fall := by
  obtain ⟨m', hm', -, -, -, hseen, hbf, -, -, -, hst⟩ :=
    frame_at_first hpl hR hrun σ u pre t i _ S rfl hc
      (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
  have hmm : m' = m := by
    rw [hm] at hm'
    exact (Option.some.inj (Except.ok.inj hm')).symm
  subst hmm
  obtain ⟨a₁, y, -, ha, hw, hl, -, -⟩ := played_at_first hpl hR hrun σ u pre t i _ S rfl hc
  have h0 := start_laid ha
  have hdr : (roundsOf (r.run.played.1.take ((pre.flatMap (·.rounds)).length + i))).map (·.drawn) =
      ρ.first.take ((pre.flatMap (·.rounds)).length + i) := by
    have g := walk_laid_drawn _ _ _ _ _ hw
    rw [hl, h0] at g
    simpa [roundsOf] using g
  have hfits := S.fits
  have hn : (r.run.played.1.take ((pre.flatMap (·.rounds)).length + i)).length =
      (pre.flatMap (·.rounds)).length + i := by
    have g := walk_laid_length _ _ _ _ _ hw
    rw [hl, h0, List.length_nil, Nat.zero_add] at g
    rw [g, List.length_take]
    omega
  have hsl : (shownBy 0 (treeAsks F ρ 0)
      (r.run.played.1.take ((pre.flatMap (·.rounds)).length + i)) 0).length =
      (pre.flatMap (·.rounds)).length + i := by
    rw [shownBy_length, hn]
  have hf : (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
      ⟨σ.block.place, u.number⟩).cut i =
      ⟨shownBy 0 (treeAsks F ρ 0) (r.run.played.1.take (pre.flatMap (·.rounds)).length) 0,
        storedShown (P.storedWords w₀ rc) (storedAsks F ρ)⟩ := by
    rw [hbf, hst]
    show (⟨shownBy 0 (treeAsks F ρ 0)
      (r.run.played.1.take ((pre.flatMap (·.rounds)).length + i)) 0,
      storedShown (P.storedWords w₀ rc) (storedAsks F ρ)⟩ : Before).cut i = _
    unfold Before.cut
    simp only [hsl, Nat.add_sub_cancel]
    rw [← shownBy_take, List.take_take]
    simp
  have hseenF : ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
      ⟨σ.block.place, u.number⟩).cut i).seen =
      m'.seen.take (pre.flatMap (·.rounds)).length := by
    rw [hf, seen_by, roundsOff_by, hseen]
    unfold roundsOf
    rw [← List.map_take, List.take_take]
    simp
  have hdraw : (m'.seen.take (pre.flatMap (·.rounds)).length).map (·.drawn) =
      ρ.first.take (pre.flatMap (·.rounds)).length := by
    rw [hseen, List.map_take, hdr, List.take_take]
    simp
  have hdecl : pre.flatMap (·.rounds) = F.roundsDeclaredByBlocks.1.take (pre.flatMap (·.rounds)).length := by
    show _ = (F.first.blocksInOrder.flatMap (·.rounds)).take _
    rw [S.cut, List.flatMap_append]
    simp
  have hv := columnsOfView_at (F := F) (ρ := ρ) (stored := P.storedWords w₀ rc)
    (r.run.played.1.take (pre.flatMap (·.rounds)).length) (pre.flatMap (·.rounds)).length
    (pre.flatMap (·.rounds)) hdecl _ hdraw cs hfill _ hf (by rw [hseenF])
  unfold stateFromView doorFromView
  rw [hv, hseenF, hstart]
  dsimp only
  rw [hfold]
  rfl

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.stateFromView_at_stand
