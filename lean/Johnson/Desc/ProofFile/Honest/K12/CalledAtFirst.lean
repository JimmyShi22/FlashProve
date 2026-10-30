-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/CalledAtFirst.lean

What it proves. called_at_run (CalledAtRun.lean) at the first chain: at a called part of the first
chain, at a run of the frame's walking prover (runC): the stand that midAtW returns; its input; that
the first view's rounds and columns begin with what the stand has seen and with the columns cols;
that the description's own fold over the blocks in front of the part's block returns at these; and
that cols is the filling of what these blocks' declared rounds read. General in the description, the
book, the prover, the side, the member and the blocks in front: no block in front is named.

Names.
  called_at_first   the theorem.

By what. called_fold (CalledFold.lean), which is general in the chain. Of the frame's laws
(ProofFile/Honest/Law/): mid_first, told_behind (RunMidFile.lean); at_first, runC_laidAs
(RunAtFile.lean); runC_parts (Rule/WalkLaw.lean); stretch_back (OwedParts.lean); ready_ok
(Run.lean); steps_shaped (Along.lean); walk_mid (WalkMid.lean).

Limits.
- Its proof is a second text of called_at_run's, with the first chain's names; one step is new: the
  first view lacks the chain's last round (the seal's), by the frame's own text.
- A conditional: nothing on whether ready or runC returns, or whether the part is called, at any
  prover and book.
- Of the walk (runC), not of play (run): midAtW (ProofFile/Honest/MidW.lean) is made of ready, of
  the start as runC lays it and of walk over the Steps in front of the part: the stand is the state
  that this walk holds. Of midAt, which is made of play, nothing is said.
- Nothing of it is the kind K12's: steps of the frame's. It says nothing of what a part sends.
- The stand is the state that midAtW (Honest/MidW.lean) returns. That runC's own walk goes through
  that state is not said here.
- It moves no count. Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.CalledAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block OpenedColumn FileDescription foldBlocks)
open ProofFile.Honest

/-- **At a called part of the first chain, at a run of the frame's walking prover**: called_at_run
(CalledAtRun.lean) at the first chain. General in the description, the book, the prover, the side,
the member and the blocks in front. Where ready and runC return and the part is called: midAtW
returns a stand m; its input is the first chain's own (index, randomness, instance, the prover's
trace); the first view's rounds begin with what m has seen; m has seen the rounds of the blocks in
front and i more; the first view's columns begin with cols; the description's own fold over the
blocks in front, from the first chain's start, at the rounds that m has seen of them and at cols,
returns, with no round and no column left; and cols is the filling of what these blocks' declared
rounds read at what was drawn (the frame's readsOf at the chain's number 0).
Public: hpl. On the filling and the book: hR, S. On the run: hrun, hc.
The first view lacks the chain's last round (the seal's): the frame's own text. Of the walk (runC),
not of play (run); nothing on whether ready or runC returns or the part is called. -/
theorem called_at_first {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R)
    (σ : Side F.S₁ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₁ F.Cl)) (i : ℕ) (S : StandsAt F.first.blocksInOrder R.first σ u pre t i)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ (m : Mid (Local W₀ Rc Xi Tr) Y) (s : F.S₁) (cols more : List OpenedColumn) (rest : List Fmt.RoundView)
      (tr : Tr),
      midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      P.trace w₀ x = some tr ∧ m.st.input = ⟨w₀, rc, x, tr⟩ ∧
      r.run.views.1.rounds = m.seen ++ rest ∧
      m.seen.length = (pre.flatMap (·.rounds)).length + i ∧
      r.run.views.1.opened = cols ++ more ∧
      foldBlocks 0 pre (F.start₁ (F.pub x)) (m.seen.take (pre.flatMap (·.rounds)).length) cols =
        .ok (s, [], []) ∧
      fillCols (readsOf 0 0 (P.storedWords w₀ rc)
        (treeOwn (r.run.played.1.take (pre.flatMap (·.rounds)).length))
        (pre.flatMap (·.rounds))
        ((m.seen.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cols := by
  have Q := (F.planOk_ok).1 hpl
  have hp := Q.places
  obtain ⟨-, tr, htr, hown, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨ha, hN, -, hseg⟩ := stretch_back S.str S.pos S.fits
  obtain ⟨m, hm, hseen⟩ := mid_first hrun hR o₁ o₂ o₃ hp ha hseg hc
  rw [hN] at hseen
  -- a real round behind the rounds in front of the part
  obtain ⟨l1, l2, l3⟩ := runC_laidAs hrun hR o₁ o₂ o₃
  obtain ⟨p1, p2, p3⟩ := places_chain hp
  have c1 := steps_chain s1 p1
  have c2 := steps_chain s2 p2
  have c3 := steps_chain s3 p3
  have hA := at_first hrun hR o₁ o₂ o₃ hp ha
  have hb := told_behind hA S.str hc (fun p hp' hat => by
    rcases List.mem_append.1 hp' with g | g
    · rcases List.mem_append.1 g with g | g
      · exact g
      · rw [all_of_map (laidAs_mask l2 _) (off_chain (by decide) c1 c2 ha) p g] at hat
        cases hat
    · rw [all_of_map (laidAs_mask l3 _) (off_chain (by decide) c1 c3 ha) p g] at hat
      cases hat)
  -- the input
  have hin : m.st.input = ⟨w₀, rc, x, tr⟩ := by
    have h0 := hm
    unfold midAtW at h0
    obtain ⟨R', hR', h0⟩ := exBind_ok h0
    rw [hR] at hR'
    cases hR'
    obtain ⟨a₁, ha₁, h1⟩ := exBind_ok h0
    split at h1
    · unfold midInW at h1
      split at h1
      · cases h1
      · obtain ⟨y, hy, e⟩ := exMap_ok h1
        rw [(walk_mid ha₁ hy e).1]
        exact hown
    · rename_i hno
      exact absurd ha hno
  -- the first chain's walk
  obtain ⟨R', a₁, z₁, a₂, z₂, a₃, z₃, hR', ha₁, hz₁, -, -, -, -, -, rfl⟩ := runC_parts hrun
  rw [hR] at hR'
  cases hR'
  have hLo : ∀ ps, treeOwn ps = (envOf (P.storedWords w₀ rc) (fun _ _ => none) ps).tree :=
    fun ps => ((envOf_tree (P.storedWords w₀ rc) ps [] []).1).symm
  have hpos : 0 < σ.block.rounds.length := by
    have := S.le
    have := S.pos
    omega
  have ht : ∃ p ∈ z₁.laid.drop (pre.flatMap (·.rounds)).length, p.told = true := by
    obtain ⟨p, hp', e⟩ := hb
    have hp'' : p ∈ (z₁.laid.drop (pre.flatMap (·.rounds)).length).drop i := by
      rw [List.drop_drop]
      exact hp'
    exact ⟨p, List.mem_of_mem_drop hp'', e⟩
  rw [S.cut] at ha₁
  obtain ⟨s, cols, more, hfold, hfill, hcols⟩ := called_fold ⟨0, 0, P.storedWords w₀ rc, treeOwn⟩
    hLo pre σ.block t hpos (R.start₁ P) (F.start₁ (F.pub x)) ha₁ hz₁ ht
  have hseen' : m.seen = roundsOf (z₁.laid.take ((pre.flatMap (·.rounds)).length + i)) := hseen
  have htake : m.seen.take (pre.flatMap (·.rounds)).length =
      roundsOf (z₁.laid.take (pre.flatMap (·.rounds)).length) := by
    rw [hseen']
    unfold roundsOf
    rw [← List.map_take, List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)]
  have hlenZ : (pre.flatMap (·.rounds)).length + i + 1 ≤ z₁.laid.length := by
    have e := congrArg List.length (laidAs_mask l1 ⟨σ.block.place, u.number⟩)
    rw [List.length_map, List.length_map] at e
    have e' : z₁.laid.length = R.first.length := e
    have := S.fits
    have := S.pos
    omega
  refine ⟨m, s, cols, more,
    (roundsOf (z₁.laid.drop ((pre.flatMap (·.rounds)).length + i))).dropLast, tr, hm, htr, hin, ?_,
    ?_, hcols, ?_, ?_⟩
  · show (roundsOf z₁.laid).dropLast = _
    have hne : roundsOf (z₁.laid.drop ((pre.flatMap (·.rounds)).length + i)) ≠ [] := by
      intro h0
      have h1 := congrArg List.length h0
      rw [roundsOf_length, List.length_drop] at h1
      have h2 : z₁.laid.length - ((pre.flatMap (·.rounds)).length + i) = 0 := h1
      omega
    rw [hseen', ← List.dropLast_append_of_ne_nil hne, ← roundsOf_append, List.take_append_drop]
  · rw [hseen', roundsOf_length, List.length_take, Nat.min_eq_left (by omega)]
  · rw [htake]
    exact hfold
  · rw [htake]
    have ed : (roundsOf (z₁.laid.take (pre.flatMap (·.rounds)).length)).map (·.drawn) =
        (z₁.laid.take (pre.flatMap (·.rounds)).length).map (·.drawn) := by
      unfold roundsOf
      rw [List.map_map]
      rfl
    rw [ed]
    exact hfill

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.called_at_first
