-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/CalledAtRun.lean

What it proves. At a run of the frame's walking prover (runC, ProofFile/Honest/Walk.lean), at the
stand in front of a called part of the shared chain: the stand that midSharedAtW returns is there;
its input is what ready lays; it has seen the shared view's first rounds: those of the blocks in
front of the part's block, and the i rounds of that block in front of the part; and the
description's own fold over the blocks in front, from the description's own start at the instance,
has returned with nothing left over, at the rounds seen of these blocks and at columns which are the
shared view's first ones and which fillCols has laid for these blocks' reads at the prover's own
stored columns.
General in the description, the book, the prover and the part.

Names.
  called_at_run   the theorem.

By what. called_fold (CalledFold.lean). Of the frame's laws (ProofFile/Honest/Law/): mid_shared,
told_behind (RunMidFile.lean); StandsAt, stretch_back (OwedParts.lean); runC_parts
(Rule/WalkLaw.lean); ready_ok (Run.lean); steps_shaped (Along.lean); walk_mid (WalkMid.lean);
runC_laidAs, at_shared, steps_chain, places_chain, off_chain (RunAtFile.lean); laidAs_mask,
all_of_map (RunAt.lean); envOf_tree (Cut.lean); exBind_ok, exMap_ok (Play.lean); and the library's
FileDescription.planOk_ok (Johnson/Desc/RunLaws.lean).

Limits.
- It is of the walk (runC). midSharedAtW (ProofFile/Honest/MidW.lean) is made of ready, of the start
  as runC lays it and of walk over the Steps in front of the part: m is the state that this walk
  holds. Of midSharedAt, which is made of play, nothing is said.
- Nothing on whether ready or runC returns, or whether the part is called.
- That runC's own walk goes through that state is not said here. Of m's field opened nothing is
  said.
- Steps of the frame's and of the verifier's: no property of a prover or a protocol. Nothing on
  completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.CalledFold
import Johnson.Desc.ProofFile.Honest.Law.OwedParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block OpenedColumn FileDescription foldBlocks)
open ProofFile.Honest

/-- **At a run of the frame's walking prover (runC), at the stand in front of a called part of the
shared chain**: the stand is there; its input is what ready lays; it has seen the shared view's
first rounds, as many as the blocks in front declare and i more; and the description's own fold over
the blocks in front, from the description's own start at the instance, has returned with nothing
left over at the rounds seen of these blocks and at columns which are the shared view's first ones
and which fillCols has laid for these blocks' reads at the prover's own stored columns. General in
the description, the book, the prover and the part (i: how many rounds of its block come before
it).
Public: hpl. On the filling and the book: hR, S. On the run: hrun, hc.
It is of the walk (runC); m is the state that midSharedAtW returns in front of the part: that runC's
own walk goes through it is not said. Nothing on whether runC returns or calls the part. -/
theorem called_at_run {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R)
    (σ : Side F.S₂ F.Cl V (Common W₀ Rc Ky) X₀ Pb) (u : Member V (Common W₀ Rc Ky) X₀ Pb)
    (pre t : List (Block F.S₂ F.Cl)) (i : ℕ) (S : StandsAt F.shared.blocksInOrder R.shared σ u pre t i)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ (m : Mid (Common W₀ Rc Ky) X₀) (s : F.S₂) (cols more : List OpenedColumn) (rest : List Fmt.RoundView),
      midSharedAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      m.st.input = ⟨w₀, rc, P.key x⟩ ∧
      r.run.views.2.1.rounds = m.seen ++ rest ∧
      m.seen.length = (pre.flatMap (·.rounds)).length + i ∧
      r.run.views.2.1.opened = cols ++ more ∧
      foldBlocks 0 pre (F.start₂ (F.pub x)) (m.seen.take (pre.flatMap (·.rounds)).length) cols =
        .ok (s, [], []) ∧
      fillCols (readsOf 1 0 (P.storedWords w₀ rc)
        (treeOwn (r.run.played.2.1.take (pre.flatMap (·.rounds)).length))
        (pre.flatMap (·.rounds))
        ((m.seen.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cols := by
  have Q := (F.planOk_ok).1 hpl
  have hp := Q.places
  obtain ⟨-, tr, -, -, hcom, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨ha, hN, -, hseg⟩ := stretch_back S.str S.pos S.fits
  obtain ⟨m, hm, hseen⟩ := mid_shared hrun hR o₁ o₂ o₃ hp ha hseg hc
  rw [hN] at hseen
  -- a real round behind the rounds in front of the part
  obtain ⟨l1, l2, l3⟩ := runC_laidAs hrun hR o₁ o₂ o₃
  obtain ⟨p1, p2, p3⟩ := places_chain hp
  have c1 := steps_chain s1 p1
  have c2 := steps_chain s2 p2
  have c3 := steps_chain s3 p3
  have hA := at_shared hrun hR o₁ o₂ o₃ hp ha
  have hb := told_behind hA S.str hc (fun p hp' hat => by
    rcases List.mem_append.1 hp' with g | g
    · rcases List.mem_append.1 g with g | g
      · rw [all_of_map (laidAs_mask l1 _) (off_chain (by decide) c2 c1 ha) p g] at hat
        cases hat
      · exact g
    · rw [all_of_map (laidAs_mask l3 _) (off_chain (by decide) c2 c3 ha) p g] at hat
      cases hat)
  -- the input
  have hin : m.st.input = ⟨w₀, rc, P.key x⟩ := by
    have h0 := hm
    unfold midSharedAtW at h0
    obtain ⟨R', hR', h0⟩ := exBind_ok h0
    rw [hR] at hR'
    cases hR'
    obtain ⟨a₂, ha₂, h1⟩ := exBind_ok h0
    unfold midInW at h1
    split at h1
    · cases h1
    · obtain ⟨y, hy, e⟩ := exMap_ok h1
      rw [(walk_mid ha₂ hy e).1]
      exact hcom
  -- the shared chain's walk
  obtain ⟨R', a₁, z₁, a₂, z₂, a₃, z₃, hR', -, -, -, ha₂, hz₂, -, -, rfl⟩ := runC_parts hrun
  rw [hR] at hR'
  cases hR'
  have hLo : ∀ ps, treeOwn ps = (envOf (P.storedWords w₀ rc) (fun _ _ => none) ps).tree :=
    fun ps => ((envOf_tree (P.storedWords w₀ rc) ps [] []).1).symm
  have hpos : 0 < σ.block.rounds.length := by
    have := S.le
    have := S.pos
    omega
  have ht : ∃ p ∈ z₂.laid.drop (pre.flatMap (·.rounds)).length, p.told = true := by
    obtain ⟨p, hp', e⟩ := hb
    have hp'' : p ∈ (z₂.laid.drop (pre.flatMap (·.rounds)).length).drop i := by
      rw [List.drop_drop]
      exact hp'
    exact ⟨p, List.mem_of_mem_drop hp'', e⟩
  rw [S.cut] at ha₂
  obtain ⟨s, cols, more, hfold, hfill, hcols⟩ := called_fold ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩
    hLo pre σ.block t hpos (R.start₂ P) (F.start₂ (F.pub x)) ha₂ hz₂ ht
  have hseen' : m.seen = roundsOf (z₂.laid.take ((pre.flatMap (·.rounds)).length + i)) := hseen
  have htake : m.seen.take (pre.flatMap (·.rounds)).length =
      roundsOf (z₂.laid.take (pre.flatMap (·.rounds)).length) := by
    rw [hseen']
    unfold roundsOf
    rw [← List.map_take, List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)]
  have hlenZ : (pre.flatMap (·.rounds)).length + i ≤ z₂.laid.length := by
    have e := congrArg List.length (laidAs_mask l2 ⟨σ.block.place, u.number⟩)
    rw [List.length_map, List.length_map] at e
    have e' : z₂.laid.length = R.shared.length := e
    have := S.fits
    omega
  refine ⟨m, s, cols, more,
    roundsOf (z₂.laid.drop ((pre.flatMap (·.rounds)).length + i)), hm, hin, ?_, ?_, hcols, ?_, ?_⟩
  · show roundsOf z₂.laid = _
    rw [hseen', ← roundsOf_append, List.take_append_drop]
  · rw [hseen', roundsOf_length, List.length_take, Nat.min_eq_left hlenZ]
  · rw [htake]
    exact hfold
  · rw [htake]
    have ed : (roundsOf (z₂.laid.take (pre.flatMap (·.rounds)).length)).map (·.drawn) =
        (z₂.laid.take (pre.flatMap (·.rounds)).length).map (·.drawn) := by
      unfold roundsOf
      rw [List.map_map]
      rfl
    rw [ed]
    exact hfill

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.called_at_run
