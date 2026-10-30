-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/FrameAtSecond.lean

Conditionals: nothing here shows that ready or runC returns at any prover and book.

What it proves. At the last chain ("the second chain" of the format and of the frame; the frame's
number 2), general in the description, the side and the member: what Sim/FrameAtRun.lean proves at
the shared chain: what the frame gives at a called part at one run (the stand's input, what it has
heard and seen, its stops' list, the front in closed form, the run's challenges and positions at the
part); and where a member's rounds stand, from what the prover's list for the last chain holds.

Names.
  frame_at_second      at a called part.
  stands_member_last, stands_rest_last   where any member's, the second member's rounds stand.

By what. played_at_second (Sim/PlayedAtSecond.lean); the frame's walk_mid (Law/WalkMid.lean),
walk_hears, start_hears, start_laid, walk_laid_drawn (WalkHeard.lean), mid_second, before_second,
at_second, drawnAt_of, askedAt_of, runC_asks,
asked_is, steps_stand (Law/Rule/Stands.lean), places_nodup (Law/Cuts.lean); the texts of the frame's
three starts (Honest/Frame.lean).

Limits.
- In this chain a stand has heard all three chains' challenges so far; its stops' list holds the
  first and the last chain's alone; it has seen all rounds of the two earlier chains, the first
  chain's sealing round among them, which the first view lacks; that round's empty challenge is the
  last of the first chain's list, so it stands in what the stand has heard and in its stops' list.
- StandsAt does not say whose part plays, nor what the parts in front have played.
- Of the stand's "own" and of its field opened nothing. carriedAt is neither a premise nor
  concluded.
- Third texts, made by program out of Sim/FrameAtFirst.lean; frame_at_second's proof is new in five
  places.
- The stand is the state that midAtW (Honest/MidW.lean) returns. That runC's own walk goes through
  that state is not said here.
- Of the walk (runC). They move no count. Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.FrameAtFirst
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlayedAtSecond

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (FileDescription Block)

/-- **What the frame gives at a called part of the last chain, at one run**: frame_at_run
(Sim/FrameAtRun.lean) there. n: the rounds of the last chain in front of the member. The stand has
heard all three chains' challenges so far, its stops' list holds the first and the last chain's
alone, and it has seen all rounds of the two earlier chains and then the last chain's in front. -/
theorem frame_at_second {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₃ F.Cl)) (i n : ℕ)
    (S : StandsAt F.second.blocksInOrder R.second σ u pre t i)
    (hn : n = (pre.flatMap (·.rounds)).length + i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (st : List (ℕ × ℕ × List UInt64)) :
    ∃ m, midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      m.st.input = R.own ∧ m.st.heard = ρ.first ++ ρ.shared ++ ρ.second.take n ∧
      m.loc = ρ.first ++ ρ.second.take n ∧
      m.seen = roundsOf r.run.played.1 ++ roundsOf r.run.played.2.1 ++
        roundsOf (r.run.played.2.2.take n) ∧
      r.run.beforeAt st ⟨σ.block.place, u.number⟩ =
        (laidOf F ρ r.run.played.1 r.run.played.2.1 (r.run.played.2.2.take n)).front 2 st ∧
      m.seen = (r.run.beforeAt st ⟨σ.block.place, u.number⟩).seen ∧
      r.run.drawnAt ⟨σ.block.place, u.number⟩ = (ρ.second.drop n).take u.rounds.length ∧
      r.run.askedAt ⟨σ.block.place, u.number⟩ =
        asksFrom (treeAsks F ρ 2) (u.rounds.map (·.2.length))
          (((rowsOfChain F.second.blocksInOrder).take n).map (·.2.length)).sum ∧
      r.run.storedAsked = storedAsks F ρ := by
  have Q := (F.planOk_ok).1 hpl
  have hp := Q.places
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  have hstr := S.str
  have hown := S.own
  have hfit := S.fits
  rw [← hn] at hstr hown hfit
  obtain ⟨ha, htw, -, hseg⟩ := stretch_back hstr S.pos hfit
  have hA := at_second hrun hR o₁ o₂ o₃ hp ha
  have hRO := (runOk_of hrun).1
  obtain ⟨m, hm, hseen⟩ := mid_second hrun hR o₁ o₂ o₃ hp ha hseg hc
  have hbf := before_second hrun hR o₁ o₂ o₃ hp ha hseg (treeAsks F ρ 0) (treeAsks F ρ 1)
    (treeAsks F ρ 2) (shown_is hRO 0 (by decide)) (shown_is hRO 1 (by decide))
    (shown_is hRO 2 (by decide)) st
  rw [htw] at hbf hseen
  have e1 : ((R.second.drop n).take u.rounds.length).map (·.oracles.length) =
      u.rounds.map (·.2.length) := by
    have g := congrArg (List.map (·.2.length)) hown
    rw [List.map_map] at g
    exact g
  have e2 : (R.second.take n).map (·.oracles.length) =
      ((rowsOfChain F.second.blocksInOrder).take n).map (·.2.length) := by
    rw [← steps_pairs s3, ← List.map_take, List.map_map]
    rfl
  have hst : m.st.input = R.own ∧ m.st.heard = ρ.first ++ ρ.shared ++ ρ.second.take n ∧
      m.loc = ρ.first ++ ρ.second.take n := by
    obtain ⟨m₁, m₂, m', a₁, z₁, a₂, z₂, a₃, y, s1', g1, -, e1', s2', g2, -, e2', s3', g3, -, e3',
      hm'⟩ := played_at_second hpl hR hrun σ u pre t i n S hn hc
    obtain rfl : m' = m := Option.some.inj (Except.ok.inj (hm'.symm.trans hm))
    obtain ⟨a1, a2, -⟩ := walk_mid s3' g3 e3'
    obtain ⟨-, b2, -⟩ := walk_mid s1' g1 e1'
    have k1 := walk_laid_drawn _ _ _ a₁ z₁ g1
    rw [start_laid s1', List.map_nil, List.nil_append] at k1
    have k2 := walk_laid_drawn _ _ _ a₂ z₂ g2
    rw [start_laid s2', List.map_nil, List.nil_append] at k2
    have k3 := walk_laid_drawn _ _ _ a₃ y g3
    rw [start_laid s3', List.map_nil, List.nil_append] at k3
    have h1 := walk_hears _ _ _ _ a₁ z₁ (start_hears s1') g1 m₁ e1'
    have h2 := walk_hears _ _ _ _ a₂ z₂ (start_hears s2') g2 m₂ e2'
    have h3 := walk_hears _ _ _ _ a₃ y (start_hears s3') g3 m' e3'
    rw [k1] at h1
    rw [k2] at h2
    rw [k3] at h3
    have h1' : m₁.st.heard = ρ.first := h1.trans (List.nil_append _)
    have h2' : m₂.st.heard = ρ.shared := h2.trans (List.nil_append _)
    have b2' : m₁.loc = ρ.first := b2.trans (List.nil_append _)
    refine ⟨a1, ?_, ?_⟩
    · have h3' : m'.st.heard = (m₁.st.heard ++ m₂.st.heard) ++ ρ.second.take n := h3
      rw [h3', h1', h2']
    · have a2' : m'.loc = m₁.loc ++ ρ.second.take n := a2
      rw [a2', b2']
  refine ⟨m, hm, hst.1, hst.2.1, hst.2.2, hseen, hbf.trans rfl, ?_, drawnAt_of hA hstr, ?_,
    asked_is r.run hRO⟩
  · rw [hbf, hseen, seen_by]
    unfold roundsOff
    rw [List.map_append, List.map_append]
    have f0 := roundsOff_by 0 (treeAsks F ρ 0) r.run.played.1 0
    have f1 := roundsOff_by 1 (treeAsks F ρ 1) r.run.played.2.1 0
    have f2 := roundsOff_by 2 (treeAsks F ρ 2) (r.run.played.2.2.take n) 0
    unfold roundsOff at f0 f1 f2
    rw [f0, f1, f2]
  · rw [askedAt_of hA hstr (treeAsks F ρ 2) (runC_asks hrun hR o₁ o₂ o₃ 2), e1, e2]

/-- **Where a member's rounds stand, from what the prover's list for the last chain holds**:
stands_member (Sim/FrameAtRun.lean) at the last chain. -/
theorem stands_member_last {Xi W₀ Rc Ky Tr X₀ Y Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (σ : Side F.S₃ F.Cl (Local W₀ Rc Xi Tr)
        (Local W₀ Rc Xi Tr) Y Pb)
    (hblk : σ.block ∈ F.second.blocksInOrder) (hfit : σ.fits = true)
    (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Pb) (hu : u ∈ σ.members)
    (hpos : u.part.moves.length ≠ 0) (g : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y)
    (hg : (P.second.find? fun g => g.place == σ.block.place) = some g)
    (hparts : g.parts = σ.row.map (·.1)) :
    ∃ pre t, StandsAt F.second.blocksInOrder R.second σ u pre t
      ((σ.row.take u.number).map (·.1.moves.length)).sum := by
  obtain ⟨-, tr, -, -, -, -, -, s3⟩ := ready_ok hR
  obtain ⟨-, -, n3⟩ := places_nodup ((F.planOk_ok).1 hpl).places
  have hsum : (σ.row.map (·.1.moves.length)).sum =
      (σ.block.rounds.zip σ.block.oracles).length := by
    unfold Side.fits at hfit
    simp only [Bool.and_eq_true, beq_iff_eq] at hfit
    have h1 : σ.half.rounds = σ.block.rounds.length := hfit.1.2
    rw [List.length_zip, hfit.2, Nat.min_self, ← h1]
    unfold Side.half Placed.rounds
    rw [foldl_moves, Nat.zero_add, List.map_map]
    rfl
  obtain ⟨pre, t, n, hcut, hle, hp0, hstr, hown, hn⟩ :=
    steps_stand s3 n3 σ hblk hg hparts hsum u hu hpos
  subst hn
  refine ⟨pre, t, hcut, hle, hp0, ?_, hstr, hown⟩
  have e := congrArg List.length hown
  rw [List.length_map, List.length_take, List.length_drop] at e
  omega

/-- **Where the second member's rounds stand**: stands_rest (Sim/FrameAtRun.lean) at the last chain.
-/
theorem stands_rest_last {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (J : TestJob (Local W₀ Rc Xi Tr) Y) (Js : SimJob Xi)
    (σ : Side F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Xi) (hblk : σ.block ∈
        F.second.blocksInOrder)
    (hrow : σ.row = testPairs J Js) (hfit : σ.fits = true)
    (hmem : restMember J Js ∈ σ.members)
    (hpos : (restPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).moves.length ≠ 0)
    (g : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y)
    (hg : (P.second.find? fun g => g.place == σ.block.place) = some g)
    (hparts : g.parts = [firstPart J, restPart J]) :
    ∃ pre t, StandsAt F.second.blocksInOrder R.second σ (restMember J Js) pre t
      (firstLen J.p.nums.stages) := by
  have l1 : (firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).moves.length =
      firstLen J.p.nums.stages :=
    (congrArg List.length (first_moves J)).trans (len_movesFrom J _ _ _)
  have hp' : g.parts = σ.row.map (·.1) := by
    rw [hparts, hrow]
    rfl
  obtain ⟨pre, t, S⟩ := stands_member_last hpl hR σ hblk hfit (restMember J Js) hmem hpos g hg hp'
  have e : ((σ.row.take (restMember (V := Local W₀ Rc Xi Tr) J Js).number).map
      (·.1.moves.length)).sum =
      firstLen J.p.nums.stages := by
    rw [hrow, ← l1]
    show (firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).moves.length + 0 = _
    exact Nat.add_zero _
  rw [e] at S
  exact ⟨pre, t, S⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.frame_at_second
#print axioms ProofFile.Honest.K12.Light.stands_member_last
#print axioms ProofFile.Honest.K12.Light.stands_rest_last
