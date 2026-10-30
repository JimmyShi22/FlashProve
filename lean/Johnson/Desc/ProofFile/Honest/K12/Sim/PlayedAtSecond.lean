-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/PlayedAtSecond.lean

Conditionals: nothing here shows that ready or runC returns at any prover and book.

What it proves. At the last chain (one chain, three names: "the last chain" here; "the second chain"
in the format and in the frame's fields second; the frame numbers it 2, and its places bear chain
3): at a called part, at a run of the frame's walking prover (runC): the rounds that the run has
produced in front of the part are those of the last chain's walk over just these rounds, from the
start that runC itself lays behind its walks of the whole first chain and of the whole shared chain;
and the stand that midAtW (Honest/MidW.lean) returns is the state that this walk holds at its end:
played_at_run (Sim/PlayedAtRun.lean) at the last chain. And, general in the chain: where a chain's
walk has a real round, both of its starts were there.

Names.
  starts_some        a real round gives both starts.
  played_at_second   the run's rounds in front are those of the walk over just these rounds.

By what. The frame's walk_cut, midInW_of (Law/WalkMid.lean), told_live, walk_laid'
(Law/RunMid.lean), start_live, walk_live (Honest/WalkLive.lean), start_laid
(Honest/WalkHeard.lean), told_behind (Law/RunMidFile.lean), at_second (Law/RunAtFile.lean),
runC_parts, runC_laidAs.

Limits.
- played_at_second's proof is a second text of the frame's proof of mid_second
  (Law/RunMidFile.lean), which does not state the walks.
- StandsAt does not say whose part plays, nor what the parts in front have played.
- Of the walk (runC): of play and of midAt nothing is said. General in the description, the side and
  the member.
- The stand is the state that midAtW (Honest/MidW.lean) returns. That runC's own walk goes through
  that state is not said here.
- They move no count. Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlayedAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (FileDescription Block)

/-- **Where a chain's walk has a real round, both of its starts were there**: the state of the
prover's run and the verifier's state. General in the chain and in the columns front₀ that the start
is handed. The frame's told_live (Law/RunMid.lean): the prover's run was going on at the start;
start_live (Honest/WalkLive.lean): then both were there. For the last chain, whose two starts are
Options. -/
theorem starts_some {S Cl W Y : Type} (L : Lay) (bs : List (Block S Cl)) (mo : Option
    (ProofFile.Honest.Mid W Y))
    (v : Option S) {a z : ChainProgress S Cl W Y} {ss : List (Step W Y)} {ds : List Fmt.Drawn}
    {front₀ : List VerifiableInference.Desc.OpenedColumn} (n : ℕ)
    (ha : ChainProgress.start L bs mo v front₀ = .ok a) (hz : walk L ss ds a = .ok z)
    (ht : ∃ p ∈ z.laid.drop n, p.told = true) :
    ∃ m₀ v₀, mo = some m₀ ∧ v = some v₀ := by
  obtain ⟨ps, f, -⟩ := walk_laid' L ss ds a z hz
  obtain ⟨p, hp, e⟩ := ht
  have hp' : p ∈ ps := by
    have g := List.mem_of_mem_drop hp
    rw [f, start_laid ha, List.nil_append] at g
    exact g
  exact start_live ha (told_live L ss ds a z ps hz f ⟨p, hp', e⟩)

/-- **At a called part of the last chain: the rounds that the run has produced in front of the part
are those of the last chain's walk over just these rounds, from runC's own start behind the two
earlier chains' walks**; and the stand is the state that this walk holds at its end: played_at_run
(Sim/PlayedAtRun.lean) at the last chain. m₁, m₂: the states that the walks of the whole first chain
and of the whole shared chain hold at their ends. -/
theorem played_at_second {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₃ F.Cl)) (i n : ℕ)
    (S : StandsAt F.second.blocksInOrder R.second σ u pre t i)
    (hn : n = (pre.flatMap (·.rounds)).length + i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ (m₁ : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y) (m₂ : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀) (m :
                    ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y) (a₁ z₁ : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) Y)
      (a₂ z₂ : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀) (a₃ y : ChainProgress F.S₃ F.Cl (Local W₀ Rc Xi Tr) Y),
      ChainProgress.start ⟨0, 0, P.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ P))
        (some (F.start₁ (F.pub x))) [] = .ok a₁ ∧
      walk ⟨0, 0, P.storedWords w₀ rc, treeOwn⟩ R.first ρ.first a₁ = .ok z₁ ∧
      z₁.laid = r.run.played.1 ∧ z₁.mid = some m₁ ∧
      ChainProgress.start ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ P))
        (some (F.start₂ (F.pub x))) [] = .ok a₂ ∧
      walk ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ R.shared ρ.shared a₂ = .ok z₂ ∧
      z₂.laid = r.run.played.2.1 ∧ z₂.mid = some m₂ ∧
      ChainProgress.start ⟨2, F.lastChainFirstTreeNumber, P.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ F.second.blocksInOrder
        (some (R.start₃ P m₁ m₂)) (door₃ F x z₁.ver z₂.ver) (z₁.cols ++ z₂.cols) = .ok a₃ ∧
      walk ⟨2, F.lastChainFirstTreeNumber, P.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ (R.second.take n)
        (ρ.second.take n) a₃ = .ok y ∧
      y.laid = r.run.played.2.2.take n ∧ y.mid = some m ∧
      midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) := by
  have Q := (F.planOk_ok).1 hpl
  have hp := Q.places
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  have hstr := S.str
  have hfit := S.fits
  rw [← hn] at hstr hfit
  obtain ⟨ha, htw, -, hseg⟩ := stretch_back hstr S.pos hfit
  obtain ⟨l1, l2, l3⟩ := runC_laidAs hrun hR o₁ o₂ o₃
  obtain ⟨p1, p2, p3⟩ := places_chain hp
  have c1 := steps_chain s1 p1
  have c2 := steps_chain s2 p2
  have c3 := steps_chain s3 p3
  have hA := at_second hrun hR o₁ o₂ o₃ hp ha
  have hb := told_behind hA (stretch_of R.second _ hseg) hc (fun p hp' hat => by
    rcases List.mem_append.1 hp' with g | g
    · rcases List.mem_append.1 g with g | g
      · rw [all_of_map (laidAs_mask l1 _) (off_chain (by decide) c3 c1 ha) p g] at hat
        cases hat
      · rw [all_of_map (laidAs_mask l2 _) (off_chain (by decide) c3 c2 ha) p g] at hat
        cases hat
    · exact g)
  have hnot : R.first.any (·.addr == ⟨σ.block.place, u.number⟩) = false := by
    rw [List.any_eq_false]
    intro s hs
    rw [off_chain (by decide) c3 c1 ha s hs]
    exact Bool.false_ne_true
  obtain ⟨R', a₁, z₁, a₂, z₂, a₃, z₃, hR', ha₁, hz₁, hq, ha₂, hz₂, ha₃, hz₃, rfl⟩ :=
    runC_parts hrun
  rw [hR] at hR'
  cases hR'
  obtain ⟨y, w1, w2, e1, e2⟩ := walk_cut (start_laid ha₃) hz₃
    (R.second.takeWhile fun s => s.addr != ⟨σ.block.place, u.number⟩).length
    (List.takeWhile_prefix _).length_le
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (told_live _ _ _ y z₃ _ w2 e2 hb)
  obtain ⟨m₀, _, e0, -⟩ := start_live ha₃ (walk_live _ _ _ a₃ y m w1 hm)
  have ha₃₀ := ha₃
  have hno : ¬ R.first.any (·.addr == ⟨σ.block.place, u.number⟩) = true := by
    rw [hnot]
    exact Bool.false_ne_true
  cases hm₁ : z₁.mid with
  | none =>
    rw [hm₁] at e0
    cases e0
  | some m₁ =>
    cases hm₂ : z₂.mid with
    | none =>
      rw [hm₁, hm₂] at e0
      cases e0
    | some m₂ =>
      rw [hm₁, hm₂] at ha₃
      have ha₃' : ChainProgress.start ⟨2, F.lastChainFirstTreeNumber, P.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩
          F.second.blocksInOrder (some (R.start₃ P m₁ m₂)) (door₃ F x z₁.ver z₂.ver)
          (z₁.cols ++ z₂.cols) = .ok a₃ := ha₃
      have k1 : midInW ⟨2, F.lastChainFirstTreeNumber, P.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ R.second
          ρ.second a₃ ⟨σ.block.place, u.number⟩ = .ok (some m) :=
        (midInW_of ha w1).trans (by rw [hm])
      rw [htw] at w1 e1
      refine ⟨m₁, m₂, m, a₁, z₁, a₂, z₂, a₃, y, ha₁, hz₁, rfl, hm₁, ha₂, hz₂, rfl, hm₂, ha₃', w1,
        e1, hm, ?_⟩
      unfold midAtW
      simp only [hR, ha₁, Except.bind]
      rw [if_neg hno]
      simp only [hz₁, hq, ha₂, hz₂, ha₃₀, Bool.not_true, Bool.false_eq_true, if_false]
      exact k1

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.starts_some
#print axioms ProofFile.Honest.K12.Light.played_at_second
