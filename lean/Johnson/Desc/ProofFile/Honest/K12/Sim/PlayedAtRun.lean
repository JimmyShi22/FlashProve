-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/PlayedAtRun.lean: at a run of the frame's walking prover
(`runC`, Johnson/Desc/ProofFile/Honest/Walk.lean), at a called part of the shared chain: the rounds
that the run has produced in front of the part are those that the shared chain's walk over just
these rounds produces, from the start that `runC` itself lays, tables and all; and the stand that
`midSharedAtW` (Johnson/Desc/ProofFile/Honest/MidW.lean) returns is the state that this walk holds
at its end. General in the description, the book, the prover, the side and the member.

A conditional: nothing here shows that `ready` or `runC` returns, or that the part is called.

  `played_at_run`   the statement

What for. Of the stand and of a run's own letters at a part (the front, the challenges, the
positions asked) Sim/FrameAtRun.lean gives closed forms (of the stand: of its input, of what it has
heard and seen and of `loc`; not of `own`, nor of the field `opened`) but for one term: the front is
made of the walk's first n rounds. By this file these are a field of a term in which the run does
not stand: `walk` at what `ready` has laid, at the description's own start, at the prover's stored
words and at the challenges.

By what. The frame's own laws `walk_cut` and `midInW_of`
(Johnson/Desc/ProofFile/Honest/Law/WalkMid.lean) and `told_live` (Law/RunMid.lean). The proof is,
in its second half, a second text of the proof of `mid_shared` (Law/RunMidFile.lean), which keeps
the stand alone: `told_behind`, `runC_laidAs`, `places_chain`, `steps_chain`, `off_chain`,
`laidAs_mask`, `all_of_map`, `runC_parts`, `start_laid`. Its first half is that of `frame_at_run`
(Sim/FrameAtRun.lean): `FileDescription.planOk_ok`, `ready_ok`, `steps_shaped`, `stretch_back`,
`at_shared`.

Limits. Of the walk (`runC`): of `play` and of `midSharedAt` nothing is said. `StandsAt` does not
say whose part plays, nor what the parts in front have played. The shared chain alone. Steps of the
frame's: no property of a prover or a protocol. Nothing on completeness, soundness or hiding.
The stand is the state that `midSharedAtW` (Honest/MidW.lean) returns. That `runC`'s own walk goes
through that state is not said here.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.FrameAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (FileDescription Block)

/-- **At a called part of the shared chain: the rounds that the run has produced in front of the
part are those of the shared chain's walk over just these rounds, from runC's own start; and the
stand is the state that this walk holds at its end.** hpl: public.
hR, S: on the filling and the book. hrun, hc: on the run. n: the rounds of the shared chain in front
of the member. -/
theorem played_at_run {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₂ F.Cl V (Common W₀ Rc Ky) X₀ Pb) (u : Member V (Common W₀ Rc Ky) X₀ Pb)
    (pre t : List (Block F.S₂ F.Cl)) (i n : ℕ)
    (S : StandsAt F.shared.blocksInOrder R.shared σ u pre t i)
    (hn : n = (pre.flatMap (·.rounds)).length + i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ a₂ y m, ChainProgress.start ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ P))
        (some (F.start₂ (F.pub x))) [] = .ok a₂ ∧
      walk ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ (R.shared.take n) (ρ.shared.take n) a₂ = .ok y ∧
      y.laid = r.run.played.2.1.take n ∧ y.mid = some m ∧
      midSharedAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) := by
  have Q := (F.planOk_ok).1 hpl
  have hp := Q.places
  obtain ⟨-, tr, -, -, hcom, s1, s2, s3⟩ := ready_ok hR
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
  have hA := at_shared hrun hR o₁ o₂ o₃ hp ha
  have hb := told_behind hA (stretch_of R.shared _ hseg) hc (fun p hp' hat => by
    rcases List.mem_append.1 hp' with g | g
    · rcases List.mem_append.1 g with g | g
      · rw [all_of_map (laidAs_mask l1 _) (off_chain (by decide) c2 c1 ha) p g] at hat
        cases hat
      · exact g
    · rw [all_of_map (laidAs_mask l3 _) (off_chain (by decide) c2 c3 ha) p g] at hat
      cases hat)
  obtain ⟨R', a₁, z₁, a₂, z₂, a₃, z₃, hR', -, -, -, ha₂, hz₂, -, -, rfl⟩ := runC_parts hrun
  rw [hR] at hR'
  cases hR'
  obtain ⟨y, w1, w2, e1, e2⟩ := walk_cut (start_laid ha₂) hz₂
    (R.shared.takeWhile fun s => s.addr != ⟨σ.block.place, u.number⟩).length
    (List.takeWhile_prefix _).length_le
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (told_live _ _ _ y z₂ _ w2 e2 hb)
  have k1 : midInW ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ R.shared ρ.shared a₂
      ⟨σ.block.place, u.number⟩ = .ok (some m) := (midInW_of ha w1).trans (by rw [hm])
  rw [htw] at w1 e1
  refine ⟨a₂, y, m, ha₂, w1, e1, hm, ?_⟩
  unfold midSharedAtW
  simp only [hR, ha₂, Except.bind]
  exact k1

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.played_at_run
