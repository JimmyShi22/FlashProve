-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/CalledAtSecond.lean

A conditional: nothing here shows that ready or runC returns or that the part is called.

What it proves. called_at_run (CalledAtRun.lean) at the last chain ("the second chain" of the format
and of the frame; the frame's number 2): at a called part, at a run of the frame's walking prover:
the stand that midAtW returns, with the request's own input; it has seen all rounds of the two
earlier chains and then the last chain's in front of the part; both earlier chains' verifier's ends
are there, and the description's start of the last chain returns at them; the description's own fold
over the blocks in front, from that start, at the run's own rounds and columns, returns with nothing
left over; and these columns are the filling of what the blocks in front read, own trees and trees
taken over from the two earlier chains. General in the description, the book, the prover, the side,
the member and the blocks in front.

Names.
  called_at_second   the theorem.

By what. called_fold (CalledFold.lean), which is general in the chain; starts_some, played_at_second
(Sim/PlayedAtSecond.lean); the frame's mid_second (Law/RunMidFile.lean), at_second
(Law/RunAtFile.lean),
envOf_tree's second half (Law/Cut.lean), walk_mid (Law/WalkMid.lean), runC_parts.

Limits.
- By the frame's runC_ends (Law/RunC.lean) the two ends are the description's folds over the whole
  first and the whole shared chain at the run's own views: that step is a caller's; it is not drawn
  here.
- At the request's own proximity test the blocks in front have no round (by the description's text:
  Johnson/Desc/Third/Chain.lean): there the fold is at no round and at what these blocks read.
- In what the stand has seen the first chain's piece holds that chain's sealing round, which the
  first view lacks.
- Its proof is a third text of called_at_run's.
- Of the walk (runC), not of play (run): at an address of this chain midAtW (Honest/MidW.lean) is
  made of ready, of the walks over the whole first and the whole shared chain with the test on the
  sealing round, of the start as runC lays it behind these and of walk over the Steps in front of
  the part: the stand is the state that this last walk holds. Of midAt, which is made of play,
  nothing is said.
- The stand is the state that midAtW (Honest/MidW.lean) returns. That runC's own walk goes through
  that state is not said here.
- It moves no count. Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.CalledFold
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlayedAtSecond

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block OpenedColumn FileDescription foldBlocks)
open ProofFile.Honest

/-- **At a called part of the last chain, at a run of the frame's walking prover**: called_at_run
(CalledAtRun.lean) at the last chain. Where ready and runC return and the part is called: midAtW
returns a stand m; its input is the request's own; m has seen all rounds of the two earlier chains
and then the last chain's in front of the part; both earlier chains' verifier's ends are there (e₁,
e₂) and the description's start of the last chain returns v₀ at them; the last view's rounds and
columns begin with the chain's rounds in front of the part and with cols; the description's own fold
over the blocks in front, from v₀, at these blocks' rounds and at cols, returns, with no round and
no column left; and cols is the filling of what these blocks' declared rounds read at what was
drawn, own trees and trees taken over from the two earlier chains (the frame's readsOf at the
chain's number 2 and treeThird).
Public: hpl. On the filling and the book: hR, S. On the run: hrun, hc. Of the walk (runC). -/
theorem called_at_second {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₃ F.Cl)) (i : ℕ) (S : StandsAt F.second.blocksInOrder R.second σ u pre t i)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y) (e₁ : F.S₁) (e₂ : F.S₂) (v₀ s : F.S₃) (cols more :
              List OpenedColumn)
      (rest : List Fmt.RoundView) (tr : Tr),
      midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      P.trace w₀ x = some tr ∧ m.st.input = ⟨w₀, rc, x, tr⟩ ∧
      m.seen = roundsOf r.run.played.1 ++ roundsOf r.run.played.2.1 ++
        roundsOf (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + i)) ∧
      r.ends.1 = some e₁ ∧ r.ends.2.1 = some e₂ ∧ F.start₃ (F.pub x) e₁ e₂ = .ok v₀ ∧
      r.run.views.2.2.rounds =
        roundsOf (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + i)) ++ rest ∧
      r.run.views.2.2.opened = cols ++ more ∧
      foldBlocks F.lastChainFirstTreeNumber pre v₀
        (roundsOf (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)) cols = .ok (s, [], []) ∧
      fillCols (readsOf 2 F.lastChainFirstTreeNumber (P.storedWords w₀ rc)
        (treeThird r.run.played.1 r.run.played.2.1
          (r.run.played.2.2.take (pre.flatMap (·.rounds)).length))
        (pre.flatMap (·.rounds))
        ((r.run.played.2.2.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cols := by
  have Q := (F.planOk_ok).1 hpl
  have hp := Q.places
  obtain ⟨-, tr, htr, hown, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨ha, hN, -, hseg⟩ := stretch_back S.str S.pos S.fits
  obtain ⟨m, hm, hseen⟩ := mid_second hrun hR o₁ o₂ o₃ hp ha hseg hc
  rw [hN] at hseen
  obtain ⟨l1, l2, l3⟩ := runC_laidAs hrun hR o₁ o₂ o₃
  obtain ⟨p1, p2, p3⟩ := places_chain hp
  have c1 := steps_chain s1 p1
  have c2 := steps_chain s2 p2
  have c3 := steps_chain s3 p3
  have hA := at_second hrun hR o₁ o₂ o₃ hp ha
  have hb := told_behind hA S.str hc (fun p hp' hat => by
    rcases List.mem_append.1 hp' with g | g
    · rcases List.mem_append.1 g with g | g
      · rw [all_of_map (laidAs_mask l1 _) (off_chain (by decide) c3 c1 ha) p g] at hat
        cases hat
      · rw [all_of_map (laidAs_mask l2 _) (off_chain (by decide) c3 c2 ha) p g] at hat
        cases hat
    · exact g)
  -- the input
  have hin : m.st.input = ⟨w₀, rc, x, tr⟩ := by
    obtain ⟨m₁, m₂, m', a₁, z₁, a₂, z₂, a₃, y, -, -, -, -, -, -, -, -, ha₃, hy, -, hy', hm'⟩ :=
      played_at_second hpl hR hrun σ u pre t i _ S rfl hc
    have e : m' = m := Option.some.inj (Except.ok.inj (hm'.symm.trans hm))
    subst e
    rw [(walk_mid ha₃ hy hy').1]
    exact hown
  -- the last chain's walk
  obtain ⟨R', a₁, z₁, a₂, z₂, a₃, z₃, hR', -, -, -, -, -, ha₃, hz₃, rfl⟩ := runC_parts hrun
  rw [hR] at hR'
  cases hR'
  have hpos : 0 < σ.block.rounds.length := by
    have := S.le
    have := S.pos
    omega
  have ht : ∃ p ∈ z₃.laid.drop (pre.flatMap (·.rounds)).length, p.told = true := by
    obtain ⟨p, hp', e⟩ := hb
    have hp'' : p ∈ (z₃.laid.drop (pre.flatMap (·.rounds)).length).drop i := by
      rw [List.drop_drop]
      exact hp'
    exact ⟨p, List.mem_of_mem_drop hp'', e⟩
  obtain ⟨m₀, v₀, em, ev⟩ := starts_some _ F.second.blocksInOrder _ _ _ ha₃ hz₃ ht
  rw [em, ev, S.cut] at ha₃
  have hLo : ∀ ps, treeThird z₁.laid z₂.laid ps =
      (envOf (P.storedWords w₀ rc) (fun ch k => if ch == 0 then ((tablesOf z₁.laid)[k]?).bind id
        else if ch == 1 then ((tablesOf z₂.laid)[k]?).bind id else none) ps).tree :=
    fun ps => ((envOf_tree (P.storedWords w₀ rc) z₁.laid z₂.laid ps).2).symm
  obtain ⟨s, cols, more, hfold, hfill, hcols⟩ := called_fold
    ⟨2, F.lastChainFirstTreeNumber, P.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ hLo pre σ.block t hpos m₀ v₀
    ha₃ hz₃ ht
  -- the two ends and the start
  obtain ⟨e₁, he₁, e₂, he₂, hst⟩ : ∃ e₁, z₁.ver = some e₁ ∧ ∃ e₂, z₂.ver = some e₂ ∧
      F.start₃ (F.pub x) e₁ e₂ = .ok v₀ := by
    unfold door₃ at ev
    cases h1 : z₁.ver with
    | none =>
      rw [h1] at ev
      cases ev
    | some e₁ =>
      cases h2 : z₂.ver with
      | none =>
        rw [h1, h2] at ev
        cases ev
      | some e₂ =>
        rw [h1, h2] at ev
        refine ⟨e₁, rfl, e₂, rfl, ?_⟩
        have ev' : (F.start₃ (F.pub x) e₁ e₂).toOption = some v₀ := ev
        cases h3 : F.start₃ (F.pub x) e₁ e₂ with
        | error w =>
          rw [h3] at ev'
          cases ev'
        | ok v =>
          rw [h3] at ev'
          rw [Option.some.inj ev']
  refine ⟨m, e₁, e₂, v₀, s, cols, more,
    roundsOf (z₃.laid.drop ((pre.flatMap (·.rounds)).length + i)), tr, hm, htr, hin, hseen, he₁,
        he₂,
    hst, ?_, hcols, hfold, hfill⟩
  show roundsOf z₃.laid = _
  rw [← roundsOf_append, List.take_append_drop]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.called_at_second
