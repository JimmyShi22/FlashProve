-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FiveAtRun.lean

What it proves. The five clauses le, leS, heardFit, heard, fold of OnFreeT (Sim/TreesExact.lean), in
that structure's own letters, as five conjuncts, at a run of the frame's walking prover (runC): at
the stand in front of a proximity test's second part, where that part is called; at the blocks that
the part is handed as carried; at the run's own front. As onFreeT_at_run (OnFreeTAtRun.lean), less
its arrow: no stand in front of the first part and nothing at the test's entry stands in the
conclusion: a caller lays OnFreeT by its constructor from these five and its own door, asks and
trees at the same stand.

It pays none of door, asks, trees. At a state on entry that is the job's own letter rec₀, not shown
to be the verifier's.

Names.
  five_at_run   the theorem.

By what. first_play_at_run (FirstPlayAtRun.lean); five_of_lent (Sim/FiveFromPlay.lean);
carried_of_row (OnFreeTAtRun.lean); and the frame's laws that OnFreeTAtRun.lean's head names.

Limits. Those of OnFreeTAtRun.lean: what is asked (public at the place; on the challenges; on the
job's text; on the filling and the book, tiesB among it; on the run); of the walk (runC), not of
play (run); nothing on whether ready or runC returns, or whether the part is called; where the first
fold's fresh table has come earlier alone. Its proof is a second text of onFreeT_at_run's. It moves
no count. Nothing on completeness, on soundness or on what a view shows.
The stand is the state that midSharedAtW (Honest/MidW.lean) returns. That runC's own walk goes
through that state is not said here.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.OnFreeTAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.FiveFromPlay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block FileDescription)
open Johnson.Prover.Link (μOf rowOf)
open H2K.Pub (sgOf)
open ProofFile.Honest

/-- **The five at a run, in OnFreeT's own letters, at the run's stand and own front.** As
onFreeT_at_run (OnFreeTAtRun.lean), less the arrow: no stand in front of the first part, no D's tie
to the entry and no AtEntryT stand in the conclusion: a caller lays OnFreeT by its constructor from
these five and its own door, asks, trees at m. mem is what the second part is handed as carried.
Public at the place: hpl, hlaid, hk, and T's fields stages, enough, sorts, tables. On the
challenges: hfit, and T's fields len, own. On the job's text: hrows. On the filling and the book:
hR, S, hg, hT.
On the run: hrun, hc. It pays none of door, asks, trees. Of the walk (runC); nothing on whether runC
returns or calls the part. Where the first fold's fresh table has come earlier alone. -/
theorem five_at_run {Xi W₀ Rc Ky Tr X₀ Y Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (J : TestJob (Common W₀ Rc Ky) X₀) (f : Addr × ℕ) (hfr : J.fresh = some f)
    (Js : SimJob Pb)
    (hR : ready F Bk P w₀ rc x k = .ok R)
    (σ : Side F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Pb) (pre t : List (Block F.S₂ F.Cl))
    (S : StandsAt F.shared.blocksInOrder R.shared σ (restMember J Js) pre t (firstLen J.p.nums.stages))
    (hg : (P.shared.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J))
    (hlaid : σ.block.rounds.zip σ.block.oracles = J.laid)
    (hT : tiesB Bk J.p.place J.members.length = true)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (D : ℕ → Fmt.Drawn)
    (T : FirstTies J s next rest D
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)))
    (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hrows : ∀ (w : Common W₀ Rc Ky) (fr : Front X₀) (mem mem' : ℕ → Stretch),
      (∀ t, t < J.members.length → mem t = mem' t) →
      μOf (sgOf s) (J.rows₀ w fr mem) = μOf (sgOf s) (J.rows₀ w fr mem'))
    (hfit : drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) = true)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = true)
    (st : List (ℕ × ℕ × List UInt64)) :
    ∃ (c : RowCoins [(firstPart J : Part Empty (Common W₀ Rc Ky) X₀), restPart J])
      (m : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀),
      midSharedAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ =
        .ok (some m) ∧
      carriedAt Bk k 1 ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩
        (restMember (V := Empty) J Js).part = .ok c.2.1.2.2 ∧
      m.st.input = ⟨w₀, rc, P.key x⟩ ∧
      firstLen J.p.nums.stages ≤ m.st.heard.length ∧
      firstLen J.p.nums.stages ≤ m.seen.length ∧
      drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
        (m.st.lately (firstLen J.p.nums.stages)) = true ∧
      (lastSeen (r.run.beforeAt st ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩)
        (firstLen J.p.nums.stages)).map (·.drawn) =
        m.st.lately (firstLen J.p.nums.stages) ∧
      (lastSeen (r.run.beforeAt st ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩)
        (firstLen J.p.nums.stages)).tail =
        aFold (coinsOf J.p.nums.stages (carriedCoins J (stretches _ c.2.1.2.2)).hide fun _ => 0) 0
          J.s₀ 1
          (rowsAt J (stretches _ c.2.1.2.2) m)
          (rowOf (J.recB m.st.input (restFront J m) (heardIn J m 0))) (heardIn J m) := by
  obtain ⟨c, m₀, m, y, hl, hm, hplay, hy, hin0, -⟩ :=
    first_play_at_run hpl J hR σ _ pre t S hg hlaid hrun hc
  have hplace : J.p.place = σ.block.place := by
    have := List.find?_some hg
    exact beq_iff_eq.1 this
  have Q := (F.planOk_ok).1 hpl
  have hp := Q.places
  obtain ⟨-, tr', -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨ha, hN, -, hseg⟩ := stretch_back S.str S.pos S.fits
  obtain ⟨m', hm', hseen⟩ := mid_shared hrun hR o₁ o₂ o₃ hp ha hseg hc
  obtain rfl : m' = m := Option.some.inj (Except.ok.inj (hm'.symm.trans hm))
  have hbef := before_shared hrun hR o₁ o₂ o₃ hp ha hseg (treeAsks F ρ 1)
    (shown_is (runOk_of hrun).1 1 (by decide)) st
  have hfront : m'.seen = (r.run.beforeAt st
      ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩).seen := by
    rw [hbef, seen_by, roundsOff_by, hseen]
  have hinm : m'.st.input = ⟨w₀, rc, P.key x⟩ := by
    rw [← hy, (play_mid _ _ _ _ y hplay).1]
    exact hin0
  refine ⟨c, m', hm, carried_of_row k σ.block.place _ _ c hl, hinm, ?_⟩
  rw [← hplace] at hl
  obtain ⟨y', hplay', -, hon⟩ := five_of_lent (V := Empty) J f hfr Bk (Bk.rowsOf 1)
    (sharedLook Bk k.shared) c hl hT σ.block.name ⟨σ.block.place, 0⟩ none s next rest m₀ D _ T hk
    (hrows _ _) hfit (r.run.beforeAt st ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩)
  obtain rfl : y' = y := Except.ok.inj (hplay'.symm.trans hplay)
  rw [hy] at hon
  exact hon hfront

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.five_at_run
