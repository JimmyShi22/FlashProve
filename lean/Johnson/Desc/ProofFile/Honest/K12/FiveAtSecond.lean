-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FiveAtSecond.lean

A conditional: nothing here shows that ready or runC returns, or that the part is called.

What it proves. FiveAtRun.lean's statement at the last chain ("the second chain" of the format and
of the frame; the frame's number 2): the five clauses le, leS, heardFit, heard, fold of OnFreeT, in
its own letters, at a run of the frame's walking prover: at the stand that midAtW returns in front
of a proximity test's second part, at the blocks that the part is handed as carried, at the run's
own front. General in the description, the book, the prover and the two jobs; where the first fold's
fresh table has come earlier.

It pays none of door, asks, trees. At a state on entry that is the job's own letter rec₀, not shown
to be the verifier's.

Names.
  carried_of_row_second   what the second part is handed as carried, out of the lending of the row.
  five_at_second          the five clauses.

By what. The proofs of carried_of_row_first and five_at_first (FiveAtFirst.lean), with the last
chain's names: first_play_at_second (FirstPlayAtSecond.lean); the frame's mid_second, before_second
at the three chains' lists; five_of_lent (Sim/FiveFromPlay.lean), which is general in the table and
the look-up.

Limits. Those of FiveAtRun.lean and OnFreeTAtRun.lean. In this chain the lending looks values up in
all three chains' purses. That the premise on the book (tiesB) holds at the request's own test at
the maker's book is ties_second and ties_of_lent_second (AtProof/MakerBook.lean): at every plan,
under named premises. Of the walk (runC). It moves no
count. Nothing on completeness, soundness or hiding.
The stand is the state that midAtW (Honest/MidW.lean) returns. That runC's own walk goes through
that state is not said here.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.FirstPlayAtSecond
import Johnson.Desc.ProofFile.Honest.K12.FiveAtFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block FileDescription Place)
open Johnson.Prover.Link (μOf rowOf)
open H2K.Pub (sgOf)
open ProofFile.Honest

/-- What the second part of a pair is handed as carried, out of the lending of the pair's row in the
last chain: carried_of_row (OnFreeTAtRun.lean) there. -/
theorem carried_of_row_second {V W X : Type} {Bk : ProverCoinCounts} (k : Coins Bk) (a : Place)
    (p₀ p₁ : Part V W X)
    (c : RowCoins [p₀, p₁])
    (hl : lendRow Bk (Bk.rowsOf 2) (k.look 2) a [p₀, p₁] 0 = .ok c) :
    carriedAt Bk k 2 ⟨a, 1⟩ p₁ = .ok c.2.1.2.2 := by
  have h1 := (lendRow_cons_ok (lendRow_cons_ok hl).2).1
  unfold carriedAt
  rw [h1]
  rfl

/-- **The five clauses le, leS, heardFit, heard, fold of OnFreeT at a run, in the last chain**:
five_at_run (FiveAtRun.lean) there: in OnFreeT's own letters, at the stand that midAtW returns in
front of the test's second part, at the blocks that the part is handed as carried, at the run's own
front. It pays none of door, asks, trees. At a state on entry that is the job's own letter rec₀, not
shown to be the verifier's. Of the walk (runC); nothing on whether runC returns or calls the part.
Where the first fold's fresh table has come earlier alone. -/
theorem five_at_second {Xi W₀ Rc Ky Tr X₀ Y Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (J : TestJob (Local W₀ Rc Xi Tr) Y) (f : Addr × ℕ) (hfr : J.fresh = some f)
    (Js : SimJob Pb)
    (hR : ready F Bk P w₀ rc x k = .ok R)
    (σ : Side F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Pb) (pre t : List (Block F.S₃
        F.Cl))
    (S : StandsAt F.second.blocksInOrder R.second σ (restMember J Js) pre t (firstLen J.p.nums.stages))
    (hg : (P.second.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J))
    (hlaid : σ.block.rounds.zip σ.block.oracles = J.laid)
    (hT : tiesB Bk J.p.place J.members.length = true)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (D : ℕ → Fmt.Drawn)
    (T : FirstTies J s next rest D
      ((ρ.second.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)))
    (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hrows : ∀ (w : Local W₀ Rc Xi Tr) (fr : Front Y) (mem mem' : ℕ → Stretch),
      (∀ t, t < J.members.length → mem t = mem' t) →
      μOf (sgOf s) (J.rows₀ w fr mem) = μOf (sgOf s) (J.rows₀ w fr mem'))
    (hfit : drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
      ((ρ.second.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) = true)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, (restMember (V := Local W₀ Rc Xi Tr) J Js).number⟩ = true)
    (st : List (ℕ × ℕ × List UInt64)) :
    ∃ (c : RowCoins [(firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y), restPart J])
      (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y),
      midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, (restMember (V := Local W₀ Rc Xi Tr) J Js).number⟩ =
        .ok (some m) ∧
      carriedAt Bk k 2 ⟨σ.block.place, (restMember (V := Local W₀ Rc Xi Tr) J Js).number⟩
        (restMember (V := Local W₀ Rc Xi Tr) J Js).part = .ok c.2.1.2.2 ∧
      m.st.input = R.own ∧
      firstLen J.p.nums.stages ≤ m.st.heard.length ∧
      firstLen J.p.nums.stages ≤ m.seen.length ∧
      drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
        (m.st.lately (firstLen J.p.nums.stages)) = true ∧
      (lastSeen (r.run.beforeAt st ⟨σ.block.place, (restMember (V := Local W₀ Rc Xi Tr) J
          Js).number⟩)
        (firstLen J.p.nums.stages)).map (·.drawn) =
        m.st.lately (firstLen J.p.nums.stages) ∧
      (lastSeen (r.run.beforeAt st ⟨σ.block.place, (restMember (V := Local W₀ Rc Xi Tr) J
          Js).number⟩)
        (firstLen J.p.nums.stages)).tail =
        aFold (coinsOf J.p.nums.stages (carriedCoins J (stretches _ c.2.1.2.2)).hide fun _ => 0) 0
          J.s₀ 1
          (rowsAt J (stretches _ c.2.1.2.2) m)
          (rowOf (J.recB m.st.input (restFront J m) (heardIn J m 0))) (heardIn J m) := by
  obtain ⟨c, m₀, m, y, hl, hm, hplay, hy, hin0, -⟩ :=
    first_play_at_second hpl J hR σ _ pre t S hg hlaid hrun hc
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
  obtain ⟨m', hm', hseen⟩ := mid_second hrun hR o₁ o₂ o₃ hp ha hseg hc
  obtain rfl : m' = m := Option.some.inj (Except.ok.inj (hm'.symm.trans hm))
  have hbef := before_second hrun hR o₁ o₂ o₃ hp ha hseg (treeAsks F ρ 0) (treeAsks F ρ 1)
    (treeAsks F ρ 2) (shown_is (runOk_of hrun).1 0 (by decide))
    (shown_is (runOk_of hrun).1 1 (by decide)) (shown_is (runOk_of hrun).1 2 (by decide)) st
  have hfront : m'.seen = (r.run.beforeAt st
      ⟨σ.block.place, (restMember (V := Local W₀ Rc Xi Tr) J Js).number⟩).seen := by
    rw [hbef, seen_by, hseen]
    unfold roundsOff
    rw [List.map_append, List.map_append]
    have e0 := roundsOff_by 0 (treeAsks F ρ 0) r.run.played.1 0
    have e1 := roundsOff_by 1 (treeAsks F ρ 1) r.run.played.2.1 0
    have e2 := roundsOff_by 2 (treeAsks F ρ 2) (r.run.played.2.2.take
      (R.second.takeWhile fun s =>
        s.addr != ⟨σ.block.place, (restMember (V := Local W₀ Rc Xi Tr) J Js).number⟩).length) 0
    unfold roundsOff at e0 e1 e2
    rw [e0, e1, e2]
  have hinm : m'.st.input = R.own := by
    rw [← hy, (play_mid _ _ _ _ y hplay).1]
    exact hin0
  refine ⟨c, m', hm, carried_of_row_second k σ.block.place _ _ c hl, hinm, ?_⟩
  rw [← hplace] at hl
  obtain ⟨y', hplay', -, hon⟩ := five_of_lent (V := Local W₀ Rc Xi Tr) J f hfr Bk (Bk.rowsOf 2)
    (k.look 2) c hl hT σ.block.name ⟨σ.block.place, 0⟩ (some R.own) s next rest m₀ D _ T hk
    (hrows _ _) hfit (r.run.beforeAt st ⟨σ.block.place, (restMember (V := Local W₀ Rc Xi Tr) J
        Js).number⟩)
  obtain rfl : y' = y := Except.ok.inj (hplay'.symm.trans hplay)
  rw [hy] at hon
  exact hon hfront

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.carried_of_row_second
#print axioms ProofFile.Honest.K12.Light.five_at_second
