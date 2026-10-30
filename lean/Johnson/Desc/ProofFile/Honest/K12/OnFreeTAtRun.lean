-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/OnFreeTAtRun.lean

What it proves. Five of the eight clauses of OnFreeT (Sim/TreesExact.lean), le, leS, heardFit, heard
and fold, as conclusions at a run of the frame's walking prover (runC): at the stand in front of a
proximity test's second part, where that part is called, at the blocks that the part is handed as
carried, and at the run's own front. The three others, door, asks and trees, stay premises, at the
entry's letters (AtEntryT, Sim/OnTFromPlay.lean). General in the description, the book, the prover
and the two jobs; where the first fold's fresh table has come earlier.

It pays none of door, asks, trees. At a state on entry that is the job's own letter rec₀, not shown
to be the verifier's.

Names.
  carried_of_row   what the second part of a pair is handed as carried, out of the lending of the
      pair's row.
  onFreeT_at_run   the theorem.

By what. first_play_at_run (FirstPlayAtRun.lean); onFreeT_of_lent (Sim/OnTFromPlay.lean). Of the
frame's laws (ProofFile/Honest/Law/): mid_shared (RunMidFile.lean); before_shared (RunBefore.lean);
seen_by, roundsOff_by (Rule/Faith.lean); shown_is, runOk_of (Rule/Reads.lean); lendRow_cons_ok
(Rule/RowModel.lean); look_shared, steps_shaped (Along.lean); stretch_back (OwedParts.lean);
ready_ok (Run.lean).

Limits.
- door, asks and trees are asked, at a stand m₀ that stands under "there is": of m₀ the input and
  what it has seen are said; what it has heard, what the parts pass on and its field opened are not
  (frontBy m₀ 0, at which the three are asked, hands that field on).
- Asked besides. Public at the place: hlaid; T's fields stages, enough, sorts, tables; hk. On the
  challenges: hfit; T's fields len and own. On the job's text: hrows (for a job made of a ManyJob:
  rowsMu_many, Sim/ExactFirstAtU.lean). On the filling and the book: hR, S, hg, and hT: tiesB, a
  test with code on the book's entries. On the run: hrun, hc.
- Of the walk (runC), not of play (run); nothing on whether ready or runC returns, or whether the
  part is called.
- Where the first fold's fresh table has come earlier (fresh = some f) alone: the arm of the test on
  G_u; the arm of the test on G_omega has no like.
- The stand is the state that midSharedAtW (Honest/MidW.lean) returns. That runC's own walk goes
  through that state is not said here.
- It moves no count. Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.FirstPlayAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.OnTFromPlay
import Johnson.Desc.ProofFile.Honest.Law.Rule.Faith
import Johnson.Desc.ProofFile.Honest.Law.Rule.Reads
import Johnson.Desc.ProofFile.Honest.Law.Rule.RowModel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Codes)
open VerifiableInference.Desc (Block FileDescription Place)
open Johnson.Prover.Link (μOf)
open H2K.Pub (sgOf)
open ProofFile.Honest

/-- What the second part of a pair is handed as carried, out of the lending of the pair's row in the
shared chain. -/
theorem carried_of_row {V W X : Type} {Bk : ProverCoinCounts} (k : Coins Bk) (a : Place) (p₀ p₁ : Part V W X)
    (c : RowCoins [p₀, p₁])
    (hl : lendRow Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) a [p₀, p₁] 0 = .ok c) :
    carriedAt Bk k 1 ⟨a, 1⟩ p₁ = .ok c.2.1.2.2 := by
  have h1 := (lendRow_cons_ok (lendRow_cons_ok hl).2).1
  unfold carriedAt
  rw [look_shared, h1]
  rfl

/-- **The five clauses le, leS, heardFit, heard, fold of OnFreeT as conclusions at a run; the three
others as premises at the entry's letters.** J: a test's job whose first fold's fresh table has
come earlier (hfr). Js: a simulators' job. At a run of the frame's walking prover, at the stand m in
front of the test's second part (the member restMember J Js), where that part is called, and at the
run's own front at any list st of stored columns: there are values c of the pair's type, and what
the second part is handed as carried is c's (that the book has lent the pair c is not in the end);
there is a stand m₀, with the run's input, that has seen what m has seen of the blocks in front; and
OnFreeT holds at m and that front as soon as its clauses door, asks and trees hold at the entry's
letters (AtEntryT at m₀'s input and frontBy m₀ 0).
It pays none of door, asks, trees.
Public at the place: hpl, hlaid, hk, and T's fields stages, enough, sorts, tables. On the
challenges: hfit, and T's fields len, own (D: the first part's challenges by number). On the job's
text: hrows.
On the filling and the book: hR, S, hg, hT. On the run: hrun, hc.
Of the walk (runC); nothing on whether runC returns or calls the part. -/
theorem onFreeT_at_run {Xi W₀ Rc Ky Tr X₀ Y Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (J : TestJob (Common W₀ Rc Ky) X₀) (f : Addr × ℕ) (hfr : J.fresh = some f)
    (Js : SimJob Pb) (K : Codes) (chain : ℕ) (os : List (Fmt.Shape × Fmt.TreeSource)) (pb : Pb)
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
      (m₀ m : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀),
      midSharedAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ =
        .ok (some m) ∧
      carriedAt Bk k 1 ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩
        (restMember (V := Empty) J Js).part = .ok c.2.1.2.2 ∧
      m₀.st.input = ⟨w₀, rc, P.key x⟩ ∧ m.st.input = ⟨w₀, rc, P.key x⟩ ∧
      m₀.seen = m.seen.take (pre.flatMap (·.rounds)).length ∧
      (AtEntryT J Js K chain os pb (stretches _ c.2.1.2.2) m₀.st.input (frontBy m₀ 0) D
          (r.run.beforeAt st ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩) →
        OnFreeT J Js K chain os pb (stretches _ c.2.1.2.2) m
          (r.run.beforeAt st ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩)) := by
  obtain ⟨p, ms, fresh, r₁, ro, tr⟩ := J
  obtain rfl : fresh = some f := hfr
  obtain ⟨c, m₀, m, y, hl, hm, hplay, hy, hin0, hseen0⟩ := first_play_at_run hpl
    (⟨p, ms, some f, r₁, ro, tr⟩ : TestJob (Common W₀ Rc Ky) X₀) hR σ _ pre t S hg hlaid hrun hc
  have hplace : p.place = σ.block.place := by
    have := List.find?_some hg
    exact beq_iff_eq.1 this
  -- the frame's laws at this run
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
      ⟨σ.block.place, (restMember (V := Empty) (⟨p, ms, some f, r₁, ro, tr⟩ :
        TestJob (Common W₀ Rc Ky) X₀) Js).number⟩).seen := by
    rw [hbef, seen_by, roundsOff_by, hseen]
  have hinm : m'.st.input = ⟨w₀, rc, P.key x⟩ := by
    rw [← hy, (play_mid _ _ _ _ y hplay).1]
    exact hin0
  refine ⟨c, m₀, m', hm, carried_of_row k σ.block.place _ _ c hl, hin0, hinm, hseen0,
    fun E => ?_⟩
  rw [← hplace] at hl
  obtain ⟨y', hplay', -, hon⟩ := onFreeT_of_lent (V := Empty) p ms f r₁ ro tr Js K chain os pb Bk
    (Bk.rowsOf 1) (sharedLook Bk k.shared) c hl hT σ.block.name ⟨σ.block.place, 0⟩ none s next rest
    m₀ D _ T hk (hrows _ _) hfit _ E
  obtain rfl : y' = y := Except.ok.inj (hplay'.symm.trans hplay)
  rw [hy] at hon
  exact hon hfront

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.carried_of_row
#print axioms ProofFile.Honest.K12.Light.onFreeT_at_run
