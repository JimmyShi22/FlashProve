-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/FrameAtFirst.lean

Conditionals: nothing here shows that ready or runC returns at any prover and book.

What it proves. At the first chain, general in the description, the side and the member: what
Sim/StandsOfFilling.lean (stands_first), Sim/FrameAtRun.lean (frame_at_run, draws_at_run,
stands_member, stands_rest) and Sim/PlayedAtRun.lean (played_at_run) prove at the shared chain:
where a member's rounds stand, from what the prover's first list holds; what the frame gives at a
called part at one run (the stand's input, what it has heard and seen, the front in closed form, the
run's challenges and positions at the part); the challenges' form; and that the rounds which the
run has produced in front of the part are those of the chain's walk over just these rounds.

Names.
  planOk_shaped_first   under planOk each block of the first chain is shaped.
  stands_first_own, stands_member_own, stands_rest_own   where the first, any, the second member's
      rounds stand.
  frame_at_first, draws_at_first   at a called part; the challenges' form.
  played_at_first       the run's rounds in front are those of the walk over just these rounds.

By what. The elder proofs, step for step, with the first chain's names; of the frame's laws:
mid_first, before_first, at_first, steps_stand (Law/Rule/Stands.lean), places_nodup (Law/Cuts.lean),
walk_mid, walk_cut, midInW_of (Law/WalkMid.lean), told_live (Law/RunMid.lean), and the others that
the three elder heads name.

Limits.
- Second texts of seven proofs, made by program out of the elder files.
- StandsAt does not say whose part plays, nor what the parts in front have played.
- Of the stand's "own" and of its field opened nothing. carriedAt is neither a premise nor
  concluded. The first chain alone.
- Of the walk (runC): the stand is midAtW's (Honest/MidW.lean); of play and of midAt nothing is
  said. Nothing of it is the kind K12's but the two statements that name the test's pair
  (stands_first_own, stands_rest_own).
- The stand is the state that midAtW (Honest/MidW.lean) returns. That runC's own walk goes through
  that state is not said here.
- They move no count. Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlayedAtRun
import Johnson.Desc.ProofFile.Honest.K12.TreeInFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (FileDescription Block blocksOk)

/-- Under planOk each block of the first chain's flat list is shaped: planOk_shaped
(TreeInFront.lean) at the first chain. -/
theorem planOk_shaped_first {Xi : Type} {F : FileDescription Xi} (h : F.planOk = true) :
    ∀ b ∈ F.first.blocksInOrder, b.shaped = true := by
  have hb : blocksOk F.first.blocksInOrder = true := by
    cases hb : blocksOk F.first.blocksInOrder with
    | true => rfl
    | false => simp [FileDescription.planOk, FileDescription.planOkCore, hb] at h
  intro b hm
  have := List.all_eq_true.1 hb b hm
  rw [Bool.and_eq_true] at this
  exact this.2

/-- **Where the first member's rounds stand, from what the prover's first list holds**: stands_first
(Sim/StandsOfFilling.lean) at the first chain. -/
theorem stands_first_own {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (J : TestJob (Local W₀ Rc Xi Tr) Y) (Js : SimJob Xi)
    (σ : Side F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Xi) (hblk : σ.block ∈
        F.first.blocksInOrder)
    (hrow : σ.row = testPairs J Js) (hfit : σ.fits = true)
    (hmem : firstMember J Js ∈ σ.members) (hpos : firstLen J.p.nums.stages ≠ 0)
    (g : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y)
    (hg : (P.first.find? fun g => g.place == σ.block.place) = some g)
    (hparts : g.parts = [firstPart J, restPart J]) :
    ∃ pre t, StandsAt F.first.blocksInOrder R.first σ (firstMember J Js) pre t 0 := by
  obtain ⟨-, tr, -, -, -, s1, -, -⟩ := ready_ok hR
  obtain ⟨n1, -, -⟩ := places_nodup ((F.planOk_ok).1 hpl).places
  have l1 : (firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).moves.length =
      firstLen J.p.nums.stages :=
    (congrArg List.length (first_moves J)).trans (len_movesFrom J _ _ _)
  have hsum : (σ.row.map (·.1.moves.length)).sum =
      (σ.block.rounds.zip σ.block.oracles).length := by
    unfold Side.fits at hfit
    simp only [Bool.and_eq_true, beq_iff_eq] at hfit
    have h1 : σ.half.rounds = σ.block.rounds.length := hfit.1.2
    rw [List.length_zip, hfit.2, Nat.min_self, ← h1]
    unfold Side.half Placed.rounds
    rw [hrow]
    show (firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).moves.length +
        ((restPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).moves.length + 0) =
      0 + (firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).moves.length +
        (restPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).moves.length
    omega
  have hp' : g.parts = σ.row.map (·.1) := by
    rw [hparts, hrow]
    rfl
  obtain ⟨pre, t, n, hcut, hle, hp0, hstr, hown, hn⟩ :=
    steps_stand s1 n1 σ hblk hg hp' hsum (firstMember J Js) hmem (by
      show (firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).moves.length ≠ 0
      rw [l1]
      exact hpos)
  have hn0 : n = 0 := hn
  subst hn0
  refine ⟨pre, t, hcut, hle, hp0, ?_, hstr, hown⟩
  have e := congrArg List.length hown
  rw [List.length_map, List.length_take, List.length_drop] at e
  omega

/-- **What the frame gives at a called part of the first chain, at one run**: frame_at_run
(Sim/FrameAtRun.lean) there. n: the rounds of the first chain in front of the member. -/
theorem frame_at_first {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₁ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₁ F.Cl)) (i n : ℕ)
    (S : StandsAt F.first.blocksInOrder R.first σ u pre t i)
    (hn : n = (pre.flatMap (·.rounds)).length + i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (st : List (ℕ × ℕ × List UInt64)) :
    ∃ m, midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      m.st.input = R.own ∧ m.st.heard = ρ.first.take n ∧ m.loc = ρ.first.take n ∧
      m.seen = roundsOf (r.run.played.1.take n) ∧
      r.run.beforeAt st ⟨σ.block.place, u.number⟩ =
        (laidOf F ρ (r.run.played.1.take n) [] []).front 0 st ∧
      m.seen = (r.run.beforeAt st ⟨σ.block.place, u.number⟩).seen ∧
      r.run.drawnAt ⟨σ.block.place, u.number⟩ = (ρ.first.drop n).take u.rounds.length ∧
      r.run.askedAt ⟨σ.block.place, u.number⟩ =
        asksFrom (treeAsks F ρ 0) (u.rounds.map (·.2.length))
          (((rowsOfChain F.first.blocksInOrder).take n).map (·.2.length)).sum ∧
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
  have hA := at_first hrun hR o₁ o₂ o₃ hp ha
  have hRO := (runOk_of hrun).1
  obtain ⟨m, hm, hseen⟩ := mid_first hrun hR o₁ o₂ o₃ hp ha hseg hc
  have hbf := before_first hrun hR o₁ o₂ o₃ hp ha hseg (treeAsks F ρ 0)
    (shown_is hRO 0 (by decide)) st
  rw [htw] at hbf hseen
  have e1 : ((R.first.drop n).take u.rounds.length).map (·.oracles.length) =
      u.rounds.map (·.2.length) := by
    have g := congrArg (List.map (·.2.length)) hown
    rw [List.map_map] at g
    exact g
  have e2 : (R.first.take n).map (·.oracles.length) =
      ((rowsOfChain F.first.blocksInOrder).take n).map (·.2.length) := by
    rw [← steps_pairs s1, ← List.map_take, List.map_map]
    rfl
  have hst : m.st.input = R.own ∧ m.st.heard = ρ.first.take n ∧
      m.loc = ρ.first.take n := by
    have h0 := hm
    unfold midAtW at h0
    obtain ⟨R', hR', h0⟩ := exBind_ok h0
    rw [hR] at hR'
    cases hR'
    obtain ⟨a₁, ha₁, h1⟩ := exBind_ok h0
    split at h1
    case isFalse hno => exact absurd ha hno
    unfold midInW at h1
    split at h1
    · cases h1
    · obtain ⟨y, hy, e⟩ := exMap_ok h1
      rw [htw] at hy
      obtain ⟨a1, a2, -⟩ := walk_mid ha₁ hy e
      have a3 := walk_hears _ _ _ _ a₁ y (start_hears ha₁) hy m e
      have a4 := walk_laid_drawn _ _ _ a₁ y hy
      rw [start_laid ha₁, List.map_nil, List.nil_append] at a4
      rw [a4] at a3
      exact ⟨a1, a3.trans (List.nil_append _), a2.trans (List.nil_append _)⟩
  refine ⟨m, hm, hst.1, hst.2.1, hst.2.2, hseen, hbf.trans rfl, ?_, drawnAt_of hA hstr, ?_,
    asked_is r.run hRO⟩
  · rw [hbf, hseen, seen_by, roundsOff_by]
  · rw [askedAt_of hA hstr (treeAsks F ρ 0) (runC_asks hrun hR o₁ o₂ o₃ 0), e1, e2]

/-- **The run's own challenges at the part have the form that the member's rounds declare**:
draws_at_run (Sim/FrameAtRun.lean) at the first chain. -/
theorem draws_at_first {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true) (hρ : ρ.due F = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₁ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₁ F.Cl)) (i : ℕ) (S : StandsAt F.first.blocksInOrder R.first σ u pre t i) :
    drawsFit (u.rounds.map (·.1)) (r.run.drawnAt ⟨σ.block.place, u.number⟩) = true := by
  have Q := (F.planOk_ok).1 hpl
  have hp := Q.places
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨ha, -, -, -⟩ := stretch_back S.str S.pos S.fits
  rw [drawnAt_of (at_first hrun hR o₁ o₂ o₃ hp ha) S.str]
  unfold Draws.due at hρ
  simp only [Bool.and_eq_true] at hρ
  have h2 : drawsFit (F.first.blocksInOrder.flatMap (·.rounds)) ρ.first = true := hρ.1.1.1
  have eD : F.first.blocksInOrder.flatMap (·.rounds) = R.first.map (·.decl) := by
    rw [← rows_fst F.first.blocksInOrder (planOk_shaped_first hpl), ← steps_pairs s1, List.map_map]
    rfl
  have eU : ((R.first.map (·.decl)).drop ((pre.flatMap (·.rounds)).length + i)).take
      u.rounds.length = u.rounds.map (·.1) := by
    have g := congrArg (List.map (·.1)) S.own
    rw [List.map_map] at g
    rw [← List.map_drop, ← List.map_take]
    exact g
  have hlen : (pre.flatMap (·.rounds)).length + i + u.rounds.length ≤
      (R.first.map (·.decl)).length := by
    rw [List.length_map]
    exact S.fits
  rw [eD, ← List.take_append_drop ((pre.flatMap (·.rounds)).length + i) (R.first.map (·.decl)),
    ← List.take_append_drop u.rounds.length
      ((R.first.map (·.decl)).drop ((pre.flatMap (·.rounds)).length + i)), eU] at h2
  have h3 := (drawsFit_cut _ _ _ h2).2
  rw [List.length_take, Nat.min_eq_left (by omega)] at h3
  have h4 := (drawsFit_cut _ _ _ h3).1
  rw [List.length_map] at h4
  exact h4

/-- **Where a member's rounds stand, from what the prover's first list holds**: stands_member
(Sim/FrameAtRun.lean) at the first chain. -/
theorem stands_member_own {Xi W₀ Rc Ky Tr X₀ Y Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (σ : Side F.S₁ F.Cl (Local W₀ Rc Xi Tr)
        (Local W₀ Rc Xi Tr) Y Pb)
    (hblk : σ.block ∈ F.first.blocksInOrder) (hfit : σ.fits = true)
    (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Pb) (hu : u ∈ σ.members)
    (hpos : u.part.moves.length ≠ 0) (g : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y)
    (hg : (P.first.find? fun g => g.place == σ.block.place) = some g)
    (hparts : g.parts = σ.row.map (·.1)) :
    ∃ pre t, StandsAt F.first.blocksInOrder R.first σ u pre t
      ((σ.row.take u.number).map (·.1.moves.length)).sum := by
  obtain ⟨-, tr, -, -, -, s1, -, -⟩ := ready_ok hR
  obtain ⟨n1, -, -⟩ := places_nodup ((F.planOk_ok).1 hpl).places
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
    steps_stand s1 n1 σ hblk hg hparts hsum u hu hpos
  subst hn
  refine ⟨pre, t, hcut, hle, hp0, ?_, hstr, hown⟩
  have e := congrArg List.length hown
  rw [List.length_map, List.length_take, List.length_drop] at e
  omega

/-- **Where the second member's rounds stand**: stands_rest (Sim/FrameAtRun.lean) at the first
chain. -/
theorem stands_rest_own {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (J : TestJob (Local W₀ Rc Xi Tr) Y) (Js : SimJob Xi)
    (σ : Side F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Xi) (hblk : σ.block ∈
        F.first.blocksInOrder)
    (hrow : σ.row = testPairs J Js) (hfit : σ.fits = true)
    (hmem : restMember J Js ∈ σ.members)
    (hpos : (restPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).moves.length ≠ 0)
    (g : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y)
    (hg : (P.first.find? fun g => g.place == σ.block.place) = some g)
    (hparts : g.parts = [firstPart J, restPart J]) :
    ∃ pre t, StandsAt F.first.blocksInOrder R.first σ (restMember J Js) pre t
      (firstLen J.p.nums.stages) := by
  have l1 : (firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).moves.length =
      firstLen J.p.nums.stages :=
    (congrArg List.length (first_moves J)).trans (len_movesFrom J _ _ _)
  have hp' : g.parts = σ.row.map (·.1) := by
    rw [hparts, hrow]
    rfl
  obtain ⟨pre, t, S⟩ := stands_member_own hpl hR σ hblk hfit (restMember J Js) hmem hpos g hg hp'
  have e : ((σ.row.take (restMember (V := Local W₀ Rc Xi Tr) J Js).number).map
      (·.1.moves.length)).sum =
      firstLen J.p.nums.stages := by
    rw [hrow, ← l1]
    show (firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).moves.length + 0 = _
    exact Nat.add_zero _
  rw [e] at S
  exact ⟨pre, t, S⟩

/-- **At a called part of the first chain: the rounds that the run has produced in front of the
part are those of the chain's walk over just these rounds, from runC's own start**; and the stand is
the state that this walk holds at its end: played_at_run (Sim/PlayedAtRun.lean) at the first
chain. -/
theorem played_at_first {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₁ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₁ F.Cl)) (i n : ℕ)
    (S : StandsAt F.first.blocksInOrder R.first σ u pre t i)
    (hn : n = (pre.flatMap (·.rounds)).length + i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ a₁ y m, ChainProgress.start ⟨0, 0, P.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ P))
        (some (F.start₁ (F.pub x))) [] = .ok a₁ ∧
      walk ⟨0, 0, P.storedWords w₀ rc, treeOwn⟩ (R.first.take n) (ρ.first.take n) a₁ = .ok y ∧
      y.laid = r.run.played.1.take n ∧ y.mid = some m ∧
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
  have hA := at_first hrun hR o₁ o₂ o₃ hp ha
  have hb := told_behind hA (stretch_of R.first _ hseg) hc (fun p hp' hat => by
    rcases List.mem_append.1 hp' with g | g
    · rcases List.mem_append.1 g with g | g
      · exact g
      · rw [all_of_map (laidAs_mask l2 _) (off_chain (by decide) c1 c2 ha) p g] at hat
        cases hat
    · rw [all_of_map (laidAs_mask l3 _) (off_chain (by decide) c1 c3 ha) p g] at hat
      cases hat)
  obtain ⟨R', a₁, z₁, a₂, z₂, a₃, z₃, hR', ha₁, hz₁, -, -, -, -, -, rfl⟩ := runC_parts hrun
  rw [hR] at hR'
  cases hR'
  obtain ⟨y, w1, w2, e1, e2⟩ := walk_cut (start_laid ha₁) hz₁
    (R.first.takeWhile fun s => s.addr != ⟨σ.block.place, u.number⟩).length
    (List.takeWhile_prefix _).length_le
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (told_live _ _ _ y z₁ _ w2 e2 hb)
  have k1 : midInW ⟨0, 0, P.storedWords w₀ rc, treeOwn⟩ R.first ρ.first a₁
      ⟨σ.block.place, u.number⟩ = .ok (some m) := (midInW_of ha w1).trans (by rw [hm])
  rw [htw] at w1 e1
  refine ⟨a₁, y, m, ha₁, w1, e1, hm, ?_⟩
  unfold midAtW
  simp only [hR, ha₁, Except.bind]
  rw [if_pos ha]
  exact k1

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.planOk_shaped_first
#print axioms ProofFile.Honest.K12.Light.stands_first_own
#print axioms ProofFile.Honest.K12.Light.frame_at_first
#print axioms ProofFile.Honest.K12.Light.draws_at_first
#print axioms ProofFile.Honest.K12.Light.stands_member_own
#print axioms ProofFile.Honest.K12.Light.stands_rest_own
#print axioms ProofFile.Honest.K12.Light.played_at_first
