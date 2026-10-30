-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/FrameAtRun.lean: what the frame gives at a part of the shared
chain, at one run of `runC` (Johnson/Desc/ProofFile/Honest/Walk.lean): general in the description,
the side and the member, so that either member of a proximity test is a case. No fact of a kind of
sub-protocol is spent. It imports Mathlib.

A conditional. Nothing here shows that `ready` or `runC` returns at any prover and book: so nothing
here shows that the premises can be met together.

  `frame_at_run`   at a called part: the stand m that `midSharedAtW`
                 (Johnson/Desc/ProofFile/Honest/MidW.lean) returns; its input; what it has heard,
                 what its stops may read and what it has seen; the front
                 `r.run.beforeAt` (Johnson/Desc/ProofFile/Honest/Side.lean) in its closed form
                 (`laidOf`, Johnson/Desc/ProofFile/Honest/Law/Rule/Words.lean); that m has seen what
                 that front shows; the run's challenges and positions at the part in their closed
                 forms; the stored positions that the run reads, in theirs
  `draws_at_run`   the run's challenges at the part have the form that the member's
                 rounds declare, where the list of challenges passes `Draws.due`
  `stands_member`   `StandsAt` (Johnson/Desc/ProofFile/Honest/Law/OwedParts.lean) at any member with
                 a move, from what the prover's shared list holds at the side's place
  `stands_rest`  the case of a proximity test's second member

Premises, sorted. Public: `F.planOk`; `ρ.due`. On the filling and the book: `ready` has returned R;
`StandsAt`, or: the side's sub-protocol is one of the shared list, the side passes `Side.fits`, the
member is one of its members and has a move, and the first entry of the prover's shared list at the
side's place has the row's parts. On the run: `runC` has returned r; the run has called the part.

By what. The proof of `meets_at_run` (Sim/MeetsAtRun.lean) and of `stands_first`
(Sim/StandsOfFilling.lean), at a general member; the laws that go with the frame which these call;
and `walk_mid` (Law/WalkMid.lean), `walk_hears`, `start_hears`, `start_laid`, `walk_laid_drawn`
(WalkHeard.lean), `asked_is`
(Law/Rule/OnAt.lean), `rows_fst` (Law/Data.lean), `foldl_moves` (Law/Steps.lean), all under
Johnson/Desc/ProofFile/Honest/.

Limits.
- `StandsAt` reads of the prepared rounds their addresses, declared rounds and oracle messages
  alone: it does not say whose part plays at the address, nor what the parts in front have played.
  `stands_member` and `stands_rest` take that from what the prover's shared list holds at one place.
- Of the stand's state `own`, what the parts pass on, nothing is said; nor of its field `opened`,
  the columns handed to the parts.
- That the book lends the part its carried values (`carriedAt`) is neither a premise nor concluded.
- The stand is the state that `midSharedAtW` (Honest/MidW.lean) returns. That `runC`'s own walk goes
  through that state is not said here.
- The shared chain alone. One request. Nothing on what a part sends, on On or on a bound on
  positions. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.StandsOfFilling
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.Desc.ProofFile.Honest.Law.Data

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (FileDescription Block)

/-! ## 1 At a called part -/

/-- **What the frame gives at a called part of the shared chain, at one run.** General in the
description, the side and the member. hpl: public. hR, S: on the filling and the book. hrun, hc: on
the run. n: the rounds of the shared chain in front of the member. -/
theorem frame_at_run {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₂ F.Cl V (Common W₀ Rc Ky) X₀ Pb) (u : Member V (Common W₀ Rc Ky) X₀ Pb)
    (pre t : List (Block F.S₂ F.Cl)) (i n : ℕ)
    (S : StandsAt F.shared.blocksInOrder R.shared σ u pre t i)
    (hn : n = (pre.flatMap (·.rounds)).length + i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (st : List (ℕ × ℕ × List UInt64)) :
    ∃ m, midSharedAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      m.st.input = ⟨w₀, rc, P.key x⟩ ∧ m.st.heard = ρ.shared.take n ∧ m.loc = ρ.shared.take n ∧
      m.seen = roundsOf (r.run.played.2.1.take n) ∧
      r.run.beforeAt st ⟨σ.block.place, u.number⟩ =
        (laidOf F ρ [] (r.run.played.2.1.take n) []).front 1 st ∧
      m.seen = (r.run.beforeAt st ⟨σ.block.place, u.number⟩).seen ∧
      r.run.drawnAt ⟨σ.block.place, u.number⟩ = (ρ.shared.drop n).take u.rounds.length ∧
      r.run.askedAt ⟨σ.block.place, u.number⟩ =
        asksFrom (treeAsks F ρ 1) (u.rounds.map (·.2.length))
          (((rowsOfChain F.shared.blocksInOrder).take n).map (·.2.length)).sum ∧
      r.run.storedAsked = storedAsks F ρ := by
  have Q := (F.planOk_ok).1 hpl
  have hp := Q.places
  obtain ⟨-, tr, -, -, hcom, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  have hstr := S.str
  have hown := S.own
  have hfit := S.fits
  rw [← hn] at hstr hown hfit
  obtain ⟨ha, htw, -, hseg⟩ := stretch_back hstr S.pos hfit
  have hA := at_shared hrun hR o₁ o₂ o₃ hp ha
  have hRO := (runOk_of hrun).1
  obtain ⟨m, hm, hseen⟩ := mid_shared hrun hR o₁ o₂ o₃ hp ha hseg hc
  have hbf := before_shared hrun hR o₁ o₂ o₃ hp ha hseg (treeAsks F ρ 1)
    (shown_is hRO 1 (by decide)) st
  rw [htw] at hbf hseen
  have e1 : ((R.shared.drop n).take u.rounds.length).map (·.oracles.length) =
      u.rounds.map (·.2.length) := by
    have g := congrArg (List.map (·.2.length)) hown
    rw [List.map_map] at g
    exact g
  have e2 : (R.shared.take n).map (·.oracles.length) =
      ((rowsOfChain F.shared.blocksInOrder).take n).map (·.2.length) := by
    rw [← steps_pairs s2, ← List.map_take, List.map_map]
    rfl
  have hst : m.st.input = ⟨w₀, rc, P.key x⟩ ∧ m.st.heard = ρ.shared.take n ∧
      m.loc = ρ.shared.take n := by
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
      rw [htw] at hy
      obtain ⟨a1, a2, -⟩ := walk_mid ha₂ hy e
      have a3 := walk_hears _ _ _ _ a₂ y (start_hears ha₂) hy m e
      have a4 := walk_laid_drawn _ _ _ a₂ y hy
      rw [start_laid ha₂, List.map_nil, List.nil_append] at a4
      rw [a4] at a3
      exact ⟨a1.trans hcom, a3.trans (List.nil_append _), a2.trans (List.nil_append _)⟩
  refine ⟨m, hm, hst.1, hst.2.1, hst.2.2, hseen, hbf.trans rfl, ?_, drawnAt_of hA hstr, ?_,
    asked_is r.run hRO⟩
  · rw [hbf, hseen, seen_by, roundsOff_by]
  · rw [askedAt_of hA hstr (treeAsks F ρ 1) (runC_asks hrun hR o₁ o₂ o₃ 1), e1, e2]

/-! ## 2 The challenges' form -/

/-- **The run's own challenges at the part have the form that the member's rounds declare.** One
premise more, public: the list of challenges passes `Draws.due`. -/
theorem draws_at_run {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true) (hρ : ρ.due F = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₂ F.Cl V (Common W₀ Rc Ky) X₀ Pb) (u : Member V (Common W₀ Rc Ky) X₀ Pb)
    (pre t : List (Block F.S₂ F.Cl)) (i : ℕ) (S : StandsAt F.shared.blocksInOrder R.shared σ u pre t i) :
    drawsFit (u.rounds.map (·.1)) (r.run.drawnAt ⟨σ.block.place, u.number⟩) = true := by
  have Q := (F.planOk_ok).1 hpl
  have hp := Q.places
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨ha, -, -, -⟩ := stretch_back S.str S.pos S.fits
  rw [drawnAt_of (at_shared hrun hR o₁ o₂ o₃ hp ha) S.str]
  unfold Draws.due at hρ
  simp only [Bool.and_eq_true] at hρ
  have h2 : drawsFit (F.shared.blocksInOrder.flatMap (·.rounds)) ρ.shared = true := hρ.1.1.2
  have eD : F.shared.blocksInOrder.flatMap (·.rounds) = R.shared.map (·.decl) := by
    rw [← rows_fst F.shared.blocksInOrder (planOk_shaped hpl), ← steps_pairs s2, List.map_map]
    rfl
  have eU : ((R.shared.map (·.decl)).drop ((pre.flatMap (·.rounds)).length + i)).take
      u.rounds.length = u.rounds.map (·.1) := by
    have g := congrArg (List.map (·.1)) S.own
    rw [List.map_map] at g
    rw [← List.map_drop, ← List.map_take]
    exact g
  have hlen : (pre.flatMap (·.rounds)).length + i + u.rounds.length ≤
      (R.shared.map (·.decl)).length := by
    rw [List.length_map]
    exact S.fits
  rw [eD, ← List.take_append_drop ((pre.flatMap (·.rounds)).length + i) (R.shared.map (·.decl)),
    ← List.take_append_drop u.rounds.length
      ((R.shared.map (·.decl)).drop ((pre.flatMap (·.rounds)).length + i)), eU] at h2
  have h3 := (drawsFit_cut _ _ _ h2).2
  rw [List.length_take, Nat.min_eq_left (by omega)] at h3
  have h4 := (drawsFit_cut _ _ _ h3).1
  rw [List.length_map] at h4
  exact h4

/-! ## 3 Where a member's rounds stand -/

/-- **Where a member's rounds stand, from what the prover's shared list holds.** General in the
description, the side and the member. -/
theorem stands_member {Xi W₀ Rc Ky Tr X₀ Y Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (σ : Side F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Pb)
    (hblk : σ.block ∈ F.shared.blocksInOrder) (hfit : σ.fits = true)
    (u : Member Empty (Common W₀ Rc Ky) X₀ Pb) (hu : u ∈ σ.members)
    (hpos : u.part.moves.length ≠ 0) (g : Placed Empty (Common W₀ Rc Ky) X₀)
    (hg : (P.shared.find? fun g => g.place == σ.block.place) = some g)
    (hparts : g.parts = σ.row.map (·.1)) :
    ∃ pre t, StandsAt F.shared.blocksInOrder R.shared σ u pre t
      ((σ.row.take u.number).map (·.1.moves.length)).sum := by
  obtain ⟨-, tr, -, -, -, -, s2, -⟩ := ready_ok hR
  obtain ⟨-, n2, -⟩ := places_nodup ((F.planOk_ok).1 hpl).places
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
    steps_stand s2 n2 σ hblk hg hparts hsum u hu hpos
  subst hn
  refine ⟨pre, t, hcut, hle, hp0, ?_, hstr, hown⟩
  have e := congrArg List.length hown
  rw [List.length_map, List.length_take, List.length_drop] at e
  omega

/-- **The second member of a proximity test.** -/
theorem stands_rest {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (J : TestJob (Common W₀ Rc Ky) X₀) (Js : SimJob Ky)
    (σ : Side F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky) (hblk : σ.block ∈ F.shared.blocksInOrder)
    (hrow : σ.row = testPairs J Js) (hfit : σ.fits = true)
    (hmem : restMember J Js ∈ σ.members)
    (hpos : (restPart J : Part Empty (Common W₀ Rc Ky) X₀).moves.length ≠ 0)
    (g : Placed Empty (Common W₀ Rc Ky) X₀)
    (hg : (P.shared.find? fun g => g.place == σ.block.place) = some g)
    (hparts : g.parts = [firstPart J, restPart J]) :
    ∃ pre t, StandsAt F.shared.blocksInOrder R.shared σ (restMember J Js) pre t
      (firstLen J.p.nums.stages) := by
  have l1 : (firstPart J : Part Empty (Common W₀ Rc Ky) X₀).moves.length =
      firstLen J.p.nums.stages :=
    (congrArg List.length (first_moves J)).trans (len_movesFrom J _ _ _)
  have hp' : g.parts = σ.row.map (·.1) := by
    rw [hparts, hrow]
    rfl
  obtain ⟨pre, t, S⟩ := stands_member hpl hR σ hblk hfit (restMember J Js) hmem hpos g hg hp'
  have e : ((σ.row.take (restMember (V := Empty) J Js).number).map (·.1.moves.length)).sum =
      firstLen J.p.nums.stages := by
    rw [hrow, ← l1]
    show (firstPart J : Part Empty (Common W₀ Rc Ky) X₀).moves.length + 0 = _
    exact Nat.add_zero _
  rw [e] at S
  exact ⟨pre, t, S⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.frame_at_run
#print axioms ProofFile.Honest.K12.Light.draws_at_run
#print axioms ProofFile.Honest.K12.Light.stands_member
#print axioms ProofFile.Honest.K12.Light.stands_rest
