-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/MeetsAtSecond.lean

Conditionals: nothing here shows that ready or runC returns at a prover whose list for the last
chain holds these two parts, at a book that lends them.

What it proves. At the last chain (one chain, three names: "the last chain" here; "the second chain"
in the format, in the frame's fields second and in Sim/FirstAnyAtHeadW.lean; the frame numbers it 2,
and its places bear chain 3), general in the description: what Sim/MeetsAtRun.lean (meets_at_run),
Sim/StandsOfFilling.lean (stands_first) and Sim/FrameAtRun.lean (draws_at_run) prove at the shared
chain: the first member of a proximity test, at one run of the frame's runC: the record MeetsAt
(Sim/MeetsOwnAtHead.lean) as a conclusion at that run's stand and own front, challenges and
positions; where the first member's rounds stand, from what the prover's list holds; the challenges'
form. Face .own; the chain's number 2.

Names.
  planOk_shaped_second   under planOk each block of the last chain is shaped.
  meets_at_second        the first member at one run.
  stands_first_last      where the first member's rounds stand.
  drawn_at_second, draws_at_second   the run's challenges at a part: which; their form.

By what. The elder proofs, step for step, with the last chain's names: mid_second
(Law/RunMidFile.lean), at_second, drawnAt_of, askedAt_of, runC_asks (Law/RunAtFile.lean),
before_second (Law/RunBefore.lean), steps_stand (Law/Rule/Stands.lean), places_nodup
(Law/Cuts.lean), roundsOff_by, seen_by (Law/Rule/Faith.lean), and the others that the elder heads
name. One step is new: in this chain a stand has seen all rounds of the two earlier chains and then
the chain's own in front of the part, and the front lists the same three stretches.

Limits. All limits of Sim/MeetsAtRun.lean, among them: no premise says that the part which the
prover plays at the member's address is this member's part; StandsAt does not say whose part plays;
the carried values are any, not those that the book lends; the equation samples the part's own
values anew: it says nothing on the values of the run; the first member alone; one request.
MeetsEvery is a premise here: whoever pays it names the public premises under which the first
member's sentence stands, formPubB J.p = true (h ≤ k) and Js.p = J.p among them. ft, the number in
the label of the chain's first own tree, is a letter. Second texts, made by program out of the elder
files. They move no count. Nothing on completeness, soundness or hiding.
The stand is the state that midAtW (Honest/MidW.lean) returns. That runC's own walk goes through
that state is not said here.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.FrameAtRun
import Johnson.Desc.ProofFile.Honest.K12.TreeInFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (FileDescription Block blocksOk)

/-- Under planOk each block of the last chain's flat list is shaped: planOk_shaped
(TreeInFront.lean) at the last chain. -/
theorem planOk_shaped_second {Xi : Type} {F : FileDescription Xi} (h : F.planOk = true) :
    ∀ b ∈ F.second.blocksInOrder, b.shaped = true := by
  have hb : blocksOk F.second.blocksInOrder = true := by
    cases hb : blocksOk F.second.blocksInOrder with
    | true => rfl
    | false => simp [FileDescription.planOk, FileDescription.planOkCore, hb] at h
  intro b hm
  have := List.all_eq_true.1 hb b hm
  rw [Bool.and_eq_true] at this
  exact this.2

/-- **The first member of a proximity test in the last chain, at one run's stand and own front,
challenges and positions**: meets_at_run (Sim/MeetsAtRun.lean) at the last chain: face .own, the
chain's number 2; ft: the number in the label of the chain's first own tree: a letter. hpl: public.
hR, S: on the filling and the book. hrun, hc: on the run. hd, hb, hE: on public data; a caller pays
them. -/
theorem meets_at_second {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (J : TestJob (Local W₀ Rc Xi Tr) Y) (Js : SimJob Xi) (ft : ℕ)
    (σ : Side F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Xi) (pre t : List (Block F.S₃
        F.Cl))
    (S : StandsAt F.second.blocksInOrder R.second σ (firstMember J Js) pre t 0)
    (hc : r.called ⟨σ.block.place, 0⟩ = true)
    (hd : drawsFit ((firstMember (V := Local W₀ Rc Xi Tr) J Js).rounds.map (·.1))
      ((ρ.second.drop (pre.flatMap (·.rounds)).length).take
        (firstMember (V := Local W₀ Rc Xi Tr) J Js).rounds.length) = true)
    (hb : testBud Js 0 ((ρ.second.drop (pre.flatMap (·.rounds)).length).take
        (firstMember (V := Local W₀ Rc Xi Tr) J Js).rounds.length)
      (asksFrom (treeAsks F ρ 2) ((firstMember (V := Local W₀ Rc Xi Tr) J Js).rounds.map
          (·.2.length))
        (((rowsOfChain F.second.blocksInOrder).take (pre.flatMap (·.rounds)).length).map
          (·.2.length)).sum))
    (hE : ∀ ca m, MeetsEvery .own σ 2 ft J Js ca m) :
    ∃ m, midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, 0⟩ = .ok (some m) ∧
      ∀ ca, MeetsAt .own σ 2 ft (testOn .own J Js) (testBud Js) (firstMember J Js) ca m
        (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
          ⟨σ.block.place, 0⟩)
        (r.run.drawnAt ⟨σ.block.place, 0⟩) (r.run.askedAt ⟨σ.block.place, 0⟩) := by
  have Q := (F.planOk_ok).1 hpl
  have hp := Q.places
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  have hstr : InStretch R.second ⟨σ.block.place, 0⟩ (pre.flatMap (·.rounds)).length
      (firstMember (V := Local W₀ Rc Xi Tr) J Js).rounds.length := S.str
  have hown : ((R.second.drop (pre.flatMap (·.rounds)).length).take
      (firstMember (V := Local W₀ Rc Xi Tr) J Js).rounds.length).map (fun s => (s.decl, s.oracles))
          =
      (firstMember (V := Local W₀ Rc Xi Tr) J Js).rounds := S.own
  have hfit : (pre.flatMap (·.rounds)).length + (firstMember (V := Local W₀ Rc Xi Tr) J
      Js).rounds.length ≤
      R.second.length := S.fits
  obtain ⟨ha, htw, -, hseg⟩ := stretch_back hstr S.pos hfit
  have hA := at_second hrun hR o₁ o₂ o₃ hp ha
  have hRO := (runOk_of hrun).1
  obtain ⟨m, hm, hseen⟩ := mid_second hrun hR o₁ o₂ o₃ hp ha hseg hc
  refine ⟨m, hm, fun ca => ?_⟩
  have hbf := before_second hrun hR o₁ o₂ o₃ hp ha hseg (treeAsks F ρ 0) (treeAsks F ρ 1)
    (treeAsks F ρ 2) (shown_is hRO 0 (by decide)) (shown_is hRO 1 (by decide))
    (shown_is hRO 2 (by decide)) (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
  rw [htw] at hbf hseen
  have e1 : ((R.second.drop (pre.flatMap (·.rounds)).length).take
      (firstMember (V := Local W₀ Rc Xi Tr) J Js).rounds.length).map (·.oracles.length) =
      (firstMember (V := Local W₀ Rc Xi Tr) J Js).rounds.map (·.2.length) := by
    have g := congrArg (List.map (·.2.length)) hown
    rw [List.map_map] at g
    exact g
  have e2 : (R.second.take (pre.flatMap (·.rounds)).length).map (·.oracles.length) =
      ((rowsOfChain F.second.blocksInOrder).take (pre.flatMap (·.rounds)).length).map (·.2.length) := by
    rw [← steps_pairs s3, ← List.map_take, List.map_map]
    rfl
  rw [drawnAt_of hA hstr,
    askedAt_of hA hstr (treeAsks F ρ 2) (runC_asks hrun hR o₁ o₂ o₃ 2), e1, e2, hbf]
  refine hE ca m _ _ _ ?_ hd hb
  rw [hseen, seen_by]
  unfold roundsOff
  rw [List.map_append, List.map_append]
  have e0 := roundsOff_by 0 (treeAsks F ρ 0) r.run.played.1 0
  have e1' := roundsOff_by 1 (treeAsks F ρ 1) r.run.played.2.1 0
  have e2' := roundsOff_by 2 (treeAsks F ρ 2)
    (r.run.played.2.2.take (pre.flatMap (·.rounds)).length) 0
  unfold roundsOff at e0 e1' e2'
  rw [e0, e1', e2']

/-- **Where the first member's rounds stand, from what the prover's list for the last chain holds**:
stands_first (Sim/StandsOfFilling.lean) at the last chain. -/
theorem stands_first_last {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (J : TestJob (Local W₀ Rc Xi Tr) Y) (Js : SimJob Xi)
    (σ : Side F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Xi) (hblk : σ.block ∈
        F.second.blocksInOrder)
    (hrow : σ.row = testPairs J Js) (hfit : σ.fits = true)
    (hmem : firstMember J Js ∈ σ.members) (hpos : firstLen J.p.nums.stages ≠ 0)
    (g : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y)
    (hg : (P.second.find? fun g => g.place == σ.block.place) = some g)
    (hparts : g.parts = [firstPart J, restPart J]) :
    ∃ pre t, StandsAt F.second.blocksInOrder R.second σ (firstMember J Js) pre t 0 := by
  obtain ⟨-, tr, -, -, -, -, -, s3⟩ := ready_ok hR
  obtain ⟨-, -, n3⟩ := places_nodup ((F.planOk_ok).1 hpl).places
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
    steps_stand s3 n3 σ hblk hg hp' hsum (firstMember J Js) hmem (by
      show (firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).moves.length ≠ 0
      rw [l1]
      exact hpos)
  have hn0 : n = 0 := hn
  subst hn0
  refine ⟨pre, t, hcut, hle, hp0, ?_, hstr, hown⟩
  have e := congrArg List.length hown
  rw [List.length_map, List.length_take, List.length_drop] at e
  omega

/-- The run's own challenges at a part of the last chain are the part's stretch of the chain's list.
-/
theorem drawn_at_second {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₃ F.Cl)) (i : ℕ) (S : StandsAt F.second.blocksInOrder R.second σ u pre t i) :
    r.run.drawnAt ⟨σ.block.place, u.number⟩ =
      (ρ.second.drop ((pre.flatMap (·.rounds)).length + i)).take u.rounds.length := by
  have Q := (F.planOk_ok).1 hpl
  have hp := Q.places
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨ha, -, -, -⟩ := stretch_back S.str S.pos S.fits
  exact drawnAt_of (at_second hrun hR o₁ o₂ o₃ hp ha) S.str

/-- **The run's own challenges at the part have the form that the member's rounds declare**:
draws_at_run (Sim/FrameAtRun.lean) at the last chain. -/
theorem draws_at_second {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true) (hρ : ρ.due F = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₃ F.Cl)) (i : ℕ) (S : StandsAt F.second.blocksInOrder R.second σ u pre t i) :
    drawsFit (u.rounds.map (·.1)) (r.run.drawnAt ⟨σ.block.place, u.number⟩) = true := by
  have Q := (F.planOk_ok).1 hpl
  have hp := Q.places
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨ha, -, -, -⟩ := stretch_back S.str S.pos S.fits
  rw [drawnAt_of (at_second hrun hR o₁ o₂ o₃ hp ha) S.str]
  unfold Draws.due at hρ
  simp only [Bool.and_eq_true] at hρ
  have h2 : drawsFit (F.second.blocksInOrder.flatMap (·.rounds)) ρ.second = true := hρ.1.2
  have eD : F.second.blocksInOrder.flatMap (·.rounds) = R.second.map (·.decl) := by
    rw [← rows_fst F.second.blocksInOrder (planOk_shaped_second hpl), ← steps_pairs s3, List.map_map]
    rfl
  have eU : ((R.second.map (·.decl)).drop ((pre.flatMap (·.rounds)).length + i)).take
      u.rounds.length = u.rounds.map (·.1) := by
    have g := congrArg (List.map (·.1)) S.own
    rw [List.map_map] at g
    rw [← List.map_drop, ← List.map_take]
    exact g
  have hlen : (pre.flatMap (·.rounds)).length + i + u.rounds.length ≤
      (R.second.map (·.decl)).length := by
    rw [List.length_map]
    exact S.fits
  rw [eD, ← List.take_append_drop ((pre.flatMap (·.rounds)).length + i) (R.second.map (·.decl)),
    ← List.take_append_drop u.rounds.length
      ((R.second.map (·.decl)).drop ((pre.flatMap (·.rounds)).length + i)), eU] at h2
  have h3 := (drawsFit_cut _ _ _ h2).2
  rw [List.length_take, Nat.min_eq_left (by omega)] at h3
  have h4 := (drawsFit_cut _ _ _ h3).1
  rw [List.length_map] at h4
  exact h4

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.planOk_shaped_second
#print axioms ProofFile.Honest.K12.Light.meets_at_second
#print axioms ProofFile.Honest.K12.Light.stands_first_last
#print axioms ProofFile.Honest.K12.Light.drawn_at_second
#print axioms ProofFile.Honest.K12.Light.draws_at_second
