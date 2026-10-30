-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOwedChains.lean: E2E/OfflineOwedFirst.lean's sentences at the shared and the second chain, and at all
three chains the form that leaves On to its payer: what `Lettered.owedAt`
(Johnson/Desc/ProofFile/Honest/Rule.lean) asks of a list at a run of `runC` that has returned, WITHOUT the
invariants of a thread. General in the description, the book, the prover and the lists.

  `shared_stands`, `second_stands`             where the parts stand; the carried blocks; the numbers of rounds
  `shared_part_at_run`, `second_part_at_run`   the run's challenges and positions in closed form; at a called
                                             part the carried blocks and the walk's own state
  `owedAt_first_at`, `owedAt_shared_at`, `owedAt_second_at`   `owedAt` from `bud` at the run, and On at the run's
                                             own carried blocks, state and front, at the called parts alone

What is paid: that the book gives a called part its carried blocks and that `midAtW` | `midSharedAtW` returns a
state there. What is not: `bud` and On: these two premises are the rest of `owedAt`'s own text.
Premises: the description's test on its plan; the book's tests; the run has returned. Nothing on any property.
-/
import E2E.OfflineOwedFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc

variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X} {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {k : Coins Bk} {ρ : Draws} {r : RunC F}

/-- **`owedAt` at a list of the first chain comes to its `bud` at the run and its On at the run's own carried
blocks, state and front**, at the parts that the run has called. -/
theorem owedAt_first_at (plan : F.planOk = true) (book : Bk.word F = none)
    (h : runC F Bk (G.prover H) w₀ rc x k ρ = .ok r)
    {L : Lettered Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi} (hL : L ∈ G.first)
    (st : List (Nat × Nat × List UInt64))
    (hon : ∀ σ, L.side F.first.blocksInOrder = some σ → ∀ u ∈ σ.members,
      r.called ⟨L.place, u.number⟩ = true → ∀ ca m,
      carriedAt Bk k 0 ⟨L.place, u.number⟩ u.part = .ok ca →
      orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
      L.On u ca m (r.run.beforeAt st ⟨L.place, u.number⟩))
    (hbud : ∀ σ, L.side F.first.blocksInOrder = some σ → ∀ u ∈ σ.members,
      L.bud u.number (r.run.drawnAt ⟨L.place, u.number⟩) (r.run.askedAt ⟨L.place, u.number⟩)) :
    L.owedAt F.first.blocksInOrder k 0 (fun a => orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ a)) r.run st
      r.called := by
  intro σ hσ u hu
  refine ⟨hbud σ hσ u hu, fun hc => ?_⟩
  obtain ⟨ca, m, h1, h2⟩ := (first_part_at_run plan book h hL hσ hu).2.2 hc
  exact ⟨ca, m, h1, h2, hon σ hσ u hu hc ca m h1 h2⟩

/-- **Where the parts of the shared chain's lists stand, and that they are given their carried blocks**, of
what `ready` has prepared; and each list has one move for each round of its sub-protocol. -/
theorem shared_stands (plan : F.planOk = true) (book : Bk.word F = none)
    {R : Ready W₀ Rc Xi Ky Tr X₀ X} (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R) :
    ∀ L ∈ G.shared, ∀ σ, L.side F.shared.blocksInOrder = some σ →
      ((σ.row.map (·.1.moves.length)).sum = σ.block.rounds.length ∧
        σ.block.oracles.length = σ.block.rounds.length) ∧
      ∀ u ∈ σ.members,
        (∃ pre t, StandsAt F.shared.blocksInOrder R.shared σ u pre t (σ.roundsTo u.number)) ∧
          ∃ ca, carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca := by
  obtain ⟨ht, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  obtain ⟨t1, t2, t3⟩ := tests_twice ht
  obtain ⟨n1, n2, n3⟩ := places_nodup ((F.planOk_ok).1 plan).places
  have r1 : (G.shared.map (·.place)).Nodup := by
    have e := nodup_of_twice t2
    have e' : ((G.shared.map fun L => (⟨L.place, L.row.map (·.1)⟩ :
        Placed Empty (Common W₀ Rc Ky) X₀)).map (·.place)).Nodup := e
    rw [List.map_map] at e'
    exact e'
  exact stands_of_steps s2 n2 r1 (cuts_of book)

/-- **One part of a list of the shared chain, at a run that has returned.** No invariant is taken. -/
theorem shared_part_at_run (plan : F.planOk = true) (book : Bk.word F = none)
    (h : runC F Bk (G.prover H) w₀ rc x k ρ = .ok r)
    {L : Lettered Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky} (hL : L ∈ G.shared)
    {σ : Side F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
    (hσ : L.side F.shared.blocksInOrder = some σ) {u : Member Empty (Common W₀ Rc Ky) X₀ Ky}
    (hu : u ∈ σ.members) :
    ((σ.row.map (·.1.moves.length)).sum = σ.block.rounds.length ∧
      σ.block.oracles.length = σ.block.rounds.length) ∧
    (∃ pre t, F.shared.blocksInOrder = pre ++ σ.block :: t ∧
      r.run.drawnAt ⟨L.place, u.number⟩ =
        (ρ.shared.drop ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)).take
          u.rounds.length ∧
      r.run.askedAt ⟨L.place, u.number⟩ =
        asksFrom (treeAsks F ρ 1) (u.rounds.map (·.2.length))
          (((rowsOfChain F.shared.blocksInOrder).take
            ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)).map (·.2.length)).sum) ∧
      (r.called ⟨L.place, u.number⟩ = true → ∃ ca m,
        carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca ∧
        orRefused (midSharedAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m) := by
  obtain ⟨R, a₁, z₁, a₂, z₂, a₃, z₃, hR, -⟩ := runC_parts h
  have P := (F.planOk_ok).1 plan
  have hp := P.places
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 P.blocks₁
  have o₂ := steps_shaped s2 P.blocks₂
  have o₃ := steps_shaped s3 P.blocks₃
  obtain ⟨hnum, hst⟩ := shared_stands plan book hR L hL σ hσ
  obtain ⟨⟨pre, t, S⟩, ca, hca⟩ := hst u hu
  have hstr := S.str
  have hown := S.own
  rw [side_place hσ] at hstr
  obtain ⟨ha, htw, hfl, hseg⟩ := stretch_back hstr S.pos S.fits
  have hA := at_shared h hR o₁ o₂ o₃ hp ha
  refine ⟨hnum, ⟨pre, t, S.cut, drawnAt_of hA hstr, ?_⟩, fun hc => ?_⟩
  · rw [askedAt_of hA hstr (treeAsks F ρ 1) (runC_asks h hR o₁ o₂ o₃ 1)]
    have e1 : ((R.shared.drop ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)).take
        u.rounds.length).map (·.oracles.length) = u.rounds.map (·.2.length) := by
      have g := congrArg (List.map (·.2.length)) hown
      rw [List.map_map] at g
      exact g
    have e2 : (R.shared.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)).map
        (·.oracles.length) = ((rowsOfChain F.shared.blocksInOrder).take
          ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)).map (·.2.length) := by
      rw [← steps_pairs s2, ← List.map_take, List.map_map]
      rfl
    rw [e1, e2]
  · obtain ⟨m, hm, -⟩ := mid_shared h hR o₁ o₂ o₃ hp ha hseg hc
    exact ⟨ca, m, hca, orRefused_some hm⟩

/-- **`owedAt` at a list of the shared chain comes to its `bud` at the run and its On at the run's own carried
blocks, state and front**, at the parts that the run has called. -/
theorem owedAt_shared_at (plan : F.planOk = true) (book : Bk.word F = none)
    (h : runC F Bk (G.prover H) w₀ rc x k ρ = .ok r)
    {L : Lettered Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky} (hL : L ∈ G.shared)
    (st : List (Nat × Nat × List UInt64))
    (hon : ∀ σ, L.side F.shared.blocksInOrder = some σ → ∀ u ∈ σ.members,
      r.called ⟨L.place, u.number⟩ = true → ∀ ca m,
      carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca →
      orRefused (midSharedAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
      L.On u ca m (r.run.beforeAt st ⟨L.place, u.number⟩))
    (hbud : ∀ σ, L.side F.shared.blocksInOrder = some σ → ∀ u ∈ σ.members,
      L.bud u.number (r.run.drawnAt ⟨L.place, u.number⟩) (r.run.askedAt ⟨L.place, u.number⟩)) :
    L.owedAt F.shared.blocksInOrder k 1 (fun a => orRefused (midSharedAtW F Bk (G.prover H) w₀ rc x k ρ a)) r.run
      st r.called := by
  intro σ hσ u hu
  refine ⟨hbud σ hσ u hu, fun hc => ?_⟩
  obtain ⟨ca, m, h1, h2⟩ := (shared_part_at_run plan book h hL hσ hu).2.2 hc
  exact ⟨ca, m, h1, h2, hon σ hσ u hu hc ca m h1 h2⟩

/-- **Where the parts of the second chain's lists stand, and that they are given their carried blocks**, of
what `ready` has prepared; and each list has one move for each round of its sub-protocol. -/
theorem second_stands (plan : F.planOk = true) (book : Bk.word F = none)
    {R : Ready W₀ Rc Xi Ky Tr X₀ X} (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R) :
    ∀ L ∈ G.second, ∀ σ, L.side F.second.blocksInOrder = some σ →
      ((σ.row.map (·.1.moves.length)).sum = σ.block.rounds.length ∧
        σ.block.oracles.length = σ.block.rounds.length) ∧
      ∀ u ∈ σ.members,
        (∃ pre t, StandsAt F.second.blocksInOrder R.second σ u pre t (σ.roundsTo u.number)) ∧
          ∃ ca, carriedAt Bk k 2 ⟨L.place, u.number⟩ u.part = .ok ca := by
  obtain ⟨ht, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  obtain ⟨t1, t2, t3⟩ := tests_twice ht
  obtain ⟨n1, n2, n3⟩ := places_nodup ((F.planOk_ok).1 plan).places
  have r1 : (G.second.map (·.place)).Nodup := by
    have e := nodup_of_twice t3
    have e' : ((G.second.map fun L => (⟨L.place, L.row.map (·.1)⟩ :
        Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)).map (·.place)).Nodup := e
    rw [List.map_map] at e'
    exact e'
  exact stands_of_steps s3 n3 r1 (cuts_of book)

/-- **One part of a list of the second chain, at a run that has returned.** No invariant is taken. -/
theorem second_part_at_run (plan : F.planOk = true) (book : Bk.word F = none)
    (h : runC F Bk (G.prover H) w₀ rc x k ρ = .ok r)
    {L : Lettered Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi} (hL : L ∈ G.second)
    {σ : Side F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (hσ : L.side F.second.blocksInOrder = some σ) {u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (hu : u ∈ σ.members) :
    ((σ.row.map (·.1.moves.length)).sum = σ.block.rounds.length ∧
      σ.block.oracles.length = σ.block.rounds.length) ∧
    (∃ pre t, F.second.blocksInOrder = pre ++ σ.block :: t ∧
      r.run.drawnAt ⟨L.place, u.number⟩ =
        (ρ.second.drop ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)).take
          u.rounds.length ∧
      r.run.askedAt ⟨L.place, u.number⟩ =
        asksFrom (treeAsks F ρ 2) (u.rounds.map (·.2.length))
          (((rowsOfChain F.second.blocksInOrder).take
            ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)).map (·.2.length)).sum) ∧
      (r.called ⟨L.place, u.number⟩ = true → ∃ ca m,
        carriedAt Bk k 2 ⟨L.place, u.number⟩ u.part = .ok ca ∧
        orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m) := by
  obtain ⟨R, a₁, z₁, a₂, z₂, a₃, z₃, hR, -⟩ := runC_parts h
  have P := (F.planOk_ok).1 plan
  have hp := P.places
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 P.blocks₁
  have o₂ := steps_shaped s2 P.blocks₂
  have o₃ := steps_shaped s3 P.blocks₃
  obtain ⟨hnum, hst⟩ := second_stands plan book hR L hL σ hσ
  obtain ⟨⟨pre, t, S⟩, ca, hca⟩ := hst u hu
  have hstr := S.str
  have hown := S.own
  rw [side_place hσ] at hstr
  obtain ⟨ha, htw, hfl, hseg⟩ := stretch_back hstr S.pos S.fits
  have hA := at_second h hR o₁ o₂ o₃ hp ha
  refine ⟨hnum, ⟨pre, t, S.cut, drawnAt_of hA hstr, ?_⟩, fun hc => ?_⟩
  · rw [askedAt_of hA hstr (treeAsks F ρ 2) (runC_asks h hR o₁ o₂ o₃ 2)]
    have e1 : ((R.second.drop ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)).take
        u.rounds.length).map (·.oracles.length) = u.rounds.map (·.2.length) := by
      have g := congrArg (List.map (·.2.length)) hown
      rw [List.map_map] at g
      exact g
    have e2 : (R.second.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)).map
        (·.oracles.length) = ((rowsOfChain F.second.blocksInOrder).take
          ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)).map (·.2.length) := by
      rw [← steps_pairs s3, ← List.map_take, List.map_map]
      rfl
    rw [e1, e2]
  · obtain ⟨m, hm, -⟩ := mid_second h hR o₁ o₂ o₃ hp ha hseg hc
    exact ⟨ca, m, hca, orRefused_some hm⟩

/-- **`owedAt` at a list of the second chain comes to its `bud` at the run and its On at the run's own carried
blocks, state and front**, at the parts that the run has called. -/
theorem owedAt_second_at (plan : F.planOk = true) (book : Bk.word F = none)
    (h : runC F Bk (G.prover H) w₀ rc x k ρ = .ok r)
    {L : Lettered Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi} (hL : L ∈ G.second)
    (st : List (Nat × Nat × List UInt64))
    (hon : ∀ σ, L.side F.second.blocksInOrder = some σ → ∀ u ∈ σ.members,
      r.called ⟨L.place, u.number⟩ = true → ∀ ca m,
      carriedAt Bk k 2 ⟨L.place, u.number⟩ u.part = .ok ca →
      orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
      L.On u ca m (r.run.beforeAt st ⟨L.place, u.number⟩))
    (hbud : ∀ σ, L.side F.second.blocksInOrder = some σ → ∀ u ∈ σ.members,
      L.bud u.number (r.run.drawnAt ⟨L.place, u.number⟩) (r.run.askedAt ⟨L.place, u.number⟩)) :
    L.owedAt F.second.blocksInOrder k 2 (fun a => orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ a)) r.run
      st r.called := by
  intro σ hσ u hu
  refine ⟨hbud σ hσ u hu, fun hc => ?_⟩
  obtain ⟨ca, m, h1, h2⟩ := (second_part_at_run plan book h hL hσ hu).2.2 hc
  exact ⟨ca, m, h1, h2, hon σ hσ u hu hc ca m h1 h2⟩

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.owedAt_first_at
#print axioms AtPublicFiles.OfflineRows.shared_stands
#print axioms AtPublicFiles.OfflineRows.shared_part_at_run
#print axioms AtPublicFiles.OfflineRows.owedAt_shared_at
#print axioms AtPublicFiles.OfflineRows.second_stands
#print axioms AtPublicFiles.OfflineRows.second_part_at_run
#print axioms AtPublicFiles.OfflineRows.owedAt_second_at
