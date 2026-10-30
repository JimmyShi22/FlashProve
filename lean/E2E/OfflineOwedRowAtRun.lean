-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOwedRowAtRun.lean: ONE ROW's SHARE OF THE FIELD owed, FROM ITS On AT THE RUN: what `Lettered.owedAt`
(Johnson/Desc/ProofFile/Honest/Rule.lean) asks of one list at a run of `runC` that has returned, from that list's bound on
positions in closed form and from `OnAtRun₁`, `OnAtRun₂` or `OnAtRun₃` (Honest/Law/OwedAtRun.lean) at that list alone. The
steps are those of `owed_at_run` there, which asks both of every list at once. General in the description, the book, the
prover and the lists.

  `owedAt_first_of_onAtRun`, `owedAt_shared_of_onAtRun`, `owedAt_second_of_onAtRun`   the three chains

Premises: the description's test on its plan; the book's tests; the challenges are due; no stop is met; `ready` and `runC`
have returned; one member T of `ThreadsP`, which stands in `OnAtRun`'s type; at the last chain `PlanServes`. That the parts
stand and are given their carried blocks is paid (`first_stands`, `shared_stands`, `second_stands`). Nothing on any
property.
-/
import E2E.OfflineOwedChains
import Johnson.Desc.ProofFile.Honest.Law.OwedAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc

variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X} {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ X} {r : RunC F}

/-- **One list of the first chain.** -/
theorem owedAt_first_of_onAtRun (plan : F.planOk = true) (book : Bk.word F = none)
    (hρ : ρ.due F = true) (hsil : silentAt F (G.prover H) w₀ rc x ρ = none)
    (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R)
    (h : runC F Bk (G.prover H) w₀ rc x k ρ = .ok r)
    (T : ThreadsP F Bk (G.prover H) w₀ rc x k R)
    {L : Lettered Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi} (hL : L ∈ G.first)
    (hbud : ∀ σ, L.side F.first.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
      F.first.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number →
      L.bud u.number ((ρ.first.drop n).take u.rounds.length)
        (asksFrom (treeAsks F ρ 0) (u.rounds.map (·.2.length))
          (((rowsOfChain F.first.blocksInOrder).take n).map (·.2.length)).sum))
    (hon : OnAtRun₁ T ρ r L) :
    L.owedAt F.first.blocksInOrder k 0 (fun a => orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ a)) r.run
      (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called := by
  intro σ hσ u hu
  obtain ⟨⟨pre, t, S⟩, hl⟩ := (first_stands plan book hR L hL σ hσ).2 u hu
  have A := owed_part_first (L := L.atRun r.called
      (fun a => orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ a))
      (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked)))
    h hR plan hρ hsil T (side_place hσ) S rfl hl (hbud σ hσ u hu pre t _ S.cut rfl)
    (fun m ca hin hs hca hc hm hf => hon σ hσ u hu pre t S.cut m ca hin hs hca hc hm hf)
  refine ⟨A.1, fun hc => ?_⟩
  obtain ⟨ca, m, h₁, h₂, h₃⟩ := A.2 hc
  exact ⟨ca, m, h₁, h₂, h₃ hc h₂ rfl⟩

/-- **One list of the shared chain.** -/
theorem owedAt_shared_of_onAtRun (plan : F.planOk = true) (book : Bk.word F = none)
    (hρ : ρ.due F = true) (hsil : silentAt F (G.prover H) w₀ rc x ρ = none)
    (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R)
    (h : runC F Bk (G.prover H) w₀ rc x k ρ = .ok r)
    (T : ThreadsP F Bk (G.prover H) w₀ rc x k R)
    {L : Lettered Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky} (hL : L ∈ G.shared)
    (hbud : ∀ σ, L.side F.shared.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
      F.shared.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number →
      L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
        (asksFrom (treeAsks F ρ 1) (u.rounds.map (·.2.length))
          (((rowsOfChain F.shared.blocksInOrder).take n).map (·.2.length)).sum))
    (hon : OnAtRun₂ T ρ r L) :
    L.owedAt F.shared.blocksInOrder k 1
      (fun a => orRefused (midSharedAtW F Bk (G.prover H) w₀ rc x k ρ a)) r.run
      (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called := by
  intro σ hσ u hu
  obtain ⟨⟨pre, t, S⟩, hl⟩ := (shared_stands plan book hR L hL σ hσ).2 u hu
  have A := owed_part_shared (L := L.atRun r.called
      (fun a => orRefused (midSharedAtW F Bk (G.prover H) w₀ rc x k ρ a))
      (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked)))
    h hR plan hρ hsil T (side_place hσ) S rfl hl (hbud σ hσ u hu pre t _ S.cut rfl)
    (fun m ca hin hs hca hc hm hf => hon σ hσ u hu pre t S.cut m ca hin hs hca hc hm hf)
  refine ⟨A.1, fun hc => ?_⟩
  obtain ⟨ca, m, h₁, h₂, h₃⟩ := A.2 hc
  exact ⟨ca, m, h₁, h₂, h₃ hc h₂ rfl⟩

/-- **One list of the last chain.** -/
theorem owedAt_second_of_onAtRun (plan : F.planOk = true) (book : Bk.word F = none)
    (hρ : ρ.due F = true) (hsil : silentAt F (G.prover H) w₀ rc x ρ = none)
    (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R)
    (h : runC F Bk (G.prover H) w₀ rc x k ρ = .ok r) (hP : PlanServes (G.prover H) w₀ rc R)
    (T : ThreadsP F Bk (G.prover H) w₀ rc x k R)
    {L : Lettered Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi} (hL : L ∈ G.second)
    (hbud : ∀ σ, L.side F.second.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
      F.second.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number →
      L.bud u.number ((ρ.second.drop n).take u.rounds.length)
        (asksFrom (treeAsks F ρ 2) (u.rounds.map (·.2.length))
          (((rowsOfChain F.second.blocksInOrder).take n).map (·.2.length)).sum))
    (hon : OnAtRun₃ T ρ r L) :
    L.owedAt F.second.blocksInOrder k 2 (fun a => orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ a)) r.run
      (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called := by
  intro σ hσ u hu
  obtain ⟨⟨pre, t, S⟩, hl⟩ := (second_stands plan book hR L hL σ hσ).2 u hu
  have A := owed_part_second (L := L.atRun r.called
      (fun a => orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ a))
      (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked)))
    h hR plan hρ hsil hP T (side_place hσ) S rfl hl (hbud σ hσ u hu pre t _ S.cut rfl)
    (fun m ca hin hs hca hc hm hf => hon σ hσ u hu pre t S.cut m ca hin hs hca hc hm hf)
  refine ⟨A.1, fun hc => ?_⟩
  obtain ⟨ca, m, h₁, h₂, h₃⟩ := A.2 hc
  exact ⟨ca, m, h₁, h₂, h₃ hc h₂ rfl⟩

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.owedAt_first_of_onAtRun
#print axioms AtPublicFiles.OfflineRows.owedAt_shared_of_onAtRun
#print axioms AtPublicFiles.OfflineRows.owedAt_second_of_onAtRun
