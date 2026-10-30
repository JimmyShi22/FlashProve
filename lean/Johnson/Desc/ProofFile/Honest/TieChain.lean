-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/TieChain.lean: `FieldAt` and `FieldFit` (Field.lean, FieldLaw.lean)
hold at the state that `midInW` (MidW.lean) returns before the first part of a sub-protocol that has
a round: one chain; general in the chain, the steps and the challenges. A step on the way to the
statement `Tie2` (Ties.lean).

  `fieldAt_midInW`   from the count of the rounds in front of the address
  `fieldAt_midInW_steps`   the same where the steps are what `chainSteps` returns: the count is paid
     by `chainSteps_front` (StepsFront.lean)
  `fieldAt_chain`   **the same with the available tables named as `Tie2` names them**: `envOf` at
     `roundsAhead` of the rounds that the walk over the whole chain has produced: by `laid_ahead`
     (WalkTake.lean)

By what: `fieldAt_walk` (FieldWalk.lean).

Limits.
  * One chain. `Tie2` speaks of `midAtW` and of a run of `runC`: what the run's parts and the three
    chains' starts are, and that the description's places differ, is not treated here.
  * Conditional: nothing shows that `midInW` returns a state.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.FieldWalk
import Johnson.Desc.ProofFile.Honest.MidW
import Johnson.Desc.ProofFile.Honest.StepsFront
import Johnson.Desc.ProofFile.Honest.WalkTake

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn Place)

/-- **At the state that `midInW` returns.** `hn`: the rounds in front of the address are as many as
the sub-protocols in front of `b` declare. -/
theorem fieldAt_midInW {S Cl W Y : Type} (L : Lay) {taken : Nat → Nat → Option (Place × Table)}
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (pre : List (Block S Cl))
    (b : Block S Cl) (t : List (Block S Cl)) (hb : 0 < b.rounds.length) (m₀ : Mid W Y) (v₀ : S)
    (front : List OpenedColumn) {a₀ : ChainProgress S Cl W Y} {steps : List (Step W Y)} {ds : List Fmt.Drawn}
    {a : Addr} (ha : ChainProgress.start L (pre ++ b :: t) (some m₀) (some v₀) front = .ok a₀)
    (hn : (steps.takeWhile fun s => s.addr != a).length = (pre.flatMap (·.rounds)).length)
    {m : Mid W Y} (hm : midInW L steps ds a₀ a = .ok (some m)) :
    ∃ z₁ : ChainProgress S Cl W Y,
      walk L (steps.take (pre.flatMap (·.rounds)).length)
        (ds.take (pre.flatMap (·.rounds)).length) a₀ = .ok z₁ ∧ z₁.mid = some m ∧
      FieldAt L.chain L.firstTree (pre.flatMap (·.rounds)) front m₀.st.heard.length m
        (envOf L.stored taken z₁.laid) ∧
      FieldFit (pre.flatMap (·.rounds)) m₀.st.heard.length m (envOf L.stored taken z₁.laid) := by
  unfold midInW at hm
  simp only [hn] at hm
  split at hm
  · cases hm
  · obtain ⟨z₁, h1, e⟩ := map_ok hm
    have hlen : (steps.take (pre.flatMap (·.rounds)).length).length =
        (pre.flatMap (·.rounds)).length := by
      have e : ((steps.takeWhile fun s => s.addr != a) ++
          steps.dropWhile fun s => s.addr != a).length = steps.length := by
        rw [List.takeWhile_append_dropWhile]
      rw [List.length_append] at e
      rw [List.length_take, ← hn]
      exact Nat.min_eq_left (by omega)
    obtain ⟨f1, f2⟩ := fieldAt_walk L hL pre b t hb m₀ v₀ front ha h1 hlen e
    exact ⟨z₁, h1, e, f1, f2⟩

/-- **The same where the steps are what `chainSteps` returns.** CONDITIONAL: no other sub-protocol
of the list stands at `b`'s place; a round stands at `⟨b.place, 0⟩`. -/
theorem fieldAt_midInW_steps {S Cl V W Y : Type} (L : Lay)
    {taken : Nat → Nat → Option (Place × Table)}
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (pre : List (Block S Cl))
    (b : Block S Cl) (t : List (Block S Cl)) (hb : 0 < b.rounds.length) (m₀ : Mid W Y) (v₀ : S)
    (front : List OpenedColumn) {a₀ : ChainProgress S Cl W Y} {steps : List (Step W Y)} {ds : List Fmt.Drawn}
    {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d} {v : Option V}
    {hs : List (Placed V W Y)}
    (hc : chainSteps B rows look v (pre ++ b :: t) hs = .ok steps)
    (hp : ∀ b' ∈ pre, b'.place ≠ b.place) (ht : ∀ b' ∈ t, b'.place ≠ b.place)
    (hany : steps.any (fun s => s.addr == ⟨b.place, 0⟩) = true)
    (ha : ChainProgress.start L (pre ++ b :: t) (some m₀) (some v₀) front = .ok a₀)
    {m : Mid W Y} (hm : midInW L steps ds a₀ ⟨b.place, 0⟩ = .ok (some m)) :
    ∃ z₁ : ChainProgress S Cl W Y,
      walk L (steps.take (pre.flatMap (·.rounds)).length)
        (ds.take (pre.flatMap (·.rounds)).length) a₀ = .ok z₁ ∧ z₁.mid = some m ∧
      FieldAt L.chain L.firstTree (pre.flatMap (·.rounds)) front m₀.st.heard.length m
        (envOf L.stored taken z₁.laid) ∧
      FieldFit (pre.flatMap (·.rounds)) m₀.st.heard.length m (envOf L.stored taken z₁.laid) :=
  fieldAt_midInW L hL pre b t hb m₀ v₀ front ha (chainSteps_front hc hp ht hany) hm

/-- **With the available tables named as `Tie2` names them.** `hw`: the walk over the whole chain
returns `z`. CONDITIONAL: as `fieldAt_midInW_steps`. -/
theorem fieldAt_chain {S Cl V W Y : Type} (L : Lay)
    {taken : Nat → Nat → Option (Place × Table)}
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (pre : List (Block S Cl))
    (b : Block S Cl) (t : List (Block S Cl)) (hb : 0 < b.rounds.length) (m₀ : Mid W Y) (v₀ : S)
    (front : List OpenedColumn) {a₀ z : ChainProgress S Cl W Y} {steps : List (Step W Y)} {ds : List Fmt.Drawn}
    {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d} {v : Option V}
    {hs : List (Placed V W Y)}
    (hc : chainSteps B rows look v (pre ++ b :: t) hs = .ok steps)
    (hp : ∀ b' ∈ pre, b'.place ≠ b.place) (ht : ∀ b' ∈ t, b'.place ≠ b.place)
    (hany : steps.any (fun s => s.addr == ⟨b.place, 0⟩) = true)
    (ha : ChainProgress.start L (pre ++ b :: t) (some m₀) (some v₀) front = .ok a₀)
    (hw : walk L steps ds a₀ = .ok z)
    {m : Mid W Y} (hm : midInW L steps ds a₀ ⟨b.place, 0⟩ = .ok (some m)) :
    FieldAt L.chain L.firstTree (pre.flatMap (·.rounds)) front m₀.st.heard.length m
        (envOf L.stored taken (roundsAhead z.laid b.place)) ∧
      FieldFit (pre.flatMap (·.rounds)) m₀.st.heard.length m
        (envOf L.stored taken (roundsAhead z.laid b.place)) := by
  obtain ⟨z₁, h1, -, f1, f2⟩ :=
    fieldAt_midInW_steps L hL pre b t hb m₀ v₀ front hc hp ht hany ha hm
  obtain ⟨l₁, s₀, l', rfl, hl, n1, e0, -⟩ := chainSteps_split hc hp ht hany
  rw [← hl] at h1
  rw [← laid_ahead (start_laid ha) hw h1 n1 (by rw [e0])]
  exact ⟨f1, f2⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.fieldAt_midInW
#print axioms ProofFile.Honest.fieldAt_midInW_steps
#print axioms ProofFile.Honest.fieldAt_chain
