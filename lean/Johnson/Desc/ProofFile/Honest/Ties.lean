-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Ties.lean: three texts say what the field `opened` holds: the
hypothesis of `Good.exact` on the field (Side.lean), `FieldAt` (Field.lean), and what the walk lays
(`ChainProgress.start`, `ChainProgress.settle`, Walk.lean). Here the two statements that would tie them at a run of
`runC`, as propositions. Definitions only: nothing is proved in this file. `Tie2`
is a theorem: `tie2` (Tie2File.lean). No statement of this library concludes
`Tie1`.

  `takenOf`, `roundsAhead`   the look-up of a tree that the second chain takes over; a chain's
     played rounds before a place
  `Tie1`   at the state that the walk has before a part, the field is what `Good.exact`'s
     hypothesis says of it at the run's own `front`
  `Tie2`   at the state that the walk has before the first part of a place, `FieldAt` and `FieldFit`
     hold, at the available tables of the run (`envOf`, Law/Cut.lean)

The letters, chain by chain. `base`: nothing in the first and the shared chain; in the second chain
the columns of the run's first two views. `skip`: 0; in the second chain the number of the first two
chains' challenges. The available tables: `envOf` at the chain's played rounds before the place; in
the second chain with the trees that it takes over from the first two.

Both statements follow texts written out in this project's review.
Those texts gave the available tables as a term by hand; here they are `envOf`, the definition by
which this folder's laws on a walk's columns speak.

Limits.
  * No statement of this library concludes `Tie1`. It does not say that a run returns, that a state
    is returned, or that the state is the one through which `runC`'s own walk goes. With the
    `Before` written out, and under hypotheses of their own, the equations of its three clauses are
    theorems: `tie_first`, `tie_shared`, `tie_second_at` (Honest/Law/Rule/OpenedRun.lean).
  * `Tie2` speaks of the first part of a place alone: before a later part the state has heard
    challenges of the place's own rounds, and `FieldFit` is false there; of a place whose first part
    has no round it says nothing.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Owed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription Place OpenedColumn)

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- The look-up of a tree that the second chain takes over from the first chain (0) or the shared
chain (1): the text of `envOf_tree` (Law/Cut.lean). -/
def takenOf (l₁ l₂ : List Played) : Nat → Nat → Option (Place × Table) :=
  fun ch k => if ch == 0 then ((tablesOf l₁)[k]?).bind id
    else if ch == 1 then ((tablesOf l₂)[k]?).bind id else none

/-- A chain's played rounds before a place; all of them if none stands at the place. -/
def roundsAhead (l : List Played) (p : Place) : List Played := l.takeWhile fun q => q.place != p

/-- **Stated, not proved: no statement of this library concludes it.** What it says: at a run of
`runC` that returns, at an address at which a round was produced, the field of the state that
`midAtW` or `midSharedAtW` returns is what `Good.exact`'s hypothesis says of it at the run's own
`front`, chain by chain. With the `Before` written out, and under hypotheses of their own, the
equations of its three clauses are theorems: `tie_first`, `tie_shared`, `tie_second_at`
(Honest/Law/Rule/OpenedRun.lean). At `Run.beforeAt`, as here, no statement of this library concludes
one of them; the proofs of `on₁`, `on₂`, `on₃` (Honest/Law/Rule/OnFile.lean) derive each inside. -/
def Tie1 (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) : Prop :=
  ∀ w₀ rc x (c : Coins B) ρ r, runC F B H w₀ rc x c ρ = .ok r → ∀ a : Addr,
    let fr := r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) a
    (r.run.played.1.any (·.isAt a) = true → ∀ m, midAtW F B H w₀ rc x c ρ a = .ok (some m) →
      m.opened = fr.opened (readsBefore (preOf 0 0 (earlierOf F 0) F.first.blocksInOrder a.place) fr)) ∧
    (r.run.played.2.1.any (·.isAt a) = true →
      ∀ m, midSharedAtW F B H w₀ rc x c ρ a = .ok (some m) →
      m.opened = fr.opened (readsBefore (preOf 1 0 (earlierOf F 1) F.shared.blocksInOrder a.place) fr)) ∧
    (r.run.played.2.2.any (·.isAt a) = true → ∀ m, midAtW F B H w₀ rc x c ρ a = .ok (some m) →
      m.opened =
        fr.opened (readsBefore (preOf 2 F.lastChainFirstTreeNumber (earlierOf F 2) F.second.blocksInOrder a.place) fr))

/-- **A STATEMENT: `FieldAt` and `FieldFit` hold at the walk's own state before the first part of a
place**, chain by chain, at the run's own letters. Its proof: `tie2` (Tie2File.lean). -/
def Tie2 (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) : Prop :=
  ∀ w₀ rc x (c : Coins B) ρ r, runC F B H w₀ rc x c ρ = .ok r → ∀ p : Place,
    (r.run.played.1.any (·.isAt ⟨p, 0⟩) = true →
      ∀ m, midAtW F B H w₀ rc x c ρ ⟨p, 0⟩ = .ok (some m) →
      let E := envOf (H.storedWords w₀ rc) (fun _ _ => none) (roundsAhead r.run.played.1 p)
      FieldAt 0 0 (roundsBefore F.first.blocksInOrder p) [] 0 m E ∧
        FieldFit (roundsBefore F.first.blocksInOrder p) 0 m E) ∧
    (r.run.played.2.1.any (·.isAt ⟨p, 0⟩) = true →
      ∀ m, midSharedAtW F B H w₀ rc x c ρ ⟨p, 0⟩ = .ok (some m) →
      let E := envOf (H.storedWords w₀ rc) (fun _ _ => none) (roundsAhead r.run.played.2.1 p)
      FieldAt 1 0 (roundsBefore F.shared.blocksInOrder p) [] 0 m E ∧
        FieldFit (roundsBefore F.shared.blocksInOrder p) 0 m E) ∧
    (r.run.played.2.2.any (·.isAt ⟨p, 0⟩) = true →
      ∀ m, midAtW F B H w₀ rc x c ρ ⟨p, 0⟩ = .ok (some m) →
      let E := envOf (H.storedWords w₀ rc) (takenOf r.run.played.1 r.run.played.2.1)
        (roundsAhead r.run.played.2.2 p)
      FieldAt 2 F.lastChainFirstTreeNumber (roundsBefore F.second.blocksInOrder p)
          (r.run.views.1.opened ++ r.run.views.2.1.opened) (ρ.first.length + ρ.shared.length) m
          E ∧
        FieldFit (roundsBefore F.second.blocksInOrder p) (ρ.first.length + ρ.shared.length) m E)

end ProofFile.Honest

#print axioms ProofFile.Honest.takenOf
#print axioms ProofFile.Honest.roundsAhead
#print axioms ProofFile.Honest.Tie1
#print axioms ProofFile.Honest.Tie2
