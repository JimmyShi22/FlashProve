-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/FieldWalk.lean: `FieldAt` and `FieldFit` (Field.lean, FieldLaw.lean)
hold at the walk's own state in front of every sub-protocol that has a round, the chain's first too:
general in the chain, the list of sub-protocols, the steps and the challenges. `base` is what
`ChainProgress.start` was handed as `front`; `skip` is the number of challenges that the chain's start state
had heard; the available tables are `envOf` (Law/Cut.lean) at the rounds produced.

  `fieldAt_walk`   the statement

By what. `live_field` (K12/LiveField.lean, by the authors of that file): which columns the field
holds at a round, and that they are the filling of the earlier sub-protocols' reads.
`walk_heard_drop`, `walk_laid_length`, `start_laid` (WalkHeard.lean): the tie between the challenges
that the state has heard and those of the rounds produced. `envOf_tight` (Law/Along.lean).

Limits.
  * A conditional: nothing here shows that a walk returns, or that the prover's run is still played.
  * It speaks of `walk` from `ChainProgress.start`. That the state which `midAtW` returns (MidW.lean) is such
    a state, and so the statement `Tie2` (Ties.lean), is not proved here.
  * In front of a sub-protocol alone: before a later round of it `FieldFit` is false.
  * `hL`: the lay's trees are `envOf`'s; paid in `tie2` (Tie2File.lean).
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.WalkHeard
import Johnson.Desc.ProofFile.Honest.FieldLaw
import Johnson.Desc.ProofFile.Honest.K12.LiveField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn Place)

/-- **At the walk's own state in front of a sub-protocol that has a round.** `pre`: the
sub-protocols in front of `b`. The walk over just the rounds that `pre` declares has returned `z₁`,
and the prover's run is going on there, at the state `m`. -/
theorem fieldAt_walk {S Cl W Y : Type} (L : Lay) {taken : Nat → Nat → Option (Place × Table)}
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (pre : List (Block S Cl))
    (b : Block S Cl) (t : List (Block S Cl)) (hb : 0 < b.rounds.length) (m₀ : Mid W Y) (v₀ : S)
    (front : List OpenedColumn) {a z₁ : ChainProgress S Cl W Y} {ss₁ : List (Step W Y)} {ds₁ : List Fmt.Drawn}
    (ha : ChainProgress.start L (pre ++ b :: t) (some m₀) (some v₀) front = .ok a)
    (h1 : walk L ss₁ ds₁ a = .ok z₁) (hlen : ss₁.length = (pre.flatMap (·.rounds)).length)
    {m : Mid W Y} (hm : z₁.mid = some m) :
    FieldAt L.chain L.firstTree (pre.flatMap (·.rounds)) front m₀.st.heard.length m
        (envOf L.stored taken z₁.laid) ∧
      FieldFit (pre.flatMap (·.rounds)) m₀.st.heard.length m (envOf L.stored taken z₁.laid) := by
  obtain ⟨s, cols, -, -, -, -, hop, -, hfill⟩ :=
    K12.live_field L hL pre b t 0 hb m₀ v₀ front ha h1 (by rw [hlen, Nat.add_zero]) hm
  obtain ⟨hle, hdrop⟩ := walk_heard_drop ha h1 hm
  have hn : z₁.laid.length = (pre.flatMap (·.rounds)).length := by
    rw [walk_laid_length L ss₁ ds₁ a z₁ h1, start_laid ha, hlen]
    exact Nat.zero_add _
  have htake : z₁.laid.take (pre.flatMap (·.rounds)).length = z₁.laid :=
    List.take_of_length_le (Nat.le_of_eq hn)
  rw [htake, hL] at hfill
  refine ⟨⟨cols, ?_, hop⟩, hle, ?_, envOf_tight _ _ _⟩
  · rw [hdrop]
    exact hfill
  · rw [hdrop, List.length_map, hn]

end ProofFile.Honest

#print axioms ProofFile.Honest.fieldAt_walk
