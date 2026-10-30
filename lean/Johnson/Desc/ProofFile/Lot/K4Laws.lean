-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lot/K4Laws.lean: what the parameters of a place of K4's lot
(Johnson/Desc/ProofFile/Lot/K4.lean) are made of. Statements and proofs on the lot's own text.

  `k4From_par`: every member of k4From's list has the layers' public record of the segments' records
    (G.W.layers), a group g at which these records have a plan, that plan, piece 3, and the name
    and group of a layers' segment of the list.
  `k4Lot_par`: so for every block that the lot lays: it is k4Block of such a member.
Limits. Nothing on what G.W is (that it is the return of the routine that reads the public files is
not said here), on the field `before`, on `link`, or on the Bool. Nothing on soundness.


-/
import Johnson.Desc.ProofFile.Lot.K4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open OnBytes OnBytes.Model OnBytes.Model.Stages

/-- What the parameters of a place are made of. -/
theorem k4From_par (Z : Pub) (G : Ground) :
    ∀ (l : List LinkH) (n : Nat) (last : Option String) (x : Bool × OnBytes.Desc.First.K4.Par),
      x ∈ k4From Z G l n last →
      x.2.P = G.W.layers ∧ G.W.G[x.2.g]? = some x.2.hp ∧ x.2.piece = 3 ∧
        ∃ X ∈ l, X.kind = 0 ∧ x.2.g = X.g ∧ x.2.name = s!"{X.name}:3"
  | [], _, _, x, h => by simp [k4From] at h
  | X :: rest, n, last, x, h => by
    unfold k4From at h
    split at h
    · rename_i hk
      have hk0 : X.kind = 0 := by simpa using hk
      rcases List.mem_append.mp h with h1 | h2
      · split at h1
        · rename_i hp hg
          have e : x = _ := List.mem_singleton.mp h1
          subst e
          exact ⟨rfl, hg, rfl, X, List.mem_cons_self, hk0, rfl, rfl⟩
        · cases h1
      · obtain ⟨a, b, c, Y, hY, d⟩ := k4From_par Z G rest (n + 1) (some X.name) x h2
        exact ⟨a, b, c, Y, List.mem_cons_of_mem _ hY, d⟩
    · obtain ⟨a, b, c, Y, hY, d⟩ := k4From_par Z G rest (n + 1) last x h
      exact ⟨a, b, c, Y, List.mem_cons_of_mem _ hY, d⟩

/-- Every block that the lot lays is k4Block of such a member. -/
theorem k4Lot_par (Z : Pub) (G : Ground) (b : VerifiableInference.Desc.Block
    VerifiableInference.Desc.First.S Cl) (h : b ∈ (k4Lot Z).hearC G) :
    ∃ x : Bool × OnBytes.Desc.First.K4.Par, b = k4Block x ∧ x.2.P = G.W.layers ∧
      G.W.G[x.2.g]? = some x.2.hp ∧ x.2.piece = 3 ∧
      ∃ X ∈ G.built.toList, X.kind = 0 ∧ x.2.g = X.g ∧ x.2.name = s!"{X.name}:3" := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  exact ⟨x, rfl, k4From_par Z G _ _ _ x hx⟩

end ProofFile

#print axioms ProofFile.k4From_par
#print axioms ProofFile.k4Lot_par
