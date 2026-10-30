-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/CloseLeaves.lean: WHAT K9's TWO MEMBERS WITHOUT A ROUND, "the one equation" AND "the
segment is shut", LEAVE OF THE STATE: drawn off their clauses `EqKeeps` and `ShutKeeps` (Honest/K9/CloseKeeps.lean),
which are equations on the whole state. Statements and proofs ON THE VERIFIER's TEXT; no prover is in this file, and
no goal is stated.
  `EqKeeps.own`, `ShutKeeps.own`   s'.own? = s.own?: what a feed-forward segment's own rounds returned (in it what the
      merge left) stays
  `EqKeeps.head`, `ShutKeeps.head`   ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ a'.x = a.x ∧ a'.t = a.t ∧
      a'.wo = a.wo
  `EqKeeps.out`, `ShutKeeps.out`   s'.out = s.out
No premise beside the clause. The small laws beneath: ours (Honest/K9/KeepsPaid.lean, YesAtSeat.lean) and the
library's `LinkJoin.putLink_own`, `S.out_putLink`. No member; called by no line.
WHAT IS NOT CLAIMED. Either clause at any pair of states. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.CloseKeeps
import Johnson.Desc.ProofFile.Honest.K9.KeepsPaid
import Johnson.Desc.First.StateOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

theorem EqKeeps.own {s s' : S} (H : EqKeeps s s') : s'.own? = s.own? := by
  obtain ⟨a, o, _, _, rfl⟩ := H.laid
  exact set_own s _

theorem EqKeeps.head {s s' : S} (H : EqKeeps s s') :
    ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ a'.x = a.x ∧ a'.t = a.t ∧ a'.wo = a.wo := by
  obtain ⟨a, o, _, _, rfl⟩ := H.laid
  exact head_form (set_headOf s _)

theorem EqKeeps.out {s s' : S} (H : EqKeeps s s') : s'.out = s.out := by
  obtain ⟨a, o, _, _, rfl⟩ := H.laid
  exact set_out s _

theorem ShutKeeps.own {s s' : S} (H : ShutKeeps s s') : s'.own? = s.own? := by
  obtain ⟨L, _, rfl⟩ := H.laid
  exact LinkJoin.putLink_own s _

theorem ShutKeeps.head {s s' : S} (H : ShutKeeps s s') :
    ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ a'.x = a.x ∧ a'.t = a.t ∧ a'.wo = a.wo := by
  obtain ⟨L, _, rfl⟩ := H.laid
  exact head_form (putLink_headOf s _)

theorem ShutKeeps.out {s s' : S} (H : ShutKeeps s s') : s'.out = s.out := by
  obtain ⟨L, _, rfl⟩ := H.laid
  exact S.out_putLink s _

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.EqKeeps.own
#print axioms ProofFile.Honest.K9.EqKeeps.head
#print axioms ProofFile.Honest.K9.EqKeeps.out
#print axioms ProofFile.Honest.K9.ShutKeeps.own
#print axioms ProofFile.Honest.K9.ShutKeeps.head
#print axioms ProofFile.Honest.K9.ShutKeeps.out
