-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/JoinState.lean: CONDITIONAL: THE LOOKUP's RUN "join", WHICH STANDS IN THE
BLOCK OF AN ATTENTION SEGMENT's OWN ROUNDS (kind K5), AT A STATE WITH `HeldLive`
(Johnson/Desc/K5/Honest/Law/LiveState.lean); and that such a state stands in a segment without a
merge. On the verifier's own runs; no prover in it. Of the kind's own three runs ("first", "keys",
"second") LiveState.lean has the like: `runs_unturned` (they return the state unturned),
`first_state`, `keys_state`, `second_state`.

Why. Whoever joins the kinds' clauses into one proposition on states asks of each run in a segment's
order: which fields it writes; that it hands the proposition on; that each claim that names a slot
takes its own number; and that the state goes on standing in a segment without a merge.

Main names:
  `join_state`: **the run "join"** (the text is the lookup's, Johnson/Desc/First/Look/K3Runs.lean;
    it stands in this kind's block): its one claim takes its own number; it writes the ledger
    alone, and hands `HeldLive` on. What a yes of that run is made of: the library's `join_heard`
    (Johnson/Top/H/Keep/K3Inv.lean) and `joinRun_cut` (Johnson/Top/H/K3RunsLaw.lean), called.
  `held_att`, `held_merge`: a state with `HeldLive` stands in an attention segment; there the
    merge's slot is none (the library's `merge_none_of_heard5`, Johnson/P5J/K03MergeAttAt.lean).

Limits. Nothing on which slots "join"'s claim names or with which coefficients: no slot of this
kind's own window needs it. `join_state` is conditional on `HeldLive` and on the run's yes; the
other two on `HeldLive` alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.LiveState
import Johnson.Desc.First.Att.Claims.WalkK5
import Johnson.Desc.First.Att.K05JoinRunN
import Johnson.P5J.K03MergeAttAt
import Johnson.Top.H.K3RunsLaw
import Johnson.Top.H.Keep.K3Inv

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes.Model (Aff)
open VerifiableInference.Desc (Claim First.S)
open VerifiableInference.Desc.K9H (plainAt)
open VerifiableInference.Desc.First.Att.P (parCOf)

variable {x : OnBytes.Params.AttentionRounds} {k : ℕ}

/-- **The run "join" at a state**: its one claim takes its own number; it hands the proposition on.
keys: the caller's key forms: any. Conditional: hI; hr: the run's yes. -/
theorem join_state (keys : First.S → Option (Array Aff)) (m : ℕ) (u : First.S)
    (z : List Claim × First.S) (hI : HeldLive x k u)
    (hr : VerifiableInference.Desc.K3.joinRun
      (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm) keys m u = .ok z) :
    (∀ j, plainAt z.1 j = true) ∧ HeldLive x k z.2 := by
  obtain ⟨cl, u'⟩ := z
  obtain ⟨F, g, e1, e2⟩ := VerifiableInference.OnPublicFiles.join_heard _ keys hr
  obtain ⟨KF, _, _, rfl, rfl⟩ := VerifiableInference.OnPublicFiles.joinRun_cut _ keys e1 e2 hr
  exact ⟨fun j => plainAt_forms [_] j, heldLive_congr (K5Law.heard5_putFork u _) hI⟩

/-- A state with the proposition stands in an attention segment. -/
theorem held_att {u : First.S} (hI : HeldLive x k u) : ∃ a, u.here = .att a := by
  obtain ⟨h5, _, _, _, _, _, e, _⟩ := hI
  unfold First.S.heard5? at e
  cases hh : u.here with
  | att a => exact ⟨a, rfl⟩
  | _ =>
    rw [hh] at e
    cases e

/-- There the merge's slot is none: the library's `merge_none_of_heard5`, called. -/
theorem held_merge {u : First.S} (hI : HeldLive x k u) :
    VerifiableInference.Desc.K9.mergeOf u = none := by
  obtain ⟨h5, _, _, _, _, _, e, _⟩ := hI
  exact P5J.merge_none_of_heard5 e

end H2K5.Honest

#print axioms H2K5.Honest.join_state
#print axioms H2K5.Honest.held_att
#print axioms H2K5.Honest.held_merge
