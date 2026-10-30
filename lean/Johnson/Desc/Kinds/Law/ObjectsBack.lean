-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ObjectsBack.lean: A NAMED PREMISE ON THE IOP AS WRITTEN IN LEAN: the way back
of ObjectsStates (Johnson/Desc/Kinds/Law/ObjectsStates.lean): an accept of the run
K9.objectsCalls is an accept of what sub-protocol number b of a segment states under "objects", and
an accept of K9.guestsNone of what it states under "guests". A definition and three small theorems.
Light imports, no Mathlib.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  ObjectsBack states b: the premise. On the pattern of PlanesBack
      (Johnson/Desc/Kinds/Law/SilentAll.lean).
  objectsCalls_putFork: an accept of K9.objectsCalls turns the verifier's state by laying a ledger
      alone. guestsNone_same: an accept of K9.guestsNone leaves the state.
  objectsBack_block: the premise holds where that sub-protocol's runs are those of the lookup's own
      K3.block at the calls, with no guest.

Every letter under "there is": in objectsCalls_putFork: G: pinned by its equation.
What it does not say. That the IOP's own segment meets the premise. WHERE NOTHING IS STATED UNDER A
NAME THE PREMISE'S HALF FOR THAT NAME IS FREE: it is meant to stand beside ObjectsStates, which says
that both names are stated. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.ObjectsStates

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (RunOf)

/-- **A NAMED PREMISE**, the way back of ObjectsStates. -/
def ObjectsBack (states : Nat → List (RunOf S)) (b : Nat) : Prop :=
  (∀ run, (states b).find? (fun r => r.1 == "objects") = some ("objects", run) →
    ∀ k t y, K9.objectsCalls k t = .ok y → run k t = .ok y) ∧
  ∀ run, (states b).find? (fun r => r.1 == "guests") = some ("guests", run) →
    ∀ k t y, K9.guestsNone k t = .ok y → run k t = .ok y

/-- An accept of the run "objects" turns the state by laying a ledger alone. -/
theorem objectsCalls_putFork (k : Nat) (t : S) (y : List Claim × S)
    (h : K9.objectsCalls k t = .ok y) : ∃ G, y.2 = t.putFork G := by
  unfold K9.objectsCalls K9.objectsBy at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals (cases h; try exact ⟨_, rfl⟩)

/-- An accept of the run "guests" leaves the state. -/
theorem guestsNone_same (k : Nat) (t : S) (y : List Claim × S)
    (h : K9.guestsNone k t = .ok y) : y.2 = t := by
  cases h
  rfl

/-- The premise holds where the runs are those of the lookup's own sub-protocol at the calls, with
no guest. -/
theorem objectsBack_block (piece : Nat) (laid : Array Nat) (before : List (Nat × Nat))
    (p : First.Look.P) (states : Nat → List (RunOf S)) (b : Nat)
    (h : states b = (K3.block (K3.seatCalls fun a => ({ form := a } : Claim)) piece laid before p
      []).claims) : ObjectsBack states b := by
  refine ⟨fun run hr k t y hy => ?_, fun run hr k t y hy => ?_⟩
  · rw [h] at hr
    obtain rfl : K9.objectsCalls = run := congrArg Prod.snd (Option.some.inj hr)
    exact hy
  · rw [h] at hr
    obtain rfl : K9.guestsNone = run := congrArg Prod.snd (Option.some.inj hr)
    exact hy

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.objectsCalls_putFork
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.guestsNone_same
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.objectsBack_block
