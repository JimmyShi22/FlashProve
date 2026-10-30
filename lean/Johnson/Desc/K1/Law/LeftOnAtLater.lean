-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- A copy of a working file of this project, K1/Law/LeftOnAtLater.lean [not in this library]: as copied, it parted from it in import lines and in one called name (commitAtS_fork -> commitAtS_forkSlots).
/-
Johnson/Desc/K1/Law/LeftOnAtLater.lean: the sentence of the public item `leftOn m`
(`k3LeftOnItemAt`, Johnson/Desc/First/Look/K3LeftItem.lean) goes over a yes of a segment's later
moment (`commitAtS`), and over a step that leaves four readers of the state (`LookSame`,
Johnson/Desc/K1/Law/LookSame.lean). Both by that file's own `leftOn_stays`.

Main names: `sized_of_ledgerB`; `leftOn_at_later`; `leftOn_quiet`.

What is not claimed. One premise is on the state in front: the Bool `ledgerB`
(Johnson/Desc/First/FillKeeper.lean), which is the public item `ledger m` at the composed meaning.
Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.First.Look.K3LeftItem
import Johnson.Desc.First.FillKeeper
import Johnson.Desc.K1.Law.PubAtLaterLook
import Johnson.Desc.K1.Law.LookSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S ledgerB)
open VerifiableInference.OnPublicFiles (k3LeftOnItemAt k3LeftOnItem leftOn_stays)

variable {Cl : Type}

/-- The Bool's yes: the open ledger's three arrays have the ledger's size. -/
theorem sized_of_ledgerB {s : S} {F : Fork} (hF : s.fork? = some F) (h : ledgerB s = true) :
    PscRun.Sized F := by
  unfold ledgerB at h
  rw [hF] at h
  simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- A ledger with the same slots is a later state, and has its sizes. -/
theorem later_of_slots {F F' : Fork} (h : PscRun.SlotsSame F F') (hS : PscRun.Sized F) :
    _root_.Fo.Later F F' ∧ PscRun.Sized F' := by
  refine ⟨⟨Nat.le_of_eq h.next.symm, h.ns, fun j hj => ?_⟩, ?_⟩
  · unfold PscRun.Filled at *
    rw [h.vp, h.mf, h.gotF]
    exact ⟨hj, rfl, rfl⟩
  · unfold PscRun.Sized at *
    rw [h.ns, h.vp, h.mf, h.gotF]
    exact hS

/-- **`leftOn m` over a yes of a segment's later moment.** -/
theorem leftOn_at_later (X : Verify.Public) (m : Nat) (P : Par) (link moment : Nat)
    (arrays : Option (List Nat)) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s')
    (hz : ledgerB s = true) (h0 : k3LeftOnItemAt X m s) : k3LeftOnItemAt X m s' := by
  obtain ⟨F, F', a, b, hs⟩ := commitAtS_forkSlots P link moment arrays s s' rs gs h
  obtain ⟨hl, hz'⟩ := later_of_slots hs (sized_of_ledgerB a hz)
  have hh : s'.lookHeard? = s.lookHeard? := by
    obtain ⟨_, _, F₁, w, _, _, e⟩ := commitAtS_rec P link moment arrays s s' rs gs h
    rw [e, lookHeard_put]
  obtain ⟨p, hp, L⟩ := h0
  exact ⟨p, hp, leftOn_stays hh a b hl hz' L⟩

/-- **`leftOn m` over a step that leaves the four readers.** -/
theorem leftOn_quiet (X : Verify.Public) (m : Nat) {s s' : S} (h : LookSame s s')
    (hz : ledgerB s = true) (h0 : k3LeftOnItemAt X m s) : k3LeftOnItemAt X m s' := by
  have hF : ∃ F, s.fork? = some F := by
    unfold ledgerB at hz
    cases e : s.fork? with
    | none => rw [e] at hz; cases hz
    | some F => exact ⟨F, rfl⟩
  obtain ⟨F, a⟩ := hF
  obtain ⟨p, hp, L⟩ := h0
  exact ⟨p, hp, leftOn_stays h.look a (h.fork.trans a) (_root_.Fo.Later.refl F)
    (sized_of_ledgerB a hz) L⟩

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.leftOn_at_later
#print axioms VerifiableInference.Desc.K1.leftOn_quiet
