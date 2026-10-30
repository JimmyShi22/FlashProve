-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/RunsStated.lean: The kind "lookup" (K3): WHICH RUNS OF CLAIMS THE SEATED BLOCK
STATES: the value of K3.theStated at an address (Johnson/Desc/First/Look/K3Stated.lean) states, in
this order, "objects": objectsRun at the seat of the calls or of the digits; "guests": guestsRun [];
and behind them nothing, or one run more. So what a link's gatherer finds there under the name
"guests" is the run without a guest, and under "objects" the run of Johnson/Top/H/K3RunsLaw.lean.
Statements and proofs: a peeling of four makers' texts.

OBJECT: K3.theStated claim readers X codes shape a's value: its field claims.
USER: nobody yet (the link's law's duty at each run of a link).
LETTERS: claim, readers, X, codes, shape, a, B free.
Compiled with the whole library.

Main names:
  Two seat l: the list l begins with the two runs, at that seat.
  theOwn_two, theWhole_two, theStated_two: of the three makers' values.
  theStated_guests, theStated_objects: what List.lookup, as the gatherer calls it
    (Johnson/Desc/Block.lean: claimsInStep), finds under the two names.
  theStated_guests_runOk: so the run that is found under "guests" meets the batching kind's premise
    on a run, at all letters.

Limits. Where theStated gives no block it says nothing. Which seat it is (by the address's piece) is
not said. Of the run behind the two ("planes") nothing.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.RunsGuests
import Johnson.Desc.First.Look.K3Stated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L (RunOk plainTm Pub9 Fx9 O9)

variable {Cl : Type}

/-- A named run of claims, as a block states it. -/
abbrev RunN (Cl : Type) : Type := String × (ℕ → S → Except String (List Cl × S))

/-- The list begins with "objects" and "guests", at one of the two seats. -/
def Two (claim : Aff → Cl) (l : List (RunN Cl)) : Prop :=
  ∃ seat tail, (seat = seatCalls claim ∨ seat = seatDigits claim) ∧
    l = ("objects", objectsRun seat) ::
      ("guests", guestsRun ([] : List (Desc.First.Look.Guest S Cl))) :: tail

theorem Two.more {claim : Aff → Cl} {l : List (RunN Cl)} (h : Two claim l) (t : List (RunN Cl)) :
    Two claim (l ++ t) := by
  obtain ⟨seat, tail, hs, rfl⟩ := h
  exact ⟨seat, tail ++ t, hs, rfl⟩

theorem theOwn_two (claim : Aff → Cl) (X : Model.Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Place) (x : Block S Cl)
    (h : Desc.K3.theOwn claim true X codes shape a = some x) : Two claim x.claims := by
  unfold Desc.K3.theOwn at h
  split at h
  · exact nomatch h
  · obtain ⟨i, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · exact nomatch h
    · rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, _, h⟩ := h
      repeat (rw [Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h)
      rw [Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      cases digits
      · exact ⟨seatCalls claim, [], Or.inl rfl, rfl⟩
      · exact ⟨seatDigits claim, [], Or.inr rfl, rfl⟩

theorem theWhole_two (claim : Aff → Cl) (X : Model.Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Place) (x : Block S Cl)
    (h : Desc.K3.theWhole claim true X codes shape a = some x) : Two claim x.claims := by
  unfold Desc.K3.theWhole at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  have h0 := theOwn_two claim X codes shape a b hb
  split
  · exact h0.more []
  · exact h0

theorem theStated_two (claim : Aff → Cl) (readers : ℕ → Option (Desc.K3.Readers S))
    (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (B : Block S Cl) (h : Desc.K3.theStated claim readers X codes shape a = some B) :
    Two claim B.claims := by
  unfold Desc.K3.theStated at h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.1 h
  have h0 := theWhole_two claim X codes shape a b hb
  split at h
  · obtain rfl := Option.some.inj h
    exact h0
  · split at h
    · obtain rfl := Option.some.inj h
      exact h0
    · split at h
      · obtain rfl := Option.some.inj h
        exact h0
      · obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
        exact h0.more _

/-- **What the gatherer finds under "guests".** -/
theorem theStated_guests (claim : Aff → Cl) (readers : ℕ → Option (Desc.K3.Readers S))
    (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (B : Block S Cl) (h : Desc.K3.theStated claim readers X codes shape a = some B) :
    B.claims.lookup "guests" =
      some (guestsRun ([] : List (Desc.First.Look.Guest S Cl))) := by
  obtain ⟨seat, tail, _, e⟩ := theStated_two claim readers X codes shape a B h
  rw [e]
  simp [List.lookup]

/-- **What it finds under "objects".** -/
theorem theStated_objects (claim : Aff → Cl) (readers : ℕ → Option (Desc.K3.Readers S))
    (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (B : Block S Cl) (h : Desc.K3.theStated claim readers X codes shape a = some B) :
    ∃ seat, (seat = seatCalls claim ∨ seat = seatDigits claim) ∧
      B.claims.lookup "objects" = some (objectsRun seat) := by
  obtain ⟨seat, tail, hs, e⟩ := theStated_two claim readers X codes shape a B h
  refine ⟨seat, hs, ?_⟩
  rw [e]
  simp [List.lookup]

/-- **So the seated block's run "guests" meets the premise on a run, at all letters.** -/
theorem theStated_guests_runOk {α : Type} (φ : S → α) (Ok : α × Option Pub9 → Prop)
    (Fu : S → Prop) (claim : Aff → Desc.Claim) (readers : ℕ → Option (Desc.K3.Readers S))
    (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (B : Block S Desc.Claim) (h : Desc.K3.theStated claim readers X codes shape a = some B)
    (run : ℕ → S → Except String (List Desc.Claim × S))
    (hr : B.claims.lookup "guests" = some run) :
    RunOk Reading.gl atS (O9 (K := GE) φ Ok Fu) (Fx9 φ Ok) run (plainTm fun _ _ => [])
      (fun _ => 0) := by
  obtain rfl := Option.some.inj
    ((theStated_guests claim readers X codes shape a B h).symm.trans hr)
  exact guests_runOk φ Ok Fu

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.theStated_two
#print axioms VerifiableInference.OnPublicFiles.theStated_guests
#print axioms VerifiableInference.OnPublicFiles.theStated_objects
#print axioms VerifiableInference.OnPublicFiles.theStated_guests_runOk
