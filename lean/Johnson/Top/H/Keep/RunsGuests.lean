-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Keep/RunsGuests.lean: The kind "lookup" (K3): ITS SECOND RUN OF CLAIMS, "guests",
WHERE NO GUEST IS HANDED IN: it returns the record as it is, with no claim; so it meets the
batching kind's premise on a run (PlainOk, RunOk) AT ALL LETTERS, WITHOUT A PREMISE. Definitions,
statements and proofs.

OBJECT: the second entry of the field claims of K3.block (Johnson/Desc/First/Look/K3Lookup.lean:238-240)
  and of K3.Law.blockVia (Johnson/Desc/First/Look/Via/Via.lean), at guests := []: as K3.theOwn lays
  them (Johnson/Desc/First/Look/K3Own.lean:82).
Used by Johnson/Top/H/Keep/RunsStated.lean.
LETTERS: phi, Ok, Fu free; seat, piece, laid, before, p free; guests := [].
Compiled with the whole library.
IS IT EMPTY: the conclusion is a "for all" over records that go on from a fixed part which meets Ok:
  where Ok is met nowhere it says nothing; it asks nothing of its own.

Main names:
  block_guests, blockVia_guests: guestsRun guests (Johnson/Top/H/Keep/K3Block.lean: the run, as the
    block states it) is the blocks' second run, to the letter: by rfl.
  guestsRun_nil: without a guest it returns ([], s).
  more9_refl: a record goes on from itself.
  guests_plainOk, guests_runOk.

Limits. At guests := [] alone: with a guest the claims are left to the guest's kind's files.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.RunsPlain
import Johnson.Top.H.Keep.K3Block
import Johnson.Desc.First.Look.Via.Via

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun _root_.Fo
open VerifiableInference.Desc (named)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L (PlainOk RunOk plainTm runOk_of_plain Pub9 Fx9 O9 more9
  goesOn_refl part_of_more)

/-- It is the second run of claims of the kind's block, to the letter. -/
theorem block_guests {S' Cl : Type} (seat : Seat S' Cl) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest S' Cl)) :
    (Desc.K3.block seat piece laid before p guests).claims[1]? =
      some ("guests", guestsRun guests) := rfl

theorem blockVia_guests {S' Cl : Type} (seat : Seat S' Cl) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest S' Cl)) :
    (Desc.K3.Law.blockVia seat piece laid before p guests).claims[1]? =
      some ("guests", guestsRun guests) := rfl

/-- Without a guest: no claim, and the record as it is. -/
theorem guestsRun_nil {S' Cl : Type} (n : ℕ) (s : S') :
    guestsRun ([] : List (Desc.First.Look.Guest S' Cl)) n s = .ok ([], s) := rfl

variable {α : Type} (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)

/-- A record goes on from itself. -/
theorem more9_refl (e : S) : more9 φ e e := ⟨rfl, fun a ha => ⟨a, ha, goesOn_refl a⟩⟩

/-- **"guests" without a guest meets the premise on a run of plain claims: no premise.** -/
theorem guests_plainOk :
    PlainOk Reading.gl atS (O9 (K := GE) φ Ok Fu) (Fx9 φ Ok)
      (guestsRun ([] : List (Desc.First.Look.Guest S Desc.Claim))) (fun _ _ => [])
      (fun _ => 0) := by
  intro q front e a c e₁ hf hg ha _ hr
  obtain ⟨rfl, rfl⟩ : [] = c ∧ e = e₁ := by
    have := Except.ok.inj ((guestsRun_nil (Cl := Desc.Claim) front e).symm.trans hr)
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  exact ⟨a, ha, rfl, rfl, hg, more9_refl φ e, hf, rfl, fun _ h => absurd h List.not_mem_nil,
    fun _ _ _ _ _ _ => rfl⟩

theorem guests_runOk :
    RunOk Reading.gl atS (O9 (K := GE) φ Ok Fu) (Fx9 φ Ok)
      (guestsRun ([] : List (Desc.First.Look.Guest S Desc.Claim))) (plainTm fun _ _ => [])
      (fun _ => 0) :=
  runOk_of_plain Reading.gl atS _ _ _ _ _ (fun e t a ha hm => part_of_more φ e t a ha hm)
    (guests_plainOk φ Ok Fu)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.blockVia_guests
#print axioms VerifiableInference.OnPublicFiles.guests_plainOk
#print axioms VerifiableInference.OnPublicFiles.guests_runOk
