-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/TablesNotYetCalls.lean.
WHAT IT DOES NOT SHOW. No soundness. It speaks of the lookup's own sub-protocol at the calls' seat
(Desc.K3.block (Desc.K3.seatCalls claim) ...), not of the one that the IOP as written in Lean holds
at the head's link's third place: that the two accept alike is not shown here. The chain of four
places is not put together here.
WORDS. "The verifier's state": the value of type S that the sub-protocols hand on. "No tables are
laid" (Law/TablesNotYet.lean: NoTables): the state stands in the head's link, and the field t of the
link's own part, the table of the tables of reads, is none.
LETTERS. No "there is" but NoTables' own, pinned by the state.
OBJECT. The lookup on a link's calls, and what it changes in the verifier's state where it accepts
(Desc/First/Look/K3CallsTurnsSharp.lean: TurnsCalls: the ledger, what the lookup returned, and
"heard": and no other field of the open link's own part).
USER. Whoever says that no tables are laid at the border in front of the output head's own rounds:
of the four places between the entry of the head's link and that border this is the third.
WHAT IT IS. THE LOOKUP ON THE CALLS KEEPS "NO TABLES ARE LAID".
  turns_noTables    from TurnsCalls.
  calls_noTables    where the lookup's sub-protocol at the calls' seat accepts.
THE OTHER THREE PLACES: the first (made and kept) and the fourth (kept): Law/TablesNotYet.lean · the
second (kept): Top/H0/Tw/K2C/HeadRest.lean: placeH2_noTables.
A search (statements that name NoTables, its test, TurnsCalls or ".t = none",
over the table of joints' files, the seats' files, the code switching's files and K6's and K7's
files, in versions other than these: 1,042 files): none for this place.

-/
import Johnson.Desc.Kinds.Law.TablesNotYet
import Johnson.Desc.First.Look.K3CallsTurnsSharp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.OnPublicFiles (TurnsCalls k3_calls_turns)

/-- From what the lookup on the calls changes. -/
theorem turns_noTables {s s' : S} (h : TurnsCalls s s') (Z : NoTables s) : NoTables s' := by
  obtain ⟨o, ho, ht⟩ := Z
  rcases h.part with ⟨a, _, _, ha, _⟩ | ⟨a, _, _, ha, _⟩ | ⟨a, F, g, ha, _, x', hs'⟩
  · rw [ho] at ha
    cases ha
  · rw [ho] at ha
    cases ha
  · rw [ho] at ha
    cases ha
    exact ⟨_, hs', ht⟩

/-- **THE LOOKUP ON THE CALLS KEEPS "NO TABLES ARE LAID".** -/
theorem calls_noTables {Cl : Type} (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest S Cl)) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List (List (Nat × List UInt64)))
    (h : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (Z : NoTables s) : NoTables s' :=
  turns_noTables (k3_calls_turns claim piece laid before p guests s s' rs cols h) Z

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.turns_noTables
#print axioms VerifiableInference.Desc.Kinds.Head.Law.calls_noTables
