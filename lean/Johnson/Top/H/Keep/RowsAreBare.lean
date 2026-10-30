-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Keep/RowsAreBare.lean: The kind "lookup" (K3): BEHIND AN ACCEPT OF ITS SUB-PROTOCOL,
WHAT ITS VERIFIER HAS HEARD IS THERE, AND EVERY ONE OF ITS KEPT ROWS IS Bare (it names no entry of
a virtual row: OnBytes/Tie/Pv/Led/LedRowsLook.lean): the form in which
Johnson/Top/H/Keep/FormsObjectsLink.lean, FormsTObjects.lean and FormsObjectsDigits.lean ask it.
Statements and proofs: the sister of Johnson/Top/H/Keep/RowsBare.lean, which says "has no entry".

OBJECT: K3.block's decide; the seat's reader of what was heard.
Used by Johnson/Desc/First/Look/K3DigitsBare.lean and Johnson/Desc/Sound/MgAt/K3CallsBareAt.lean.
LETTERS: seat (that reads back what it lays), piece, laid, before, p, guests, s, rs, cols free; F:
  the ledger in front.
Compiled with the whole library.

Main names:
  bare_of_ents: a form without an entry is Bare.
  decide_bare: at every seat that reads back what it lays.
  calls_bare, digits_bare: at the two seats.

Limits. ONE PREMISE ON THE VERIFIER's STATE IN FRONT: the open ledger has its sizes (Sized F).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.K3Named
import Johnson.Desc.First.Look.K3SeatLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun
open OnBytes.Road.Rows (Bare)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat SeatReads seatCalls seatDigits seatCalls_reads
  seatDigits_reads)

/-- A form without an entry is Bare. -/
theorem bare_of_ents {f : Aff} (h : f.ents = #[]) : Bare f := fun _ y hy => by
  rw [h] at hy
  simp at hy

/-- **Behind an accept the rows are Bare.** -/
theorem decide_bare {T Cl : Type} (seat : Seat T Cl) (hR : SeatReads seat) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest T Cl)) (s s' : T) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') {F : Fork}
    (hf : seat.fork s = some F) (hS : Sized F) :
    ∃ g, seat.heard s' = some g ∧ ∀ f ∈ g.rows.toList, Bare f := by
  obtain ⟨F0, x, hF0, hn, rfl, hP⟩ := decide_named seat piece laid before p guests s s' rs cols hd
  obtain rfl : F = F0 := Option.some.inj (hf.symm.trans hF0)
  exact ⟨x.1, hR s x.1 x.2 (by rw [hf]; rfl) hn, fun f hm => ((hP hS).rows f hm).1⟩

theorem calls_bare {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (seatCalls claim) piece laid before p guests).decide s rs cols = .ok s')
    {F : Fork} (hf : s.fork? = some F) (hS : Sized F) :
    ∃ g, (seatCalls claim).heard s' = some g ∧ ∀ f ∈ g.rows.toList, Bare f :=
  decide_bare (seatCalls claim) (seatCalls_reads claim) piece laid before p guests s s' rs cols hd
    hf hS

theorem digits_bare {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (seatDigits claim) piece laid before p guests).decide s rs cols = .ok s')
    {F : Fork} (hf : s.fork? = some F) (hS : Sized F) :
    ∃ g, (seatDigits claim).heard s' = some g ∧ ∀ f ∈ g.rows.toList, Bare f :=
  decide_bare (seatDigits claim) (seatDigits_reads claim) piece laid before p guests s s' rs cols
    hd hf hS

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.bare_of_ents
#print axioms VerifiableInference.OnPublicFiles.decide_bare
