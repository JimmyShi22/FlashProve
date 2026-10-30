-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Keep/RowsBare.lean: The kind "lookup" (K3): BEHIND A YES OF ITS BLOCK, WHAT WAS HEARD
IS THERE, AND NONE OF ITS KEPT ROWS NAMES AN ENTRY OF AN ARRAY. Statements and proofs: one step
from Johnson/Top/H/Keep/K3Named.lean's decide_named.

OBJECT: K3.block's and K3.Law.blockVia's decide; the seat's reader of what was heard.
Used by Johnson/Desc/First/Look/K03RowsBare.lean and Johnson/P4R/BareAt341.lean.
LETTERS: seat (that reads back what it lays), piece, laid, before, p, guests, s, rs, cols free; F:
  the ledger in front.
Compiled with the whole library.

Main names:
  decide_rowsBare: at every seat that reads back what it lays.
  calls_rowsBare, digits_rowsBare: at the two seats that run.
  via_rowsBare: the like of blockVia's decide, under its test on the plan.
  calls_rowsBareB: at a layers' link, as one Bool on the record behind, written out: what the lookup
    on the calls left as heard is there, and none of its rows has an entry.

Limits. ONE PREMISE ON THE RECORD IN FRONT: the open ledger has its sizes (Sized F): decide_named
asks it. At decide: for the seated piece see Johnson/Desc/First/Look/K3CallsStatedYes.lean, which
carries its yes to K3.block's decide at the same record.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.K3Named
import Johnson.Top.H.K3Via.Blocks
import Johnson.Desc.First.Look.K3SeatLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat SeatReads seatCalls seatDigits seatCalls_reads
  seatDigits_reads)
open _root_.Fo.Tp (bare_ents)

/-- **Behind a yes the rows are bare.** -/
theorem decide_rowsBare {T Cl : Type} (seat : Seat T Cl) (hR : SeatReads seat) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest T Cl)) (s s' : T) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') {F : Fork}
    (hf : seat.fork s = some F) (hS : Sized F) :
    ∃ g, seat.heard s' = some g ∧ ∀ f ∈ g.rows.toList, f.ents = #[] := by
  obtain ⟨F0, x, hF0, hn, rfl, hP⟩ := decide_named seat piece laid before p guests s s' rs cols hd
  obtain rfl : F = F0 := Option.some.inj (hf.symm.trans hF0)
  exact ⟨x.1, hR s x.1 x.2 (by rw [hf]; rfl) hn, fun f hm => bare_ents ((hP hS).rows f hm).1⟩

theorem calls_rowsBare {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (seatCalls claim) piece laid before p guests).decide s rs cols = .ok s')
    {F : Fork} (hf : s.fork? = some F) (hS : Sized F) :
    ∃ g, s'.lookHeard? = some g ∧ ∀ f ∈ g.rows.toList, f.ents = #[] :=
  decide_rowsBare (seatCalls claim) (seatCalls_reads claim) piece laid before p guests s s' rs cols
    hd hf hS

theorem digits_rowsBare {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (seatDigits claim) piece laid before p guests).decide s rs cols = .ok s')
    {F : Fork} (hf : s.fork? = some F) (hS : Sized F) :
    ∃ g, s'.tl?.bind (·.heard) = some g ∧ ∀ f ∈ g.rows.toList, f.ents = #[] :=
  decide_rowsBare (seatDigits claim) (seatDigits_reads claim) piece laid before p guests s s' rs
    cols hd hf hS

/-- The like of the block that hears on a view's rounds, under its test on the plan. -/
theorem via_rowsBare {T Cl : Type} (seat : Seat T Cl) (hR : SeatReads seat) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest T Cl)) (s s' : T) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64)))
    (hplan : (Desc.K3.Law.blockVia seat piece laid before p guests).planOk = true)
    (hd : (Desc.K3.Law.blockVia seat piece laid before p guests).decide s rs cols = .ok s')
    {F : Fork} (hf : seat.fork s = some F) (hS : Sized F) :
    ∃ g, seat.heard s' = some g ∧ ∀ f ∈ g.rows.toList, f.ents = #[] :=
  decide_rowsBare seat hR piece laid before p guests s s' rs cols
    (Desc.K3.Law.blockVia_decide hplan hd) hf hS

/-- **At a layers' link, as one Bool on the record behind.** -/
theorem calls_rowsBareB {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (seatCalls claim) piece laid before p guests).decide s rs cols = .ok s')
    {F : Fork} (hf : s.fork? = some F) (hS : Sized F) {a' : Desc.First.LayOwn}
    (hlay : s'.here = .lay a') :
    (match s'.here with
      | .lay a => a.lookHeard.any fun g => g.rows.toList.all fun f => f.ents.isEmpty
      | _ => false) = true := by
  obtain ⟨g, hg, hb⟩ := calls_rowsBare claim piece laid before p guests s s' rs cols hd hf hS
  have hg' : a'.lookHeard = some g := by
    unfold S.lookHeard? at hg
    rw [hlay] at hg
    exact hg
  rw [hlay]
  show (a'.lookHeard.any fun g => g.rows.toList.all fun f => f.ents.isEmpty) = true
  rw [hg']
  show (g.rows.toList.all fun f => f.ents.isEmpty) = true
  refine List.all_eq_true.2 fun f hm => ?_
  rw [hb f hm]
  rfl

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.decide_rowsBare
#print axioms VerifiableInference.OnPublicFiles.via_rowsBare
#print axioms VerifiableInference.OnPublicFiles.calls_rowsBareB
