-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3Rides.lean: the kind "lookup" (K3) AT THE TABLE OF JOINTS: WHAT RIDES PAST
A SEATED LOOKUP: the kind's share of the kind-free rule (Johnson/Desc/Sound/RidesSide.lean): what a
yes of the kind's block leaves (SameBut, Johnson/Desc/First/Look/K3CallsTurns.lean) gives the rule's
nine equations; and, BY LEAN's OWN EVALUATION ON THE TABLE, who rides at the kind's places.
Definitions, statements and proofs. Ties: no error term. NO RESULT ON THE PROTOCOL.

OBJECT: no text that runs: the table of joints' own functions at the driver's own list of places.
USER: Johnson/Desc/First/Look/K3RidesCalls.lean, K3RidesDigR.lean, K3RidesR.lean.
LETTERS: in the evaluations: the small list of segments (layers, attention, layers, attention, head)
  and the full one (twelve pairs and the head), ps := flatPlaces true links true.
Compiled with the whole library.


Main names:
  `SameBut.sameOut`: SameBut gives SameOut: it has the nine and a tenth clause, on the sort of
    "here".
  `partlessAtB links m pc`: ridersPartless at the index's own number of the address (1, m, pc, K3).
  `plainSort`, `ridersPlain`, `plainAtB`: a sharper Bool: every rider is of one of five sorts: pile,
    pinI, pinW, constr, row.
  THE EVALUATIONS: `partless_small`, `partless_full`, `plain_small`, `plain_full`: yes at every
    lookup on the calls of both lists, the head's among them. CONTROLS: `partless_digits_small`,
    `plain_digits_small`: NO at every lookup on the digits of the small list; `digits_there_small`:
    these addresses are there.
  `readsOut_roots`, `readsOut_fails`: TWO TOYS: a sentence that is ReadsOut; one that is not.

Limits. The evaluations stand at two lists of segments: that a description's lists are these is not
said here. WHO RIDES AT THE DIGITS WITH A PART is not listed by Lean here.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.RidesSide
import Johnson.Desc.First.Look.K3CallsTurns
import Johnson.Desc.First.Look.K3RowIndex

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item start openSets rowOf flatPlaces borderAt SameOut
  ReadsOut)

/-- SameBut has the nine equations. -/
theorem SameBut.sameOut {s s' : First.S} (h : SameBut s s') : SameOut s s' :=
  ⟨h.st, h.book, h.roots, h.rowsOwed, h.failed, h.check, h.out, h.req, h.link⟩

/-! ## The Bool at the two lists of segments -/

/-- The Bool at the index's own number of the address of segment m's block at piece pc. -/
def partlessAtB (links : List ModelPart) (m pc : ℕ) : Bool :=
  ((borderAt (flatPlaces true links true) ⟨1, some m, pc, .K3⟩).map fun k =>
    ridersPartless links (flatPlaces true links true) k).getD false

/-- At every lookup on the calls of the small list, the head's among them. -/
theorem partless_small : ((List.range 4).all fun m => partlessAtB smallSubs m 2) = true ∧
    partlessAtB smallSubs 4 3 = true := by decide +kernel

/-- At every lookup on the calls of the full list, the head's among them. -/
theorem partless_full : ((List.range 24).all fun m => partlessAtB fullSubs m 2) = true ∧
    partlessAtB fullSubs 24 3 = true := by decide +kernel

/-- A CONTROL: at every lookup on the digits of the small list the Bool says no: forms ride
there. -/
theorem partless_digits_small : ((List.range 4).all fun m => !partlessAtB smallSubs m 7) = true ∧
    partlessAtB smallSubs 4 8 = false := by decide +kernel

/-- The address is there (else the control would say no for nothing). -/
theorem digits_there_small : ((List.range 4).all fun m =>
    (borderAt (flatPlaces true smallSubs true) ⟨1, some m, 7, .K3⟩).isSome) = true ∧
    (borderAt (flatPlaces true smallSubs true) ⟨1, some 4, 8, .K3⟩).isSome = true := by
  decide +kernel

/-- One of the five sorts. -/
def plainSort : Item → Bool
  | .pile => true
  | .pinI => true
  | .pinW => true
  | .constr _ _ => true
  | .row _ _ => true
  | _ => false

/-- Every item that is open in front of block k and that its row neither closes nor reads is of one
of the five sorts. -/
def ridersPlain (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  ((openSets links ps (start links))[k]?.getD []).all fun i =>
    (((ps[k]?.map (rowOf links)).getD {}).ins ++ ((ps[k]?.map (rowOf links)).getD {}).ctx ++
      [Item.unmarked]).contains i || plainSort i

def plainAtB (links : List ModelPart) (m pc : ℕ) : Bool :=
  ((borderAt (flatPlaces true links true) ⟨1, some m, pc, .K3⟩).map fun k =>
    ridersPlain links (flatPlaces true links true) k).getD false

theorem plain_small : ((List.range 4).all fun m => plainAtB smallSubs m 2) = true ∧
    plainAtB smallSubs 4 3 = true := by decide +kernel

theorem plain_full : ((List.range 24).all fun m => plainAtB fullSubs m 2) = true ∧
    plainAtB fullSubs 24 3 = true := by decide +kernel

/-- A CONTROL: at every lookup on the digits of the small list the sharper Bool says no too. -/
theorem plain_digits_small : ((List.range 4).all fun m => !plainAtB smallSubs m 7) = true ∧
    plainAtB smallSubs 4 8 = false := by decide +kernel

/-! ## Two toys -/

/-- A sentence that is ReadsOut: it reads the number of roots received. -/
theorem readsOut_roots (base n : ℕ) :
    ReadsOut (P := Unit) (W := Unit) base (fun a _ _ => a.2.roots = n) :=
  fun _ _ _ _ _ _ hS _ h => hS.roots.symm.trans h

/-- A sentence that is not: it reads the open link's ledger. -/
theorem readsOut_fails (s₀ : First.S) (a : First.LayOwn) (F : Fork) (hF : F ≠ a.F) (base : ℕ) :
    ¬ ReadsOut (P := Unit) (W := Unit) base (fun x _ _ => x.2.fork? = some F) := by
  intro h
  have h1 := h () { s₀ with here := .lay a } { s₀ with here := .lay { a with F := F } }
    ⟨fun _ => none, fun _ _ => []⟩ ⟨fun _ => none, fun _ _ => []⟩ ()
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨fun _ => rfl, fun _ _ _ => rfl⟩ rfl
  exact hF (Option.some.inj h1).symm

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.SameBut.sameOut
#print axioms VerifiableInference.OnPublicFiles.partless_small
#print axioms VerifiableInference.OnPublicFiles.partless_full
#print axioms VerifiableInference.OnPublicFiles.partless_digits_small
#print axioms VerifiableInference.OnPublicFiles.plain_small
#print axioms VerifiableInference.OnPublicFiles.plain_full
#print axioms VerifiableInference.OnPublicFiles.plain_digits_small
#print axioms VerifiableInference.OnPublicFiles.readsOut_roots
#print axioms VerifiableInference.OnPublicFiles.readsOut_fails
