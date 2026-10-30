-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/WorthAtS.lean: WHAT A FORM IS WORTH AT ANY STATE THAT GOES ON FROM q, AT
THE CARRIED RECORD: ITS VALUE IN THE WORLD THAT q's SNAPSHOT NAMES. Theorems: tools for whoever must
show that a caller's form has one worth, named by (q, y), at every later state.

Why. The lookups' runs of claims (Johnson/Desc/First/Look/K3Runs.lean: «planes», «join») take forms
from the calling kind. Their values are flat terms at the worths of these forms, read at a later
state. For the batching kind's premise on a run these worths must be functions of what was fixed
before the draw (q) and the data (y).

What is said.
  `worth_atS`: **at a state t that goes on from q (`Fx9 φ Ok q t`), with q's snapshot u: a form each
    of whose slots is filled in u's ledger, or lies in a window that is laid in t's ledger, is worth
    there what it is worth in `refWorld ρ u.F wins ent y`**
    (Johnson/Desc/First/Link/Law/K4Values.lean), if its entries of virtual rows are ent's.
    `worth_filled`: the case without a window. `worths_atS`: the like of a list of forms.

Limits. Tools. Which slots and entries a caller's forms name, that the snapshot has these slots
filled, and that the forms themselves are read off what was heard, is each calling kind's. Nothing
on soundness.

-/
import Johnson.Desc.First.Link.Law.K4Values
import Johnson.Desc.First.Batch.Law.FitsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.WorthAtS
open OnBytes OnBytes.Model
open OnBytes.PscRun (Later Filled)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K4Values (refWorld LaidAt value_ref)

variable {α K : Type} [CommRing K] (ρ : Reading K)

/-- A state that goes on from q holds a ledger later than the snapshot's. -/
theorem later_of_fx (φ : S → α) (Ok : α × Option Pub9 → Prop) (q : α × Option Pub9) (t : S)
    (b : K9.Part) (u : Pub9) (hf : Fx9 φ Ok q t) (hb : atS.get? t = some b) (hu : q.2 = some u) :
    Later u.F b.F := by
  obtain ⟨_, _, u', b', hu', hb', g⟩ := hf
  obtain rfl : u = u' := Option.some.inj (hu.symm.trans hu')
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  exact g.1

/-- **WHAT A FORM IS WORTH AT A STATE THAT GOES ON FROM q.** -/
theorem worth_atS (φ : S → α) (Ok : α × Option Pub9 → Prop) (q : α × Option Pub9) (t : S)
    (b : K9.Part) (u : Pub9) (hf : Fx9 φ Ok q t) (hb : atS.get? t = some b) (hu : q.2 = some u)
    (f : Aff) (wins : List (ℕ × ℕ)) (ent : ℕ → ℕ → ℕ → K) (y : Bound K)
    (hw : ∀ w ∈ wins, LaidAt b.F w)
    (hs : ∀ x ∈ f.slots.toList, (∃ w ∈ wins, K4Values.InWin w x.1) ∨ Filled u.F x.1)
    (he : ∀ x ∈ f.ents.toList, (worldAt ρ b.L b.F y).entry x.tree x.row x.idx =
      ent x.tree x.row x.idx) :
    f.value ρ (worldAt ρ b.L b.F y) = f.value ρ (refWorld ρ u.F wins ent y) :=
  value_ref ρ f b.L u.F b.F wins ent y (later_of_fx φ Ok q t b u hf hb hu) hw hs he

/-- The case without a window: every slot that the form names is filled in the snapshot. -/
theorem worth_filled (φ : S → α) (Ok : α × Option Pub9 → Prop) (q : α × Option Pub9) (t : S)
    (b : K9.Part) (u : Pub9) (hf : Fx9 φ Ok q t) (hb : atS.get? t = some b) (hu : q.2 = some u)
    (f : Aff) (ent : ℕ → ℕ → ℕ → K) (y : Bound K)
    (hs : ∀ x ∈ f.slots.toList, Filled u.F x.1)
    (he : ∀ x ∈ f.ents.toList, (worldAt ρ b.L b.F y).entry x.tree x.row x.idx =
      ent x.tree x.row x.idx) :
    f.value ρ (worldAt ρ b.L b.F y) = f.value ρ (refWorld ρ u.F [] ent y) :=
  worth_atS ρ φ Ok q t b u hf hb hu f [] ent y (fun _ h => absurd h List.not_mem_nil)
    (fun x hx => Or.inr (hs x hx)) he

/-- The like of a list of forms. -/
theorem worths_atS (φ : S → α) (Ok : α × Option Pub9 → Prop) (q : α × Option Pub9) (t : S)
    (b : K9.Part) (u : Pub9) (hf : Fx9 φ Ok q t) (hb : atS.get? t = some b) (hu : q.2 = some u)
    (fs : List Aff) (wins : List (ℕ × ℕ)) (ent : ℕ → ℕ → ℕ → K) (y : Bound K)
    (hw : ∀ w ∈ wins, LaidAt b.F w)
    (hs : ∀ f ∈ fs, ∀ x ∈ f.slots.toList, (∃ w ∈ wins, K4Values.InWin w x.1) ∨ Filled u.F x.1)
    (he : ∀ f ∈ fs, ∀ x ∈ f.ents.toList, (worldAt ρ b.L b.F y).entry x.tree x.row x.idx =
      ent x.tree x.row x.idx) :
    fs.map (fun f => f.value ρ (worldAt ρ b.L b.F y)) =
      fs.map fun f => f.value ρ (refWorld ρ u.F wins ent y) :=
  List.map_congr_left fun f hf' =>
    worth_atS ρ φ Ok q t b u hf hb hu f wins ent y hw (hs f hf') (he f hf')

end VerifiableInference.Desc.WorthAtS

#print axioms VerifiableInference.Desc.WorthAtS.later_of_fx
#print axioms VerifiableInference.Desc.WorthAtS.worth_atS
#print axioms VerifiableInference.Desc.WorthAtS.worth_filled
#print axioms VerifiableInference.Desc.WorthAtS.worths_atS
