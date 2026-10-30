-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/WorldsMeet.lean: TWO WORLDS MEET: the world in which the kinds' laws say
a plain run's values (`refWorld`, K4Values.lean, with the entries `entUnit`, EntryUnit.lean) and the
world in which the table of conditions says a run's forms (`worldOwn`,
Johnson/Desc/Sound/FormsQ.lean) give a form one worth, wherever the form names only what is there.
Theorems: one bridge for all kinds.

Why. `TableOwes.hitems` (LinkTable.lean) asks, an item of the table at a time, that some runs'
values are the worths of the reader's forms in the table's world. A kind's law has these values in
its own world: under a slot of a window the mask row's entry, under another slot what the ledger in
front of the draw holds; the entries of virtual rows as the arrays' own cells, by the snapshot's
list. The table's world has: under a late slot what the run will lay; elsewhere the ledger's; row r
of an array as the array's own row r, and 0 at an array that is not named.

What is said.
  `ent_meets`: at an array that the list names the two have one entry. `slot_meets`: under a slot
    the two have one value, if a window's slot is late with (shown 0, factor −1), and another slot
    is not late. `value_meets`: **so a form has one worth in both**, if that holds of each slot and
    each entry that it names. `value_meets_still`: the case of a run without a window and a reader
    without a late slot.

Limits. Tools. That a reader's late slots are a run's windows, and that its forms are the forms of
the law, is each kind's to show. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.K4Values
import Johnson.Desc.First.Link.Law.EntryUnit
import Johnson.Desc.Sound.FormsQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K4Values (refWorld InWin)
open VerifiableInference.Desc.EntryUnit (entUnit)

variable {α : Type}

/-- At an array that the list names the two worlds have one entry. -/
theorem ent_meets (a : K9.Part) (late : List (ℕ × E × E)) (y : Bound GQ) (q : α × Option Pub9)
    (hq : q.2 = some (pubOf a)) (t r i : ℕ) (x : ℕ × String) (hx : a.L.arrayOf[t]? = some x) :
    entUnit q y t r i = (worldOwn a late y).entry t r i := by
  have e : (pubOf a).arrayOf.getD t (0, "") = x := by
    show a.L.arrayOf.getD t (0, "") = x
    rw [Array.getD_eq_getD_getElem?, hx]
    rfl
  show (match q.2 with
    | some u => y.cell (u.arrayOf.getD t (0, "")).1 (u.arrayOf.getD t (0, "")).2 r i
    | none => 0) = (match a.L.arrayOf[t]? with
    | some b => y.cell b.1 b.2 r i
    | none => 0)
  rw [hq, hx]
  show y.cell ((pubOf a).arrayOf.getD t (0, "")).1 ((pubOf a).arrayOf.getD t (0, "")).2 r i = _
  rw [e]

/-- Under a slot the two worlds have one value. -/
theorem slot_meets (U : Fork) (wins : List (ℕ × ℕ)) (ent : ℕ → ℕ → ℕ → GQ)
    (late : List (ℕ × E × E)) (y : Bound GQ) (j : ℕ)
    (hw : (∃ w ∈ wins, InWin w j) → K9.lateAt late j = some (zeroE, subE zeroE oneE))
    (hn : (¬ ∃ w ∈ wins, InWin w j) → K9.lateAt late j = none) :
    (refWorld Reading.gl U wins ent y).slot j = slotW U late y.mask j := by
  show (if ∃ w ∈ wins, InWin w j then y.mask j
    else Reading.gl.val (U.vp.getD j zeroE) - Reading.gl.val (U.mf.getD j zeroE) * y.mask j) = _
  by_cases h : ∃ w ∈ wins, InWin w j
  · rw [if_pos h, slotW_late U late y.mask j _ (hw h)]
    show y.mask j = Reading.gl.val zeroE - Reading.gl.val (subE zeroE oneE) * y.mask j
    rw [Reading.gl.sub, Reading.gl.zero, Reading.gl.one]
    ring
  · rw [if_neg h, slotW_ledger U late y.mask j (hn h)]

/-- **A form has one worth in both worlds.** -/
theorem value_meets (a : K9.Part) (wins : List (ℕ × ℕ)) (late : List (ℕ × E × E)) (y : Bound GQ)
    (q : α × Option Pub9) (hq : q.2 = some (pubOf a)) (f : Aff)
    (he : ∀ x ∈ f.ents.toList, (a.L.arrayOf[x.tree]?).isSome = true)
    (hw : ∀ x ∈ f.slots.toList, (∃ w ∈ wins, InWin w x.1) →
      K9.lateAt late x.1 = some (zeroE, subE zeroE oneE))
    (hn : ∀ x ∈ f.slots.toList, (¬ ∃ w ∈ wins, InWin w x.1) → K9.lateAt late x.1 = none) :
    f.value Reading.gl (refWorld Reading.gl a.F wins (entUnit q y) y) =
      f.value Reading.gl (worldOwn a late y) := by
  refine value_eq _ _ f (fun x hx => ?_) fun x hx => ?_
  · obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (he x hx)
    exact ent_meets a late y q hq x.tree x.row x.idx z hz
  · exact slot_meets a.F wins _ late y x.1 (hw x hx) (hn x hx)

/-- The case of a run without a window and a reader without a late slot. -/
theorem value_meets_still (a : K9.Part) (y : Bound GQ) (q : α × Option Pub9)
    (hq : q.2 = some (pubOf a)) (f : Aff)
    (he : ∀ x ∈ f.ents.toList, (a.L.arrayOf[x.tree]?).isSome = true) :
    f.value Reading.gl (refWorld Reading.gl a.F [] (entUnit q y) y) =
      f.value Reading.gl (worldOwn a [] y) :=
  value_meets a [] [] y q hq f he (fun _ _ h => by obtain ⟨_, hw, _⟩ := h; exact nomatch hw)
    fun _ _ _ => rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.ent_meets
#print axioms VerifiableInference.Desc.LinkJoin.slot_meets
#print axioms VerifiableInference.Desc.LinkJoin.value_meets
#print axioms VerifiableInference.Desc.LinkJoin.value_meets_still
