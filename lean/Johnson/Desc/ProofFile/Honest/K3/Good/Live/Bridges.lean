-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Live/Bridges.lean: the kind "lookup" (K3): from three ways in
which the library says which slots a form names to the hypotheses on the calling kind's forms of
Honest/K3/Good/Live/Runs.lean and Unnamed.lean; and two of these hypotheses shown at the readers of
an attention link. Theorems.

Terms. Honest/K3/GLOSSARY.md ("form", "slot", "caller"). In this file: `Clear a j`
(Honest/K3/Good/Live/Pure.lean) says that the form a names slot j in no pair. The three ways: the
form's array of slots is empty; `SlotsIn lo hi a` (Johnson/Desc/Kinds/Law/SlotsFilled.lean): every
slot that it names is from lo on and below hi; `SlotsIn P a` (Johnson/Road/K4/Slots/SlotsIn.lean):
every slot that it names has the property P. The two are different definitions, in different files
and namespaces, under one short name: `VerifiableInference.Desc.Kinds.Head.Law.SlotsIn` takes two
numbers, `OnBytes.Desc.First.K4.Slots.SlotsIn` a predicate. Both are written with their full names
below.

What is shown.
  `clear_of_none`, `clear_of_slotsIn`, `clear_of_pred`: `Clear a j` from each of the three.
  `bitsClear_of_none`, `pinsClear_of_none`: readers all of whose forms at a state have no slots meet
    `BitsClear` and `PinsClear` there, at every slot.
  `bitsClear_of_slotsIn`, `pinsClear_of_slotsIn`: readers all of whose forms name slots from lo on
    and below hi alone meet them at every slot outside.
  `keysClear_of_none`, `keysClear_of_slotsIn`: the like of `KeysClear`.
  `at_clear`, `readersK_clear`: a form that the attention kind's reader of a table returns names no
    slot; so that kind's readers of the planes' matrix (`readersOfK`,
    Johnson/Desc/First/Att/Guest.lean) meet `BitsClear` and `PinsClear` at every seat, state and
    slot.
  `bitsClear_att`, `pinsClear_att`: the two hypotheses at an attention link's own readers
    (`readersOfO A`, Johnson/Desc/First/Att/SeatO.lean), at every plan A, state and slot. No
    hypothesis is left.

Hypotheses that remain. Each of the first nine theorems assumes the fact on the caller's forms in
one of the three ways (`h`; with it `hj`: slot j lies outside, or lacks the property). `at_clear`
assumes that the reader returns the form (`h`). The last three assume nothing.

How the proof goes. The library's `sv_u3at` (Johnson/Desc/First/Att/Claims/SlotsCovered.lean) says
of the form that the reader of a table returns that all its slots have any property whatever; taken
at the property "is not j". The library's `readers_forms`
(Johnson/Desc/First/Att/K05ReadersThere.lean) says the like with a statement on entries beside it,
under two hypotheses that the slots' half does not need.


Limits. The first nine are implications between ways of saying one thing. Of the library's callers
the readers of an attention link alone are treated: nothing on that link's key forms, which do name
slots; nothing on the head's link. That the lookups' lot hands "planes" these readers at link 2 g +
1 is the library's `readersAt_att` (Johnson/Desc/First/Att/Door/Law/K5RestOpen.lean), not called
here.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Unnamed
import Johnson.Desc.Kinds.Law.SlotsFilled
import Johnson.Road.K4.Slots.SlotsIn
import Johnson.Desc.First.Att.K05ReadersThere
import Johnson.Desc.First.Att.SeatO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good.Live
open OnBytes.Model (Aff)
open VerifiableInference.Desc.K3 (Readers)

/-! ## One form -/

/-- A form whose array of slots is empty names no slot. -/
theorem clear_of_none {a : Aff} (h : a.slots = #[]) (j : Nat) : Clear a j := by
  intro x hx
  rw [h] at hx
  simp at hx

/-- A form that names slots from lo on and below hi alone names no slot outside. -/
theorem clear_of_slotsIn {lo hi : Nat} {a : Aff}
    (h : VerifiableInference.Desc.Kinds.Head.Law.SlotsIn lo hi a) {j : Nat}
    (hj : j < lo ∨ hi ≤ j) : Clear a j := by
  intro x hx
  have := h x hx
  omega

/-- A form all of whose slots have a property names no slot that lacks it. -/
theorem clear_of_pred {P : Nat → Prop} {a : Aff} (h : OnBytes.Desc.First.K4.Slots.SlotsIn P a)
    {j : Nat} (hj : ¬ P j) : Clear a j := by
  intro x hx e
  exact hj (e ▸ h x hx)

/-! ## The caller's readers and keys -/

variable {S : Type}

theorem bitsClear_of_none (readers : Readers S) (t : S)
    (h : ∀ r, readers t = some r → ∀ e col a, r.1 e col = some a → a.slots = #[]) (j : Nat) :
    BitsClear readers t j :=
  fun r hr e col a ha => clear_of_none (h r hr e col a ha) j

theorem pinsClear_of_none (readers : Readers S) (t : S)
    (h : ∀ r, readers t = some r → ∀ col a, r.2 col = some a → a.slots = #[]) (j : Nat) :
    PinsClear readers t j :=
  fun r hr col a ha => clear_of_none (h r hr col a ha) j

theorem bitsClear_of_slotsIn (readers : Readers S) (t : S) {lo hi : Nat}
    (h : ∀ r, readers t = some r → ∀ e col a, r.1 e col = some a →
      VerifiableInference.Desc.Kinds.Head.Law.SlotsIn lo hi a) {j : Nat} (hj : j < lo ∨ hi ≤ j) :
    BitsClear readers t j :=
  fun r hr e col a ha => clear_of_slotsIn (h r hr e col a ha) hj

theorem pinsClear_of_slotsIn (readers : Readers S) (t : S) {lo hi : Nat}
    (h : ∀ r, readers t = some r → ∀ col a, r.2 col = some a →
      VerifiableInference.Desc.Kinds.Head.Law.SlotsIn lo hi a) {j : Nat} (hj : j < lo ∨ hi ≤ j) :
    PinsClear readers t j :=
  fun r hr col a ha => clear_of_slotsIn (h r hr col a ha) hj

theorem keysClear_of_none (keys : S → Option (Array Aff)) (t : S)
    (h : ∀ KF, keys t = some KF → ∀ a ∈ KF, a.slots = #[]) (j : Nat) : KeysClear keys t j :=
  fun KF hK a ha => clear_of_none (h KF hK a ha) j

theorem keysClear_of_slotsIn (keys : S → Option (Array Aff)) (t : S) {lo hi : Nat}
    (h : ∀ KF, keys t = some KF → ∀ a ∈ KF,
      VerifiableInference.Desc.Kinds.Head.Law.SlotsIn lo hi a) {j : Nat} (hj : j < lo ∨ hi ≤ j) :
    KeysClear keys t j :=
  fun KF hK a ha => clear_of_slotsIn (h KF hK a ha) hj

/-! ## The readers of an attention link -/

open VerifiableInference.Desc.First.Att.P (Runs.gather Runs.u3at Runs.In SeatC ParC readersOfK
  readersOfO)

/-- A form that the attention kind's reader of a table returns names no slot. -/
theorem at_clear {i : Runs.In} {K t n : ℕ} {f : Aff}
    (h : (Runs.gather K (Runs.u3at i t n)).map (·.1) = some f) (j : Nat) : Clear f j := by
  unfold Runs.gather at h
  simp only [Option.map_map, Option.map_eq_some_iff] at h
  obtain ⟨y, hy, rfl⟩ := h
  exact clear_of_pred (P := (· ≠ j)) (K5Law.sv_u3at (Ps := (· ≠ j)) t n #[] y hy (by simp)).1
    fun e => e rfl

/-- So that kind's readers of the planes' matrix meet both hypotheses, at every seat, state and
slot. -/
theorem readersK_clear (seat : SeatC S) (c : ParC) (t : S) (j : Nat) :
    BitsClear (readersOfK seat c) t j ∧ PinsClear (readersOfK seat c) t j := by
  constructor
  · intro r hr e col a ha
    unfold readersOfK at hr
    obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.1 hr
    exact at_clear ha j
  · intro r hr col a ha
    unfold readersOfK at hr
    obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.1 hr
    exact at_clear ha j

/-- **`BitsClear` at an attention link's own readers**, at every plan, state and slot. -/
theorem bitsClear_att (A : OnBytes.Attention.Plan) (t : VerifiableInference.Desc.First.S)
    (j : Nat) : BitsClear (readersOfO A) t j :=
  (readersK_clear _ _ t j).1

/-- **`PinsClear` at an attention link's own readers**, at every plan, state and slot. -/
theorem pinsClear_att (A : OnBytes.Attention.Plan) (t : VerifiableInference.Desc.First.S)
    (j : Nat) : PinsClear (readersOfO A) t j :=
  (readersK_clear _ _ t j).2

end ProofFile.Honest.K3.Good.Live

#print axioms ProofFile.Honest.K3.Good.Live.clear_of_none
#print axioms ProofFile.Honest.K3.Good.Live.clear_of_slotsIn
#print axioms ProofFile.Honest.K3.Good.Live.clear_of_pred
#print axioms ProofFile.Honest.K3.Good.Live.bitsClear_of_none
#print axioms ProofFile.Honest.K3.Good.Live.pinsClear_of_none
#print axioms ProofFile.Honest.K3.Good.Live.bitsClear_of_slotsIn
#print axioms ProofFile.Honest.K3.Good.Live.pinsClear_of_slotsIn
#print axioms ProofFile.Honest.K3.Good.Live.keysClear_of_none
#print axioms ProofFile.Honest.K3.Good.Live.keysClear_of_slotsIn
#print axioms ProofFile.Honest.K3.Good.Live.at_clear
#print axioms ProofFile.Honest.K3.Good.Live.readersK_clear
#print axioms ProofFile.Honest.K3.Good.Live.bitsClear_att
#print axioms ProofFile.Honest.K3.Good.Live.pinsClear_att
