-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5MemOfSome.lean: kind K5 (an attention segment's own rounds): K5Rest's FIELD memAt (K5AtMgPaid.lean) FROM ITS FIELD someMem AND ONE TEST ON THE TABLE's LIST OF MEMBERS ALONE: "two members at one seat have one shape".

Why. MemAt ms l seat k (Johnson/Desc/First/Att/K05MsgTieAt.lean) asks that the FIRST member of ms at the seat of the list's member k have that member's shape: so the table's reader by seat (seatTab) reads the message that the law means. The field someMem gives SOME member of ms that is alike (one entry, one seat).
The two meet as soon as a seat bears one shape in ms. That is a test on ms alone: it reads neither the group nor the lookup's place: once for a head.

Main names:
  `oneShapeB ms`: the test, with code. `oneShape_of_B`: what its yes gives.
  `oneShape_bite`, `oneShape_pass`: a negative test (two members at one seat with two shapes: false) and a positive one (two members at two seats with two shapes: true), by decide.
  **`memAt_of_some`**: oneShapeB ms = true · a member of ms alike to the list's member k ⊢ MemAt ms l seat k.
  `memAt_field`: so K5Rest's field memAt, at every number of the list (the field asks at the messages that the law reads alone).
Is it empty here? oneShapeB IS SHOWN AT NO LIST OF A PLAN. It has run nowhere. At the empty list it says yes, and someMem is then false wherever the caller's list has a member.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05MsgTieAt
import Johnson.Desc.Sound.PinMove

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes
open VerifiableInference.Desc.Sound (Mem Sending Alike seatOf)
open VerifiableInference.Desc.First.Att.P (MemAt)

/-- **The test**: any two members of the list at one seat have one shape. -/
def oneShapeB (ms : List Mem) : Bool :=
  ms.all fun y => ms.all fun y' => !decide (seatOf y = seatOf y') || decide ((y.1.l.get y.2).1 = (y'.1.l.get y'.2).1)

theorem oneShape_of_B {ms : List Mem} (h : oneShapeB ms = true) {y y' : Mem} (hy : y ∈ ms) (hy' : y' ∈ ms)
    (e : seatOf y = seatOf y') : (y.1.l.get y.2).1 = (y'.1.l.get y'.2).1 := by
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h y hy) y' hy'
  rw [Bool.or_eq_true] at h1
  rcases h1 with h2 | h2
  · rw [decide_eq_true e] at h2
    cases h2
  · exact of_decide_eq_true h2

/-- A member of one entry, at a seat. -/
def memOne (s : OracleShape) (t : ℕ × ℕ) : Mem := ⟨⟨[(s, 0)], fun _ => t⟩, ⟨0, Nat.zero_lt_one⟩⟩

/-- The negative test: one seat, two shapes. -/
theorem oneShape_bite : oneShapeB [memOne {} (0, 0), memOne { mainRows := 1 } (0, 0)] = false := by decide

/-- The positive test: two seats, two shapes. -/
theorem oneShape_pass : oneShapeB [memOne {} (0, 0), memOne { mainRows := 1 } (0, 1)] = true := by decide

/-- **The first member at the seat has the shape.** -/
theorem memAt_of_some {ms : List Mem} (h : oneShapeB ms = true) (l : List (OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)
    (k : Fin l.length) (hs : ∃ y ∈ ms, Alike y (⟨⟨l, seat⟩, k⟩ : Mem)) : MemAt ms l seat k := by
  obtain ⟨y₀, hy₀, e1, e2⟩ := hs
  have e1' : y₀.1.l.get y₀.2 = l.get k := e1
  have e2' : seatOf y₀ = seat k := e2
  have hsome : (ms.find? fun y => Decidable.decide (seatOf y = seat k)).isSome = true :=
    List.find?_isSome.2 ⟨y₀, hy₀, decide_eq_true e2'⟩
  obtain ⟨y₁, hy₁⟩ := Option.isSome_iff_exists.1 hsome
  have hm : y₁ ∈ ms := List.mem_of_find?_eq_some hy₁
  have hp' : Decidable.decide (seatOf y₁ = seat k) = true :=
    List.find?_some (p := fun y => Decidable.decide (seatOf y = seat k)) hy₁
  have hp : seatOf y₁ = seat k := of_decide_eq_true hp'
  exact ⟨y₁, hy₁, (oneShape_of_B h hm hy₀ (hp.trans e2'.symm)).trans (congrArg Prod.fst e1')⟩

/-- **K5Rest's field memAt, at every number of the list.** -/
theorem memAt_field {ms : List Mem} (h : oneShapeB ms = true) (l : List (OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)
    (hs : ∀ i, ∃ y ∈ ms, Alike y (⟨⟨l, seat⟩, i⟩ : Mem)) (j : Fin l.length) : MemAt ms l seat j :=
  memAt_of_some h l seat j (hs j)

end H2K5.Door

#print axioms H2K5.Door.oneShape_of_B
#print axioms H2K5.Door.oneShape_bite
#print axioms H2K5.Door.oneShape_pass
#print axioms H2K5.Door.memAt_of_some
#print axioms H2K5.Door.memAt_field
