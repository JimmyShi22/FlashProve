-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/ShapeRun.lean: three general laws on the shape's own run
(Shape.run, Shape.yes, Johnson/Desc/ProofFile/Honest/Thread/Shape.lean), for whoever is to show that
the named public premise "the shape's run returns" holds at some description. General in the
letters; no kind and no size is named. A toy at the end shows that the premise can be met by the
third law and can fail.

Why. The premise is a fold over all members of a chain. Asked of Lean's kernel outright at a large
description it is one long walk. These laws let it be paid in parts.
  `Shape.runFrom Z m n`: the run over the n members from number m on.
  `run_add`: the run over m + n members is the run over m, then `Shape.runFrom Z m n`.
  `border len k`: where piece k begins, if the pieces have the lengths len 0, len 1, ...
  `run_of_pieces`, **`yes_of_pieces`**: with a named shape at each border: one equation a piece
    gives the whole. Each equation can be a closed fact of its own.
  `run_of_inv`, **`yes_of_inv`**: with a property Inv b of the shape in front of member b: if from
    every shape with the property the member's guards return and lead to a shape with the next
    property, the run returns. Nothing is walked: each member is paid by a law "it returns from
    these premises on the shape, and the shape behind has those".
  `toyZ`, `toy_yes`, `toy_no`: a counter that refuses at 3: over three members the run returns (by
    `yes_of_inv`); over four it does not (by evaluation).

Limits. Conditional lemmas on another file's definitions. That the premises can be met at a
description of the protocol is not said. None is one of the library's goals. Nothing on any
property. Credit. Taken over from other work of this project.
 This file
proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Shape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable {S : Type}

/-- The shape's run over the n members from number m on. -/
def Shape.runFrom (Z : Shape S) (m : Nat) : Nat → Z.Sh → Except String Z.Sh
  | 0, a => .ok a
  | n + 1, a => (Z.runFrom m n a).bind (Z.g (m + n))

/-- **The run splits at every border.** -/
theorem run_add (Z : Shape S) (m : Nat) : ∀ (n : Nat) (a : Z.Sh),
    Z.run (m + n) a = (Z.run m a).bind (Z.runFrom m n)
  | 0, a => by
    show Z.run m a = _
    cases Z.run m a <;> rfl
  | n + 1, a => by
    show (Z.run (m + n) a).bind (Z.g (m + n)) = _
    rw [run_add Z m n a]
    cases Z.run m a <;> rfl

/-- Where piece k begins. -/
def border (len : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => border len k + len k

/-- With a named shape at each border, one equation a piece gives the whole run. -/
theorem run_of_pieces (Z : Shape S) (len : Nat → Nat) (c : Nat → Z.Sh) : ∀ K : Nat,
    (∀ k, k < K → Z.runFrom (border len k) (len k) (c k) = .ok (c (k + 1))) →
    Z.run (border len K) (c 0) = .ok (c K)
  | 0, _ => rfl
  | K + 1, h => by
    show Z.run (border len K + len K) (c 0) = _
    rw [run_add, run_of_pieces Z len c K fun k hk => h k (Nat.lt_succ_of_lt hk)]
    exact h K (Nat.lt_succ_self K)

/-- **The premise, from its pieces.** -/
theorem yes_of_pieces (Z : Shape S) (len : Nat → Nat) (c : Nat → Z.Sh) (K : Nat)
    (h : ∀ k, k < K → Z.runFrom (border len k) (len k) (c k) = .ok (c (k + 1))) :
    Z.yes (c 0) (border len K) = true := by
  unfold Shape.yes
  rw [run_of_pieces Z len c K h]
  rfl

/-- From a property that each member's guards carry on, the run returns and ends in it. -/
theorem run_of_inv (Z : Shape S) (Inv : Nat → Z.Sh → Prop) : ∀ (n : Nat) (a₀ : Z.Sh), Inv 0 a₀ →
    (∀ b, b < n → ∀ a, Inv b a → ∃ a', Z.g b a = .ok a' ∧ Inv (b + 1) a') →
    ∃ e, Z.run n a₀ = .ok e ∧ Inv n e
  | 0, a₀, h0, _ => ⟨a₀, rfl, h0⟩
  | n + 1, a₀, h0, H => by
    obtain ⟨e, he, hi⟩ := run_of_inv Z Inv n a₀ h0 fun b hb => H b (Nat.lt_succ_of_lt hb)
    obtain ⟨a', hg, hi'⟩ := H n (Nat.lt_succ_self n) e hi
    refine ⟨a', ?_, hi'⟩
    show (Z.run n a₀).bind (Z.g n) = _
    rw [he]
    exact hg

/-- **The premise, from such a property: nothing is walked.** -/
theorem yes_of_inv (Z : Shape S) (Inv : Nat → Z.Sh → Prop) {n : Nat} {a₀ : Z.Sh} (h0 : Inv 0 a₀)
    (H : ∀ b, b < n → ∀ a, Inv b a → ∃ a', Z.g b a = .ok a' ∧ Inv (b + 1) a') :
    Z.yes a₀ n = true := by
  obtain ⟨e, he, -⟩ := run_of_inv Z Inv n a₀ h0 H
  unfold Shape.yes
  rw [he]
  rfl

/-! ## A toy -/

/-- A counter that refuses at 3. -/
def toyZ : Shape Unit where
  Sh := Nat
  sh := fun _ => 0
  g := fun _ a => if a < 3 then .ok (a + 1) else .error "full"
  vals := fun _ _ _ _ => true

/-- Over three members the toy's run returns: by the property "the count is the member's number". -/
theorem toy_yes : toyZ.yes (0 : Nat) 3 = true :=
  yes_of_inv toyZ (fun b (a : Nat) => a = b) rfl fun b hb (a : Nat) (ha : a = b) =>
    ⟨(b + 1 : Nat), by
      show (if a < 3 then (Except.ok (a + 1) : Except String Nat) else Except.error "full") =
        Except.ok (b + 1)
      rw [ha, if_pos hb], rfl⟩

/-- Over four it does not. -/
theorem toy_no : toyZ.yes (0 : Nat) 4 = false := by decide

end ProofFile.Honest

#print axioms ProofFile.Honest.run_add
#print axioms ProofFile.Honest.run_of_pieces
#print axioms ProofFile.Honest.yes_of_pieces
#print axioms ProofFile.Honest.run_of_inv
#print axioms ProofFile.Honest.yes_of_inv
#print axioms ProofFile.Honest.toy_yes
#print axioms ProofFile.Honest.toy_no
