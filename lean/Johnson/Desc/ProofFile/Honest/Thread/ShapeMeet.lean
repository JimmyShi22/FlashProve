-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/ShapeMeet.lean: THE FORM IN WHICH THE LETTERS OF THE CUT
"STRUCTURE | VALUES" (Shape, Johnson/Desc/ProofFile/Honest/Thread/Shape.lean) ARE TO BE FILLED: a
shape, and for each member ONE Bool (its guards on the structure, as a function of the shape) AND
ONE UPDATE. A definition and short general laws; a toy.

  `Shape.meet sh guard upd vals`: the letters with g b a := if guard b a then .ok (upd b a) else a
    refusal. No value is computed in g.
  `meet_g_ok`, `meet_g_no`: what g is where the guard passes and where it does not.
  `meetRun guard upd m n a`: with code, in the members' order: the guards of the n members from
    number m on pass along the updates; it returns the shape behind them.
  `meet_runFrom`: the shape's run over these members returns e just where meetRun does.
  **`meet_yes`**: the named public premise is meetRun's yes.
  `meet_piece`: one piece for `yes_of_pieces` (ShapeRun.lean), from a Bool test that Lean's kernel
    can evaluate where the shapes have a lawful comparison with code.
  `toyM`, `toyM_yes`, `toyM_no`: a counter that refuses at 3, in this form.

Limits. Conditional lemmas on another file's definitions. Nothing holds a guard or an update against
a description's text: that is (B1) and (B2) of Shape.lean, owed member by member. None is one of the
library's goals. Nothing on any property. Credit. Written by an author of another thread of this

 This file proves nothing about soundness, completeness, hiding or any other
property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ShapeRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Sh : Type}

/-- **One Bool and one update a member.** -/
def Shape.meet (sh : S → Sh) (guard : Nat → Sh → Bool) (upd : Nat → Sh → Sh)
    (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) : Shape S where
  Sh := Sh
  sh := sh
  g := fun b a => if guard b a then .ok (upd b a) else .error "a guard on the shape"
  vals := vals

variable (sh : S → Sh) (guard : Nat → Sh → Bool) (upd : Nat → Sh → Sh)
  (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)

theorem meet_g_ok {b : Nat} {a : Sh} (h : guard b a = true) :
    (Shape.meet sh guard upd vals).g b a = .ok (upd b a) := by
  show (if guard b a then Except.ok (upd b a) else Except.error "a guard on the shape") = _
  rw [if_pos h]
  rfl

theorem meet_g_no {b : Nat} {a : Sh} (h : guard b a = false) :
    (Shape.meet sh guard upd vals).g b a = .error "a guard on the shape" := by
  show (if guard b a then Except.ok (upd b a) else Except.error "a guard on the shape") = _
  rw [h]
  rfl

/-- The guards of the n members from number m on, along the updates, in the members' order. -/
def meetRun (guard : Nat → Sh → Bool) (upd : Nat → Sh → Sh) : Nat → Nat → Sh → Option Sh
  | _, 0, a => some a
  | m, n + 1, a => if guard m a then meetRun guard upd (m + 1) n (upd m a) else none

/-- One member more behind. -/
theorem meetRun_succ : ∀ (n m : Nat) (a : Sh), meetRun guard upd m (n + 1) a =
    (meetRun guard upd m n a).bind fun e => if guard (m + n) e then some (upd (m + n) e) else none
  | 0, m, a => by
    show (if guard m a then some (upd m a) else none) = _
    rfl
  | n + 1, m, a => by
    show (if guard m a then meetRun guard upd (m + 1) (n + 1) (upd m a) else none) = _
    rw [meetRun_succ n (m + 1) (upd m a)]
    show _ = (if guard m a then meetRun guard upd (m + 1) n (upd m a) else none).bind _
    cases guard m a
    · rfl
    · simp only [if_true, Nat.add_assoc, Nat.add_comm 1 n]

/-- **The shape's run over some members is meetRun.** -/
theorem meet_runFrom (m : Nat) : ∀ (n : Nat) (a : Sh),
    ((Shape.meet sh guard upd vals).runFrom m n a).toOption = meetRun guard upd m n a
  | 0, _ => rfl
  | n + 1, a => by
    rw [meetRun_succ, ← meet_runFrom m n a]
    show (((Shape.meet sh guard upd vals).runFrom m n a).bind
      ((Shape.meet sh guard upd vals).g (m + n))).toOption = _
    cases (Shape.meet sh guard upd vals).runFrom m n a with
    | error _ => rfl
    | ok e =>
      show ((if guard (m + n) e then Except.ok (upd (m + n) e)
        else Except.error "a guard on the shape" : Except String Sh)).toOption =
          if guard (m + n) e then some (upd (m + n) e) else none
      cases guard (m + n) e <;> rfl

/-- The run from the first member on is the run. -/
theorem runFrom_zero (Z : Shape S) : ∀ (n : Nat) (a : Z.Sh), Z.runFrom 0 n a = Z.run n a
  | 0, _ => rfl
  | n + 1, a => by
    show (Z.runFrom 0 n a).bind (Z.g (0 + n)) = (Z.run n a).bind (Z.g n)
    rw [runFrom_zero Z n a, Nat.zero_add]

/-- **The named public premise is meetRun's yes.** -/
theorem meet_yes (a : Sh) (n : Nat) :
    (Shape.meet sh guard upd vals).yes a n = (meetRun guard upd 0 n a).isSome := by
  unfold Shape.yes
  rw [← runFrom_zero, meet_runFrom]
  rfl

/-- **One piece, from a test with code.** -/
theorem meet_piece [BEq Sh] [LawfulBEq Sh] {m n : Nat} {a e : Sh}
    (h : (meetRun guard upd m n a == some e) = true) :
    (Shape.meet sh guard upd vals).runFrom m n a = .ok e := by
  have hw : meetRun guard upd m n a = some e := eq_of_beq h
  have ht := meet_runFrom sh guard upd vals m n a
  rw [hw] at ht
  cases hr : (Shape.meet sh guard upd vals).runFrom m n a with
  | error x =>
    rw [hr] at ht
    cases ht
  | ok x =>
    rw [hr] at ht
    exact congrArg Except.ok (Option.some.inj ht)

/-! ## A toy -/

/-- A counter that refuses at 3, in this form. -/
def toyM : Shape Unit :=
  Shape.meet (fun _ => (0 : Nat)) (fun _ a => decide (a < 3)) (fun _ a => a + 1) fun _ _ _ _ => true

theorem toyM_yes : toyM.yes (0 : Nat) 3 = true := by
  unfold toyM
  rw [meet_yes]
  decide

theorem toyM_no : toyM.yes (0 : Nat) 4 = false := by
  unfold toyM
  rw [meet_yes]
  decide

end ProofFile.Honest

#print axioms ProofFile.Honest.meet_g_ok
#print axioms ProofFile.Honest.meet_g_no
#print axioms ProofFile.Honest.meetRun_succ
#print axioms ProofFile.Honest.meet_runFrom
#print axioms ProofFile.Honest.runFrom_zero
#print axioms ProofFile.Honest.meet_yes
#print axioms ProofFile.Honest.meet_piece
#print axioms ProofFile.Honest.toyM_yes
#print axioms ProofFile.Honest.toyM_no
