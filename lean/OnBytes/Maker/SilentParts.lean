-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/SilentParts.lean: what the three silent rounds of a file send: types, the values that
a file as read gives them, and the test that holds the prover to the record's answers.

In the joined protocol of a file (Compile/Joined/Types.lean) the front, the joining round and the
seam send a plain part alone. What a chain's first hash call holds beyond the typed query's own
fields rides there: in the front's the record's answers and, in a proof file, the number of the
stored copy; in the joining round's the answers again and the second chain's run's value; in the
seam's the third chain's run's value.

Main definitions.
  `FrontMsg A`: the answers and a number (0 in a key file). `Compile.Joined.JoinMsg A ByteArray` is
    the joining round's, `ByteArray` the seam's.
  `silentOf ans copy`: the test: both copies of the answers are the instance's, and the number is
    the instance's.
  `frontOf`, `joinOf`, `seamOf`: the three values from a table's answers, the copy's number and the
    three chains as read; the last two give nothing where a chain has no run's value.
Main theorem. `silentOf_answers`: the premise of `wholeDesc_answers` (OnBytes/Maker/WholeLaws.lean).

What is not said. That a first hash call of the shipped format holds just these values, in which
order and spelling. The run's values are free data: no test reads them.


-/
import Compile.Joined.Types
import OnBytes.Proof.Tail

set_option autoImplicit false

namespace OnBytes.Maker

open Compile.Joined (JoinMsg)

/-- What the front sends: the record's answers, and the number of the stored copy. -/
structure FrontMsg (A : Type) where
  answers : A
  copy : Nat

/-- **The test on the silent rounds' plain parts.** ans, copy: the answers and the copy's number as
the instance has them. -/
def silentOf {Xi A : Type} [DecidableEq A] (ans : Xi → A) (copy : Xi → Nat) (x : Xi)
    (f : FrontMsg A) (j : JoinMsg A ByteArray) (_ : ByteArray) : Bool :=
  decide (f.answers = ans x) && decide (f.copy = copy x) && decide (j.answers = ans x)

theorem silentOf_answers {Xi A : Type} [DecidableEq A] (ans : Xi → A) (copy : Xi → Nat) (x : Xi)
    (f : FrontMsg A) (j : JoinMsg A ByteArray) (t : ByteArray)
    (h : silentOf ans copy x f j t = true) : f.answers = ans x ∧ j.answers = ans x := by
  unfold silentOf at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.2⟩

theorem silentOf_copy {Xi A : Type} [DecidableEq A] (ans : Xi → A) (copy : Xi → Nat) (x : Xi)
    (f : FrontMsg A) (j : JoinMsg A ByteArray) (t : ByteArray)
    (h : silentOf ans copy x f j t = true) : f.copy = copy x := by
  unfold silentOf at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

/-- The front's plain part of a file. -/
def frontOf {A : Type} (answers : A) (copy : Nat) : FrontMsg A := ⟨answers, copy⟩

/-- The joining round's plain part of a file as read. -/
def joinOf {A : Type} (answers : A) (r : Proof.TailRead) : Option (JoinMsg A ByteArray) :=
  r.shared.out.run.map fun run => ⟨answers, run⟩

/-- The seam's plain part of a file as read. -/
def seamOf (r : Proof.TailRead) : Option ByteArray := r.second.out.run

end OnBytes.Maker
