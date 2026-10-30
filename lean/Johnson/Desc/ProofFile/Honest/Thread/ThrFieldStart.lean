-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/ThrFieldStart.lean: the state of the prover's run (`Mid`,
Honest/Frame.lean) has a field `opened`: the columns opened so far. `Thread.Field`
(Honest/Thread/ThrField.lean) says what that field holds at a border of a thread. This file starts
it: what the clause says at the first border, and at which state it holds there. No definition.

  1  `Thread.field_zero_iff`   at border 0 the clause says that the field is `some base`. No
     sub-protocol stands before that border: no column is read there (`fieldAt_nil`,
     Honest/FieldFacts.lean)
  2  `Thread.field_start`   it holds at every state whose field has been laid at `some base`
  3  `thr_laid`   the invariant `Thr` at a state with the field set to any value, `none` too, is the
     same proposition as at the state itself. Its whole proof is `Iff.rfl`, as for `thr_took`
     (Honest/Thread/ThrField.lean)
  4  `thr_field_start`   from the invariant at border 0 at a state `m`: the invariant and the clause
     at `m` with the field laid at `some base`

The use. At the frame's three start states (`Ready.start₁`, `Ready.start₂`, `Ready.start₃`,
Honest/Frame.lean) no columns are handed: the field is `none`. `ChainProgress.start` (Honest/Walk.lean) lays
it at `some front`. By 4, whoever has the invariant at border 0 at a start state has it, with the
clause at base := front beside it, at that state with the field so laid: the state that
`ChainProgress.start` hands to `ChainProgress.settle`, not the one that it returns.

Limits.
  * `base` is a parameter. This file does not say which value a run has. In `runC`
    (Honest/Walk.lean) the first and the shared chain are started at `[]` and the second at the
    columns of the other two.
  * Nothing relates the states of this file to the states of a walk.
  * Nothing here shows that the invariant holds at any state of a run.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ThrField
import Johnson.Desc.ProofFile.Honest.FieldFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn Strs)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **At border 0 the clause says that the field is `some base`.** -/
theorem Thread.field_zero_iff (base : List OpenedColumn) (m : Mid W X) (E : Env) :
    T.Field base 0 m E ↔ m.opened = some base := by
  show FieldAt T.chain T.ft [] base T.front m E ↔ m.opened = some base
  exact fieldAt_nil

/-- It holds at a state whose field has been laid at `some base`. -/
theorem Thread.field_start (base : List OpenedColumn) (m : Mid W X) (E : Env) :
    T.Field base 0 { m with opened := some base } E :=
  (T.field_zero_iff base _ E).2 rfl

/-- The invariant does not see the field: at every value `o`, `none` too. -/
theorem thr_laid (b : Nat) (k : Coins Bk) (s : S) (m : Mid W X) (E : Env)
    (o : Option (List OpenedColumn)) :
    Thr T b k s { m with opened := o } E ↔ Thr T b k s m E := Iff.rfl

/-- **The start**: the invariant and the clause, at the state with the field laid. `hA`: the
invariant at border 0 at `m`. -/
theorem thr_field_start {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} (hA : Thr T 0 k s m E)
    (base : List OpenedColumn) :
    Thr T 0 k s { m with opened := some base } E ∧
      T.Field base 0 { m with opened := some base } E :=
  ⟨(thr_laid T 0 k s m E (some base)).2 hA, T.field_start base m E⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.Thread.field_zero_iff
#print axioms ProofFile.Honest.Thread.field_start
#print axioms ProofFile.Honest.thr_laid
#print axioms ProofFile.Honest.thr_field_start
