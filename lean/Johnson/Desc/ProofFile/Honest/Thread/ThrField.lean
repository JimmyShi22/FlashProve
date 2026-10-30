-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/ThrField.lean: the state of the prover's run (`Mid`,
Honest/Frame.lean) has a field `opened`: the columns opened so far, which a part is handed beside
the rounds shown. This file says what that field holds at a border of a `Thread`, as one clause
beside the invariant `Thr` (Honest/Thread/Thr.lean), and states that `Thr` and each of its clauses
do not read the field.

  1  `Thread.Field`, `field_iff` the clause: what the field holds at a border. It is `FieldAt`
     (Honest/Field.lean) at the thread's own parameters: `base` followed by the columns of
     `Thread.colsTo`, the columns that `Thread.Made` binds
  2  `took_st`, `took_seen`, `took_loc` `Mid.took` turns the field `opened` alone
  3  `form_took`, `items_took`, `trees_took`, `hand_took`, `fit_took`, `made_took`, `thr_took` the
     defined clauses of `Thr`, and `Thr` itself, at `m.took c` are the same propositions as at `m`;
     its two other clauses read `m.st` alone (`took_st`)
  4  `field_took` the field itself: after `took c` it holds `c` more

Each lemma of 2 and 3 has `rfl` or `Iff.rfl` as its whole proof: the two sides are one term by
unfolding.

Limits.
  * Nothing is said of `play`, `Thread.Moved` or `Thread.Stepped`: these do depend on the field,
    through what a part is handed. The hypotheses of Honest/Thread/Pays.lean take `Thr` alone: they
    are asked at every value of the field, `none` too. At a sub-protocol with a part that errs at
    `none`, `Plays` is met in that form only vacuously.
  * The law that carries `Thread.Field` from a border to the next is not stated here.
  * `field_took` says nothing where no columns are handed (`opened = none`).
  * `base` is a parameter. Nothing says what a run's own value is, and the clause is shown here to
    hold at no state of a run. `FieldAt` fills all the reads at once from the tables available now;
    a run fills them sub-protocol by sub-protocol from those available then; that the two agree is
    not proved (Honest/Field.lean).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Pays
import Johnson.Desc.ProofFile.Honest.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn Strs)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **What the field `opened` holds at border number `b`**: `base`, the columns that earlier chains
have opened, and then the columns that the sub-protocols before the border read. A clause beside
`Thr`, meant as one more hypothesis of a lemma that needs the columns. It is a definition. -/
def Thread.Field (base : List OpenedColumn) (b : Nat) (m : Mid W X) (E : Env) : Prop :=
  FieldAt T.chain T.ft (declsTo T.bs b) base T.front m E

/-- The clause in the terms of `Thread.colsTo`. -/
theorem field_iff (base : List OpenedColumn) (b : Nat) (m : Mid W X) (E : Env) :
    T.Field base b m E ↔ ∃ cols, T.colsTo b m E = .ok cols ∧ m.opened = some (base ++ cols) :=
  Iff.rfl

theorem took_st (m : Mid W X) (c : List OpenedColumn) : (m.took c).st = m.st := rfl

theorem took_seen (m : Mid W X) (c : List OpenedColumn) : (m.took c).seen = m.seen := rfl

theorem took_loc (m : Mid W X) (c : List OpenedColumn) : (m.took c).loc = m.loc := rfl

theorem form_took (b : Nat) (k : Coins Bk) (s : S) (m : Mid W X) (c : List OpenedColumn) :
    T.Form b k s (m.took c) ↔ T.Form b k s m := Iff.rfl

theorem items_took (O : List T.ι) (k : Coins Bk) (s : S) (m : Mid W X) (E : Env) (c : List OpenedColumn) :
    T.Items O k s (m.took c) E ↔ T.Items O k s m E := Iff.rfl

theorem trees_took (L : List Fmt.TreeSource) (k : Coins Bk) (m : Mid W X) (E : Env) (c : List OpenedColumn) :
    T.Trees L k (m.took c) E ↔ T.Trees L k m E := Iff.rfl

theorem hand_took (b : Nat) (k : Coins Bk) (m : Mid W X) (E : Env) (c : List OpenedColumn) :
    T.Hand b k (m.took c) E ↔ T.Hand b k m E := Iff.rfl

theorem fit_took (b : Nat) (m : Mid W X) (c : List OpenedColumn) : T.Fit b (m.took c) ↔ T.Fit b m := Iff.rfl

theorem made_took (b : Nat) (k : Coins Bk) (s : S) (m : Mid W X) (E : Env) (c : List OpenedColumn) :
    T.Made b k s (m.took c) E ↔ T.Made b k s m E := Iff.rfl

/-- **The invariant does not read the field.** -/
theorem thr_took (b : Nat) (k : Coins Bk) (s : S) (m : Mid W X) (E : Env) (c : List OpenedColumn) :
    Thr T b k s (m.took c) E ↔ Thr T b k s m E := Iff.rfl

/-- The field itself: where it held `some a`, after `took c` it holds `some (a ++ c)`. -/
theorem field_took (m : Mid W X) (a c : List OpenedColumn) (h : m.opened = some a) :
    (m.took c).opened = some (a ++ c) := by
  show m.opened.map (· ++ c) = some (a ++ c)
  rw [h]
  rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.field_iff
#print axioms ProofFile.Honest.took_st
#print axioms ProofFile.Honest.took_seen
#print axioms ProofFile.Honest.took_loc
#print axioms ProofFile.Honest.form_took
#print axioms ProofFile.Honest.items_took
#print axioms ProofFile.Honest.trees_took
#print axioms ProofFile.Honest.hand_took
#print axioms ProofFile.Honest.fit_took
#print axioms ProofFile.Honest.made_took
#print axioms ProofFile.Honest.thr_took
#print axioms ProofFile.Honest.field_took
#print axioms ProofFile.Honest.Thread.Field
