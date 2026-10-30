-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Field.lean: one definition, for all, of what the field `opened` holds
at a state of the prover's run, beside the tables that are available there. Definitions only. It
stands over Side.lean alone, so that whoever words a condition before or after a place, or an
invariant from border to border, can name it.

  `roundsBefore`, `roundsUpTo`   the declared rounds of a chain's list before a place, and with it
  `FieldAt`   what the field holds

How it is meant to be used. `Good` (Side.lean) speaks by place: `Lettered.withField` (Owed.lean)
lays `FieldAt` at `roundsBefore` beside a list's A and at `roundsUpTo` beside its B. An invariant
that speaks by the number of sub-protocols played lays it at the declared rounds of these. The
expression under `fillCols` is the one by which the walk (`ChainProgress.settle`, Walk.lean) fills a
sub-protocol's columns, taken over all the rounds at once.

Limits.
  * What is proved of `FieldAt` stands elsewhere: FieldLaw.lean (`FieldAt.step`),
    FieldGood.lean.
  * That it holds after a place where it held before, whatever is played there, is one law's
    matter: `FieldAt.step` (FieldLaw.lean), under its own premises, which stand in its statement. It
    is not stated here.
  * It fills all the rounds' reads at once from the tables that are available now; the walk fills
    them sub-protocol by sub-protocol from those available then. That the two agree is not proved.
  * `base` and `skip` are parameters: nothing here says what a run's own values are.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Side

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn)

variable {S Cl W Y : Type}

/-- The declared rounds of the sub-protocols of a chain's list before a place. -/
def roundsBefore (bs : List (Block S Cl)) (a : Place) : List Fmt.DeclaredRound :=
  (bs.takeWhile fun b => b.place != a).flatMap (·.rounds)

/-- The same with the rounds of the first sub-protocol at the place. AT A PLACE THAT IS IN NO
SUB-PROTOCOL OF THE LIST this and `roundsBefore` are both ALL the list's rounds, in silence
(`.getD []`). -/
def roundsUpTo (bs : List (Block S Cl)) (a : Place) : List Fmt.DeclaredRound :=
  roundsBefore bs a ++ ((bs.find? fun b => b.place == a).map (·.rounds)).getD []

/-- **What the field `opened` holds**: the columns `base`, and then the columns that the available
tables `E` hold for the reads which the declared rounds `decls` make at the challenges that the
state has heard, the first `skip` of them left out. `chain`, `firstTree`: as in `readsOf`. `chain`
IS IDLE HERE: `readsOf` lays it into a read's source alone, which `fillCols` does not read (read off
the two definitions; no lemma states it). `readsOf` stops at the shorter of its two lists, so
challenges beyond these rounds are dropped, and rounds beyond the challenges heard are dropped too;
a `skip` beyond what was heard leaves no challenge. `FieldFit` (FieldLaw.lean) excludes all three:
lay it beside. It is false where no columns are handed (`opened = none`), and where a column is not
available or has another width than its round declares. -/
def FieldAt (chain firstTree : Nat) (decls : List Fmt.DeclaredRound) (base : List OpenedColumn) (skip : Nat)
    (m : Mid W Y) (E : Env) : Prop :=
  ∃ cols, fillCols (readsOf chain firstTree E.stored E.tree decls (m.st.heard.drop skip)) [] =
      .ok cols ∧
    m.opened = some (base ++ cols)

end ProofFile.Honest

#print axioms ProofFile.Honest.roundsBefore
#print axioms ProofFile.Honest.roundsUpTo
#print axioms ProofFile.Honest.FieldAt
