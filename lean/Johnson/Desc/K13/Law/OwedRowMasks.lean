-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/OwedRowMasks.lean: A STATEMENT THAT IS OWED, WRITTEN AS A DEFINITION OF A Prop:
no proof stands here.
IN PLAIN WORDS. Where kind K13's block (the front, the batching, the quiet part: `atM3 P`) says yes,
ONE row lies on the table behind it; every mask entry that this row names is an entry of the
record's index masks' message; AND THE ROW NAMES AT LEAST ONE.
What lies already: the first two clauses: `atM3_ok` (Johnson/Desc/K13/Law/AtM3.lean), `atM3_ledger`
(Good2.lean), `rowOf_onLedger` (Agree.lean). THE THIRD IS NEW. By reading: the row's mask form
begins with the batching's own fresh entries, zipped with the coefficients of the hiding walk
(`run_fields`, Johnson/Desc/K13/Law/FitC.lean); there are 1 + 2 k fresh entries; the batching's own
test asks 1 ≤ k (`Batt.fits`, OnBytes/Iop/Batt.lean); at one variable or more the walk's list of
coefficients is not empty where the last weight's degree bound is not 0 (`Psc.hidingWalk`,
OnBytes/Iop/Psc.lean).
Used for "the own group has two members" at the last chain's first border: the
number of that group's members counts the messages that the claim's mask entries name.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.AtM3
import Johnson.Desc.K13.Law.Agree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.First (S)

/-- **OWED.** Behind a yes of kind K13's block: one row; on the index masks' message alone; with a
mask entry. -/
def OwedRowMasks : Prop :=
  ∀ {Cl : Type} (P : Where) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    (atM3 (Cl := Cl) P).decide s rs gs = .ok s' →
    ∃ r, s'.rows = [r] ∧ OnLedger s'.out.indexMasks r ∧ r.masks ≠ []

end VerifiableInference.Desc.K13.Law
