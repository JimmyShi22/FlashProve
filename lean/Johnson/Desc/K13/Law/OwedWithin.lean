-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/OwedWithin.lean: THREE STATEMENTS THAT ARE OWED, EACH WRITTEN AS A DEFINITION
OF A Prop: no proof stands here. THIN: over the layer's tests as code
(Johnson/Desc/K13/PubK13.lean), the two blocks' texts and the ledger's law
(Johnson/Desc/K13/Law/LedgerWithin.lean, OwedLedgers.lean) alone: no table of joints. THE ITEM.
"K13.pileWithin": `pileWithinC s := ledgersFitC s && rowsWithinC s`: every ledger in the statement
is that of so many takes since it was made, and every mask entry that a row on the table names lies
within its table.
  `OwedLedgersC`: the test `ledgersFitC` says yes exactly where every ledger is that of some number
  of takes since it was made (`LedgersFit`). ROAD: `LedgerAt`'s clauses one by one; k := the free
  count − left; `nextAtC m k` is `nextAt m k` by `takenNo_eq` (OnBytes/Iop/LedgerPlaces.lean) where
  0 < m.
  `OwedWithinM3`: OVER A YES OF KIND K13's BLOCK THE ITEM GOES ON. ROAD: `atM3_ok`, `batt_ok`
  (Johnson/Desc/K13/Law/AtM3.lean, Law.lean): the one row behind is `Batt.rowOf pile o`; its mask
  entries are the fresh ones, zipped, and the pile's own, scaled (`run_fields`, FitC.lean; the walk
  through them: `rowOf_onLedger`'s proof, Agree.lean:76); the fresh ones lie within by
  `takeMasksP_within` from the ledgers' clause in front; the pile's own by the rows' clause in
  front; the tables' sizes stay (`atM3_same`, PinDec.lean: each message's shape and the code table).
  The ledgers behind: `takeMasksP_within`'s last clause at the index masks' message; THE
  QUESTION: what else does the block do to the statement (the front; the quiet part), and does it
  leave every other ledger?
  `OwedWithinM4`: OVER A YES OF W's COMMITMENT IT GOES ON. ROAD: `atM4_mid`, `atM4_rec`
  (AtRecord.lean): the rows on the table stay; the sending leaves the older messages whole
  (`K1.sendAtS_kept`) and admits new ones (`ledgerAt_made`); the block behind it adds rows and joins
  messages to the own group (`rowsB_same`: THE QUESTION: SameAll says nothing of a ledger:
  read rowsB's text).
Who spends them: the riders at the two blocks (PileWithin.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.PubK13
import Johnson.Desc.K13.Law.AtRecord
import Johnson.Desc.K13.Law.OwedLedgers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.First (S)

/-- **OWED.** The test on the ledgers says what the laws' word says. -/
def OwedLedgersC : Prop := ∀ s : S, ledgersFitC s = true ↔ LedgersFit s.st

/-- **OWED.** Over a yes of kind K13's block "K13.pileWithin" goes on. -/
def OwedWithinM3 : Prop :=
  ∀ {Cl : Type} (P : Where) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    (atM3 (Cl := Cl) P).decide s rs gs = .ok s' → pileWithinC s = true → pileWithinC s' = true

/-- **OWED.** Over a yes of W's commitment it goes on. -/
def OwedWithinM4 : Prop :=
  ∀ {Cl : Type} (P : Where) (P' : K1.Par) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))),
    (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s' → pileWithinC s = true →
    pileWithinC s' = true

end VerifiableInference.Desc.K13.Law
