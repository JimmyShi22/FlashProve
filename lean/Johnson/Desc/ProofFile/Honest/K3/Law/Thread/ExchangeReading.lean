-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeReading.lean: the honest side of the kind
"lookup" (K3): one reading for two hypotheses. The item on the planes
(Honest/K3/Law/Thread/ExchangePlanes.lean) asks two things of one reading ν of places: the data's
bits are what ν reads at their places, and under the lookup's slots the mask entries of ν are the
coins spent (`Dict`, Honest/K3/Law/Thread/ExchangeRows.lean). The first reads cells, the second mask
entries. One definition with code, and theorems.

Terms. Honest/K3/GLOSSARY.md.

What is shown.
  `withMasks ν mask`: the reading ν with its mask row set anew (helper: `withMasks_off`).
  `bAt_no_mask`: at a proof file's lookup the place of a bit is never a mask entry.
  `bits_withMasks`: so "the data's bits are the reading of their places" passes from ν to ν with any
    mask row.
  `dict_withMasks`: the dictionary `Dict` at such a reading is `MasksAre`
    (Honest/K3/Law/Statements.lean) at the mask row.
  `zero_withMasks`: the place that reads 0 is left as it is.
  `bits_congr`: the first hypothesis at two readings that agree off the mask row.
So a tie of a filling's bits to a reading that was shown at some mask row (the row of zeros, say)
serves at the mask row of the coins.

Hypotheses that remain. `hs`: (in `bits_congr`) the two readings agree at every place that is no
mask entry. `hp`: (in `withMasks_off`) the place is no mask entry. The four others (`bAt_no_mask`,
`bits_withMasks`, `dict_withMasks`, `zero_withMasks`) have no hypothesis at all.

Limits. Which reading an item of the table of borders (Johnson/Desc/First/Borders.lean) speaks of is
the table's to say: that its cells are those of a filling's reading, and its mask row the coins, is
not shown in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes.Model.Forest (Shape)
open OnBytes.Slice (GE)

/-- The reading ν with its mask row set anew. -/
def withMasks (ν : _root_.Fo.Pl → GE) (mask : Nat → GE) : _root_.Fo.Pl → GE
  | .mask j => mask j
  | p => ν p

/-- At a proof file's lookup the place of a bit is never a mask entry. -/
theorem bAt_no_mask (h : Shape) (lm jLK : Nat) (θ : GE) (u j k : Nat) :
    (_root_.Fo.numsF h lm jLK θ).bAt u j ≠ .mask k := by
  show (match FoNums.cellOf h u j with
    | some x => _root_.Fo.Pl.cell (FoNums.cellRC h lm x).1 (FoNums.cellRC h lm x).2
    | none => _root_.Fo.Pl.zero) ≠ .mask k
  cases FoNums.cellOf h u j <;> exact fun e => nomatch e

/-- Two readings that agree off the mask row read a bit's place alike. -/
theorem bits_congr (h : Shape) (lm jLK : Nat) (θ : GE) (ν ν' : _root_.Fo.Pl → GE)
    (hs : ∀ p, (∀ k, p ≠ .mask k) → ν p = ν' p) (u j : Nat) :
    ν ((_root_.Fo.numsF h lm jLK θ).bAt u j) = ν' ((_root_.Fo.numsF h lm jLK θ).bAt u j) :=
  hs _ fun k => bAt_no_mask h lm jLK θ u j k

/-- Off the mask row the reading is as it was. -/
theorem withMasks_off (ν : _root_.Fo.Pl → GE) (mask : Nat → GE) (p : _root_.Fo.Pl)
    (hp : ∀ k, p ≠ .mask k) : withMasks ν mask p = ν p := by
  cases p with
  | mask j => exact absurd rfl (hp j)
  | cell r c => rfl
  | key c i => rfl
  | zero => rfl

/-- **"The data's bits are the reading of their places" passes to the reading with any mask row.**
-/
theorem bits_withMasks (h : Shape) (lm jLK : Nat) (θ : GE) (ν : _root_.Fo.Pl → GE) (mask : Nat → GE)
    (u j : Nat) : withMasks ν mask ((_root_.Fo.numsF h lm jLK θ).bAt u j) =
      ν ((_root_.Fo.numsF h lm jLK θ).bAt u j) :=
  withMasks_off ν mask _ fun k => bAt_no_mask h lm jLK θ u j k

/-- **The dictionary at such a reading is `MasksAre` at the mask row.** -/
theorem dict_withMasks {W : Type} (R : Course W) (ν : _root_.Fo.Pl → GE) (mask : Nat → GE) :
    Dict R (withMasks ν mask) ↔ MasksAre R mask := Iff.rfl

theorem zero_withMasks (ν : _root_.Fo.Pl → GE) (mask : Nat → GE) :
    withMasks ν mask .zero = ν .zero := rfl

#print axioms ProofFile.Honest.K3.Law.Exchange.bAt_no_mask
#print axioms ProofFile.Honest.K3.Law.Exchange.bits_congr
#print axioms ProofFile.Honest.K3.Law.Exchange.withMasks_off
#print axioms ProofFile.Honest.K3.Law.Exchange.bits_withMasks
#print axioms ProofFile.Honest.K3.Law.Exchange.dict_withMasks
#print axioms ProofFile.Honest.K3.Law.Exchange.zero_withMasks

end ProofFile.Honest.K3.Law.Exchange
