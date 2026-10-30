-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/LotInstKeep.lean: the honest side of the lot of lookups at the
proof file's own instance, at rows that pass their tables on: beside `theLotFast` and
`theLotInstFast` (Honest/K3/LotInstFast.lean). Definitions with code; no theorem.

Terms. Honest/K3/GLOSSARY.md. In this file: a row's own state is a value of `RowOwn`
(Honest/K3/KeptTypes.lean).

What is defined.
  `theLotKeep row cells weights req get set`: at each site `proverSideOfLookupInChainKeepingTablesAtOneOwner` at `fastKeeps`
    (Honest/K3/RowKeepFill.lean); the reader of the input is `fastWit`, as in `theLotFast`.
  `theLotInstKeep row cells weights get set`: the same at the proof file's own instance (`reqAt`).
  Three arguments more than the earlier lots have. Here row gives the table's rows, of the public
    part and the site; get reads the row's own state in what the chain's parts pass on; set lays it
    there.

In whose place. In the place of `theLotFast` or `theLotInstFast`, never beside them.

Imported. Honest/K3/LotInstFast.lean for `fastWit` and `reqAt`; Honest/K3/RowKeepFill.lean. The
frame's files lie beneath them.

Users. Honest/K3/LotInstKeepCode.lean imports this file. Meant for a filling of the honest prover
whose state has a field of the type `RowOwn`, with `rowOwn₀` in the first state.

Limits. Nothing is shown here. For these halves to show the rounds of the halves of
`theLotInstFast`, four things are wanted: that row is the table of which the face's `leaf` is the
extension, as `Fast.rowOfFace` is; the laws of Honest/K3/Law/Keep/; that get reads what set has
laid; and that a row begins at `rowOwn₀`.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.LotInstFast
import Johnson.Desc.ProofFile.Honest.K3.RowKeepFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E)

variable {X : Type} {W₀ Rc Xi Tr : Type}

/-- **The lot's honest side at rows that pass their tables on**, at a letter for the reader of the
instance. -/
def theLotKeep (row : Pub → Site → E → Nat → E) (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn)
    (set : X → RowOwn → X) : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  rowLotKeepAt (fun Z => fastFillKeep (row Z) (fastWit cells weights req Z)) get set

/-- The same at the proof file's own instance. -/
def theLotInstKeep (row : Pub → Site → E → Nat → E) (cells : Tr → Cells) (weights : W₀ → Weights)
    (get : X → RowOwn) (set : X → RowOwn → X) :
    HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  rowLotKeepAt (fun Z => fastFillKeep (row Z) (fastWit cells weights (reqAt Z) Z)) get set

end ProofFile.Honest.K3
