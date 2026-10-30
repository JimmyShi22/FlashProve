-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Tab/TabAll2.lean:
the reader of the input at the lookups with all four sorts read off tables; and the lot of rows over
it. Definitions with code.

Terms. Honest/K3/GLOSSARY.md.

After. Honest/K3/Tab/TabAll.lean, which reads three of the four sorts off tables: this is its text
with the head's field exchanged too.

What is defined.
  `tabSourcesAll2`: `ownSourcesBound` (Honest/K3/WitBound.lean) with the field `layers` exchanged
    for `layersTab` (Honest/K3/Tab/TabG.lean), `attention` for `attnTab`
    (Honest/K3/Tab/TabALaw.lean) and `head` for `headTab` (Honest/K3/Tab/TabHSeat.lean) at the
    head's public data, which is made once, as the argument of that call.
  `sourcesAtTabAll2`: `sourcesAtBound` over it.
  `tabWitAll2`: the reader at a site: `tabAsk` (Honest/K3/WitDigitsTab.lean) where the site names
    the round that samples the matrix, the filling's reader over `sourcesAtTabAll2` elsewhere.
  `theLotKeepTabAll2`, `theLotInstKeepTabAll2`: the text of `theLotKeepBound` and
    `theLotInstKeepBound` (Honest/K3/LotInstKeepBound.lean) with that reader. In the place of these,
    and of the lots of Honest/K3/Tab/TabAll.lean, never beside them.

Imported. Honest/K3/Tab/TabAll.lean and what it imports; Honest/K3/Tab/TabHSeat.lean.

Users. Honest/K3/Tab/TabAll2Law.lean imports this file.

Limits. The equations are in Honest/K3/Tab/TabAll2Law.lean. Nothing says how long anything takes.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Tab.TabAll
import Johnson.Desc.ProofFile.Honest.K3.Tab.TabHSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3

variable {X : Type} {W₀ Rc Xi Tr : Type}

/-- `ownSourcesBound` with the layers', attention's and the head's fields off tables. -/
def tabSourcesAll2 (X : OnBytes.Model.Verify.Public) (cells : Tr → Cells)
    (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) : Sources W₀ Xi Tr :=
  { ownSourcesBound X cells weights pubH with
    layers := TabG.layersTab X
    attention := TabA.attnTab X
    head := fun x C W => TabH.headTab X (pubH x) C W }

/-- `sourcesAtBound` over it. -/
def sourcesAtTabAll2 (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) : Sources W₀ Xi Tr :=
  tabSourcesAll2 Z.p.X cells weights fun x =>
    let q := req x
    headPub Z.p.X q.1 q.2

/-- **The reader of the input at a site, all four sorts off tables**: `tabAsk` where the site names
the round that samples the matrix, the filling's reader over `sourcesAtTabAll2` elsewhere. -/
def tabWitAll2 (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (s : Site) :
    Local W₀ Rc Xi Tr → Ask :=
  match s.rng with
  | some r => fun t heard => tabAsk Z.p.X s.link r (cells t.trace) heard
  | none => (fastFill (Rc := Rc) (sourcesAtTabAll2 cells weights req Z)).wit s

/-- **The lot's honest side at rows that pass their tables on, the table's rows in closed form, the
reader of the input `tabWitAll2`**, at a letter for the reader of the instance. In the place of
`theLotKeepBound` and of `theLotKeepTabAll` (Honest/K3/Tab/TabAll.lean), never beside them. -/
def theLotKeepTabAll2 (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn)
    (set : X → RowOwn → X) : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  rowLotKeepAt (fun Z => fastFillKeep (codeRows Z) (tabWitAll2 cells weights req Z)) get set

/-- **The same at the proof file's own instance.** In the place of `theLotInstKeepBound` and of
`theLotInstKeepTabAll`, never beside them. -/
def theLotInstKeepTabAll2 (cells : Tr → Cells) (weights : W₀ → Weights) (get : X → RowOwn)
    (set : X → RowOwn → X) : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  rowLotKeepAt (fun Z => fastFillKeep (codeRows Z) (tabWitAll2 cells weights (reqAt Z) Z)) get set

end ProofFile.Honest.K3
