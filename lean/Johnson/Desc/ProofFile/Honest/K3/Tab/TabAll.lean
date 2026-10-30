-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Tab/TabAll.lean:
the reader of the input at the lookups with the layers' calls, attention's calls and the digits read
off tables; and the lot of rows over it. Definitions with code.

Terms. Honest/K3/GLOSSARY.md.

What is defined.
  `tabSourcesAll`: `ownSourcesBound` (Honest/K3/WitBound.lean) with the field `layers` exchanged for
    `layersTab` (Honest/K3/Tab/TabG.lean) and the field `attention` for `attnTab`
    (Honest/K3/Tab/TabALaw.lean). The head's field is `ownSourcesBound`'s.
  `sourcesAtTabAll`: `sourcesAtBound` over it.
  `tabWitAll`: the reader at a site: `tabAsk` (Honest/K3/WitDigitsTab.lean) where the site names the
    round that samples the matrix, the filling's reader over `sourcesAtTabAll` elsewhere.
  `theLotKeepTabAll`, `theLotInstKeepTabAll`: the text of `theLotKeepBound` and
    `theLotInstKeepBound` (Honest/K3/LotInstKeepBound.lean) with that reader. In the place of these,
    never beside them.

Imported. Honest/K3/Tab/TabG.lean, Honest/K3/Tab/TabALaw.lean, Honest/K3/WitDigitsTab.lean,
Honest/K3/LotInstKeepBound.lean.

Users. Honest/K3/Tab/TabAllLaw.lean [not in this library] and Honest/K3/Tab/TabAll2.lean import this
file.

Limits. The head's calls are not read off tables. The equations are in
Honest/K3/Tab/TabAllLaw.lean [not in this library]. Nothing says how long anything takes.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Tab.TabG
import Johnson.Desc.ProofFile.Honest.K3.Tab.TabALaw
import Johnson.Desc.ProofFile.Honest.K3.WitDigitsTab
import Johnson.Desc.ProofFile.Honest.K3.LotInstKeepBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3

variable {X : Type} {W₀ Rc Xi Tr : Type}

/-- `ownSourcesBound` with the layers' and attention's fields off tables. -/
def tabSourcesAll (X : OnBytes.Model.Verify.Public) (cells : Tr → Cells)
    (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) : Sources W₀ Xi Tr :=
  { ownSourcesBound X cells weights pubH with
    layers := TabG.layersTab X
    attention := TabA.attnTab X }

/-- `sourcesAtBound` over it. -/
def sourcesAtTabAll (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) : Sources W₀ Xi Tr :=
  tabSourcesAll Z.p.X cells weights fun x =>
    let q := req x
    headPub Z.p.X q.1 q.2

/-- **The reader of the input at a site, off tables**: `tabAsk` where the site names the round that
samples the matrix, the filling's reader over `sourcesAtTabAll` elsewhere. -/
def tabWitAll (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (s : Site) :
    Local W₀ Rc Xi Tr → Ask :=
  match s.rng with
  | some r => fun t heard => tabAsk Z.p.X s.link r (cells t.trace) heard
  | none => (fastFill (Rc := Rc) (sourcesAtTabAll cells weights req Z)).wit s

/-- **The lot's honest side at rows that pass their tables on, the table's rows in closed form, the
reader of the input `tabWitAll`**, at a letter for the reader of the instance. In the place of
`theLotKeepBound`, never beside it. -/
def theLotKeepTabAll (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn)
    (set : X → RowOwn → X) : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  rowLotKeepAt (fun Z => fastFillKeep (codeRows Z) (tabWitAll cells weights req Z)) get set

/-- **The same at the proof file's own instance.** In the place of `theLotInstKeepBound`, never
beside it. -/
def theLotInstKeepTabAll (cells : Tr → Cells) (weights : W₀ → Weights) (get : X → RowOwn)
    (set : X → RowOwn → X) : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  rowLotKeepAt (fun Z => fastFillKeep (codeRows Z) (tabWitAll cells weights (reqAt Z) Z)) get set

end ProofFile.Honest.K3
