-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/WitTab.lean: the reader of the input at the lookups, with the
reader with tables (`tabAsk`, Honest/K3/WitDigitsTab.lean) at the lookups on the digits; and the
lots that hold it. Definitions with code; no theorem. That reader and lots are those of
Honest/K3/WitBound.lean and Honest/K3/LotInstKeepBound.lean is shown in Honest/K3/Law/WitTab.lean
[not in this library; so here read: not proved in this library].

Terms. Honest/K3/GLOSSARY.md. In this file: the reader of the input at a site makes, of the chain's
input and the challenges heard, the keys and bits that the lookup's row is given.

What is defined.
  `tabWit`: the reader at a site: `tabAsk` where the site names the round that samples the matrix;
    elsewhere `boundWit`'s own term.
  `theLotKeepTab`, `theLotInstKeepTab`: the texts of `theLotKeepBound` and `theLotInstKeepBound`
    with `tabWit` in the place of `boundWit`.

Imported. Honest/K3/WitDigitsTab.lean, Honest/K3/LotInstKeepBound.lean, and what stands beneath
them. No file of laws on the tables.

Users. Honest/K3/Law/WitTab.lean [not in this library].

Limits. Only one of the lots that bear the one lot's name may stand in a list of lots' honest sides
at a time: these stand in the place of `theLotKeepBound` and `theLotInstKeepBound`, never beside
them. The frame lays the halves of all lots of the list one behind the other (`firstOf`,
Honest/Frame.lean), these lots lay theirs at the sites' places, and the frame's `readyTests` refuses
where two halves stand at one place (`twice`). On the layers', attention's and the head's calls
nothing is exchanged. How long anything takes is not said here.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.WitDigitsTab
import Johnson.Desc.ProofFile.Honest.K3.LotInstKeepBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3

variable {X : Type} {W₀ Rc Xi Tr : Type}

/-- The reader of the input at a site: `tabAsk` where the site names the round that samples the
matrix, the filling's reader over `sourcesAtBound` elsewhere. -/
def tabWit (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (s : Site) :
    Local W₀ Rc Xi Tr → Ask :=
  match s.rng with
  | some r => fun t heard => tabAsk Z.p.X s.link r (cells t.trace) heard
  | none => (fastFill (Rc := Rc) (sourcesAtBound cells weights req Z)).wit s

/-- **The lot's honest side at rows that pass their tables on, the table's rows in closed form, the
reader of the input `tabWit`**, at a letter for the reader of the instance. In the place of
`theLotKeepBound`, never beside it. -/
def theLotKeepTab (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn)
    (set : X → RowOwn → X) : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  rowLotKeepAt (fun Z => fastFillKeep (codeRows Z) (tabWit cells weights req Z)) get set

/-- **The same at the proof file's own instance.** In the place of `theLotInstKeepBound`, never
beside it. -/
def theLotInstKeepTab (cells : Tr → Cells) (weights : W₀ → Weights) (get : X → RowOwn)
    (set : X → RowOwn → X) : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  rowLotKeepAt (fun Z => fastFillKeep (codeRows Z) (tabWit cells weights (reqAt Z) Z)) get set

end ProofFile.Honest.K3
