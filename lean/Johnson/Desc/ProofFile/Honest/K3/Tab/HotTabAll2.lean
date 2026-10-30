-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Tab/HotTabAll2.lean: the lot of rows that pass their tables on,
with the reader of the input off tables at all four sorts and the inner loops of Honest/K3/Hot.lean;
it is the lot at `boundWit`. Definitions with code, and theorems without a hypothesis.

Terms. Honest/K3/GLOSSARY.md.

Why. A play of the honest prover wants both: the reader of the input that makes each inner value
once a lookup (`tabWitAll2`, Honest/K3/Tab/TabAll2.lean) and the row's loops in a file whose
compiled code can be loaded (`hotFillKeep`, Honest/K3/RowKeepHot.lean). Here they stand in one lot,
with the equation that says that it is the kept lot.

What is defined. `theLotKeepHotTabAll2`, `theLotInstKeepHotTabAll2`: the text of `theLotKeepBound`
and `theLotInstKeepBound` (Honest/K3/LotInstKeepBound.lean) with `hotFillKeep` for `fastFillKeep`
and `tabWitAll2` for `boundWit`. In the place of these, never beside them; and so of every lot that
bears the one lot's name: only one of them may stand in a list of lots' honest sides at a time
(Honest/K3/LotInstKeepBound.lean). A caution: nothing here shows or tests it.

What is shown. `theLotKeepHotTabAll2_eq`, `theLotInstKeepHotTabAll2_eq`: they are `theLotKeepBound`
and `theLotInstKeepBound`.

By. `hotFillKeep_eq` (Honest/K3/RowKeepHot.lean), which is general in the reader of the input, and
`tabWitAll2_eq` (Honest/K3/Tab/TabAll2Law.lean).

Imported. Honest/K3/RowKeepHot.lean, Honest/K3/Tab/TabAll2Law.lean.

Users. Honest/K3/Law/CoverageLotsNamed.lean; Honest/AtPureKeepTab.lean
[not in this library], whose list of lots lays
`theLotInstKeepHotTabAll2`.

Limits. The equations say that the terms are equal, not how long either takes. A lot lays a half
only at an address at which a site can be made (`lotBy`, Honest/K3/Lot.lean); that the two lots'
halves are those of `rowLotKeep` at their letters: `theLotKeepHotTabAll2_halves`,
`theLotInstKeepHotTabAll2_halves` (Honest/K3/Law/CoverageLotsNamed.lean).

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.RowKeepHot
import Johnson.Desc.ProofFile.Honest.K3.Tab.TabAll2Law

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3

variable {X : Type} {W₀ Rc Xi Tr : Type}

/-- **The lot's honest side, the reader of the input off tables, the inner loops by
Honest/K3/Hot.lean**, at a letter for the reader of the instance. In the place of `theLotKeepBound`,
never beside it. -/
def theLotKeepHotTabAll2 (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn)
    (set : X → RowOwn → X) : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  rowLotKeepAt (fun Z => hotFillKeep (codeRows Z) (tabWitAll2 cells weights req Z)) get set

/-- **It is `theLotKeepBound`.** -/
theorem theLotKeepHotTabAll2_eq (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn)
    (set : X → RowOwn → X) :
    theLotKeepHotTabAll2 (Rc := Rc) cells weights req get set =
      theLotKeepBound cells weights req get set := by
  have h : ∀ Z, tabWitAll2 (Rc := Rc) cells weights req Z = boundWit cells weights req Z :=
    fun Z => funext fun s => tabWitAll2_eq cells weights req Z s
  unfold theLotKeepHotTabAll2 theLotKeepBound
  simp only [hotFillKeep_eq, h]

/-- **The same at the proof file's own instance.** In the place of `theLotInstKeepBound`, never
beside it. -/
def theLotInstKeepHotTabAll2 (cells : Tr → Cells) (weights : W₀ → Weights) (get : X → RowOwn)
    (set : X → RowOwn → X) : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  rowLotKeepAt (fun Z => hotFillKeep (codeRows Z) (tabWitAll2 cells weights (reqAt Z) Z)) get set

/-- **It is `theLotInstKeepBound`.** -/
theorem theLotInstKeepHotTabAll2_eq (cells : Tr → Cells) (weights : W₀ → Weights)
    (get : X → RowOwn) (set : X → RowOwn → X) :
    theLotInstKeepHotTabAll2 (Rc := Rc) cells weights get set =
      theLotInstKeepBound cells weights get set := by
  have h : ∀ Z,
      tabWitAll2 (Rc := Rc) cells weights (reqAt Z) Z = boundWit cells weights (reqAt Z) Z :=
    fun Z => funext fun s => tabWitAll2_eq cells weights (reqAt Z) Z s
  unfold theLotInstKeepHotTabAll2 theLotInstKeepBound
  simp only [hotFillKeep_eq, h]

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.theLotKeepHotTabAll2_eq
#print axioms ProofFile.Honest.K3.theLotInstKeepHotTabAll2_eq
