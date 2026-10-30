-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Tab/LotTabG.lean:
the lot of rows that pass their tables on, with the layers' calls read off tables; it is the lot at
`boundWit`. Definitions with code, and theorems without a hypothesis.

Terms. Honest/K3/GLOSSARY.md; Honest/K3/Tab/TabG.lean.

What is defined. `theLotKeepTabG`, `theLotInstKeepTabG`: the text of `theLotKeepBound` and
`theLotInstKeepBound` (Honest/K3/LotInstKeepBound.lean) with the reader of the input `tabWitG`
(Honest/K3/Tab/TabGLaw.lean). In the place of these, never beside them.

What is shown. `theLotKeepTabG_eq`, `theLotInstKeepTabG_eq`: they are `theLotKeepBound` and
`theLotInstKeepBound`: so every law of these carries over by one rewriting.

Imported. Honest/K3/Tab/TabGLaw.lean, Honest/K3/LotInstKeepBound.lean.

Limits. Only the layers' calls are read off tables here; attention's, the head's and the digits' are
as in `boundWit`. The equations say that the terms are equal, not how long either takes.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Tab.TabGLaw
import Johnson.Desc.ProofFile.Honest.K3.LotInstKeepBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.TabG

variable {X : Type} {W₀ Rc Xi Tr : Type}

/-- `theLotKeepBound` with the reader of the input `tabWitG`. -/
def theLotKeepTabG (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn)
    (set : X → RowOwn → X) : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  rowLotKeepAt (fun Z => fastFillKeep (codeRows Z) (tabWitG cells weights req Z)) get set

/-- **It is `theLotKeepBound`.** -/
theorem theLotKeepTabG_eq (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn)
    (set : X → RowOwn → X) :
    theLotKeepTabG (Rc := Rc) cells weights req get set =
      theLotKeepBound cells weights req get set := by
  have h : ∀ Z, tabWitG (Rc := Rc) cells weights req Z = boundWit cells weights req Z :=
    fun Z => funext fun s => tabWitG_eq cells weights req Z s
  unfold theLotKeepTabG theLotKeepBound
  simp only [h]

/-- `theLotInstKeepBound` with the reader of the input `tabWitG`. -/
def theLotInstKeepTabG (cells : Tr → Cells) (weights : W₀ → Weights) (get : X → RowOwn)
    (set : X → RowOwn → X) : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  rowLotKeepAt (fun Z => fastFillKeep (codeRows Z) (tabWitG cells weights (reqAt Z) Z)) get set

/-- **It is `theLotInstKeepBound`.** -/
theorem theLotInstKeepTabG_eq (cells : Tr → Cells) (weights : W₀ → Weights) (get : X → RowOwn)
    (set : X → RowOwn → X) :
    theLotInstKeepTabG (Rc := Rc) cells weights get set =
      theLotInstKeepBound cells weights get set := by
  have h : ∀ Z, tabWitG (Rc := Rc) cells weights (reqAt Z) Z = boundWit cells weights (reqAt Z) Z :=
    fun Z => funext fun s => tabWitG_eq cells weights (reqAt Z) Z s
  unfold theLotInstKeepTabG theLotInstKeepBound
  simp only [h]

end ProofFile.Honest.K3.TabG

#print axioms ProofFile.Honest.K3.TabG.theLotKeepTabG_eq
#print axioms ProofFile.Honest.K3.TabG.theLotInstKeepTabG_eq
