-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/LotInstKeepBound.lean: the honest side of the lot of lookups at
rows that pass their tables on, the table's rows in closed form, with `boundWit`
(Honest/K3/WitBound.lean) for the reader of the input; and the theorems that these are the lots of
Honest/K3/LotInstKeepCode.lean. Definitions with code, and theorems without a hypothesis.

Terms. Honest/K3/GLOSSARY.md. In this file: the reader of the input at a site makes, of the chain's
input and the challenges heard, the keys and bits that the lookup's row is given.

Why. `theLotKeepCode` and `theLotInstKeepCode` hold `fastWit` (Honest/K3/LotInstFast.lean) for that
reader. At the head's lookup that term can make what it reads of the instance anew for every key
and every bit; `boundWit` binds it once at an application of the reader. The two readers are equal,
but a program that takes the halves out of the lot's list evaluates the term that the lot holds.

What is defined.
  `theLotKeepBound`: the text of `theLotKeep` (Honest/K3/LotInstKeep.lean) at `codeRows`, with
    `boundWit` in the place of `fastWit`; at a letter `req` for the reader of the instance.
  `theLotInstKeepBound`: the same at `req := reqAt Z` (Honest/K3/WitReq.lean), at every public part.

What is shown.
  `theLotKeepBound_eq`: `theLotKeepBound cells weights req get set` is
    `theLotKeepCode cells weights req get set`.
  `theLotInstKeepBound_eq`: `theLotInstKeepBound cells weights get set` is
    `theLotInstKeepCode cells weights get set`.
  Both by `rfl`, as `boundWit_fast` is.

Imported. Honest/K3/LotInstKeepCode.lean and Honest/K3/WitBound.lean, and what stands beneath them.

Users. Honest/K3/WitTab.lean, Honest/K3/Tab/TabAll.lean, Honest/K3/Tab/LotTabG.lean and
Honest/K3/Law/Keep/Alike/AlikeRecord.lean [not in this library] import this file. Every theorem that
is stated of `theLotKeepCode` or `theLotInstKeepCode` holds of these lots by rewriting with the two
equations.

Limits. Only one of the lots that bear the one lot's name may stand in a list of lots' honest sides
at a time: these stand in the place of `theLotKeepCode` and `theLotInstKeepCode`, never beside them.
The frame lays the halves of all lots of the list one behind the other (`firstOf`,
Honest/Frame.lean), these lots lay theirs at the sites' places, and the frame's `readyTests` refuses
where two halves stand at one place (`twice`). The equations say that the terms are equal, not how
long either takes.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.LotInstKeepCode
import Johnson.Desc.ProofFile.Honest.K3.WitBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3

variable {X : Type} {W₀ Rc Xi Tr : Type}

/-- **The lot's honest side at rows that pass their tables on, the table's rows in closed form, the
reader of the input `boundWit`**, at a letter for the reader of the instance. In the place of
`theLotKeepCode`, never beside it. -/
def theLotKeepBound (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn)
    (set : X → RowOwn → X) : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  rowLotKeepAt (fun Z => fastFillKeep (codeRows Z) (boundWit cells weights req Z)) get set

/-- It is `theLotKeepCode`. -/
theorem theLotKeepBound_eq (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn)
    (set : X → RowOwn → X) :
    theLotKeepBound (Rc := Rc) cells weights req get set =
      theLotKeepCode cells weights req get set := rfl

/-- **The same at the proof file's own instance.** In the place of `theLotInstKeepCode`, never
beside it. -/
def theLotInstKeepBound (cells : Tr → Cells) (weights : W₀ → Weights) (get : X → RowOwn)
    (set : X → RowOwn → X) : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  rowLotKeepAt (fun Z => fastFillKeep (codeRows Z) (boundWit cells weights (reqAt Z) Z)) get set

/-- It is `theLotInstKeepCode`. -/
theorem theLotInstKeepBound_eq (cells : Tr → Cells) (weights : W₀ → Weights) (get : X → RowOwn)
    (set : X → RowOwn → X) :
    theLotInstKeepBound (Rc := Rc) cells weights get set =
      theLotInstKeepCode cells weights get set := rfl

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.theLotKeepBound_eq
#print axioms ProofFile.Honest.K3.theLotInstKeepBound_eq
