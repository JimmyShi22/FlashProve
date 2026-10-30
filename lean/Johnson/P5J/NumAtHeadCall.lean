-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- That `wMsgs` unfolds to the text in
-- the file beneath is BY READING.
/-
Johnson/P5J/NumAtHeadCall.lean: TWO OF WHAT `three_at_free_row` (Johnson/P5J/ThreeAtFreeRow.lean)
TAKES, IN ITS OWN LETTERS, FROM THE HEAD ALONE: hNum and hr.

  **`AtMg.num_at_head`**: the number of oracle messages at the first chain's end is 197 and `wMsgs
    Zp` (Johnson/Desc/Last/CountAtEnd.lean): `AtMg.num_at_head_text`
    (Johnson/P5J/NumAtHead.lean), where `wMsgs` stands written out: by unfolding.
    **`AtMg.num_at_idx`**: the same with W's number as the spender's term, `L.places.idxOf
    (At.N Zp cF).w` at any L with `laidAtCodes Zp.first.codes Zp.made.proof.1 = some L`
    (`AtMg.nW_at_head`, Johnson/P5J/PlanSitsCore.lean: it is 197).
  `AtMg.row_at_head`: the row on written values behind its guard on the key, as a list of tests
    writes it: from `AtMg.pins` (Johnson/P5J/NumbersAtHead.lean).

The five tests on the list of rounds (`ToldDesc.PlanSits`) are another file's: `planSits_at_N`
(Johnson/Second/Seam/PlanSitsInScope.lean): nothing of them is stated here.

WHICH HEAD: the head over the entry tests' list of thirteen rows: see PlanSitsCore.lean.

Limits. The full size alone. Nothing on soundness.
-/
import Johnson.P5J.PlanSitsCore
import Johnson.P5J.NumAtHead
import Johnson.Desc.Last.CountAtEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K12.Door (Laid laidAtCodes)
open VerifiableInference.PlanWritten (madeRow keyOfScan fullKey)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The number of oracle messages at the first chain's end is W's number and what goes out with
W.** -/
theorem AtMg.num_at_head (h : AtMg o Z D r Zp Np cF) :
    (At.N Zp cF).msgsAt none = 197 + VerifiableInference.Desc.Last.wMsgs Zp :=
  h.num_at_head_text

/-- The same with W's number as a term. -/
theorem AtMg.num_at_idx (h : AtMg o Z D r Zp Np cF) {L : Laid}
    (hL : laidAtCodes Zp.first.codes Zp.made.proof.1 = some L) :
    (At.N Zp cF).msgsAt none =
      L.places.idxOf (At.N Zp cF).w + VerifiableInference.Desc.Last.wMsgs Zp := by
  rw [h.nW_at_head hL]
  exact h.num_at_head

/-- The row on written values behind its guard on the key. -/
theorem AtMg.row_at_head (h : AtMg o Z D r Zp Np cF) :
    (!Decidable.decide (keyOfScan Zp.p.X.P = fullKey) || madeRow Zp) = true := by
  rw [h.pins.1, Bool.or_true]

end P5J

#print axioms P5J.AtMg.num_at_head
#print axioms P5J.AtMg.num_at_idx
#print axioms P5J.AtMg.row_at_head
