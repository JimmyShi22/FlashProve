-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/PadAtHead.lean: the proofs of the two statements of
Honest/K11/Plays/PadAtHeadStatement.lean, to the letter. Lemmas; none of the library's goals.

How. The pad: under the head the list of members is the written one (`P5J.AtMg.ms_full`,
Johnson/P5J/PlanSixAtMg.lean) and the codes are the written ones (`P5J.AtMg.codes_full`,
Johnson/P5J/CodesFullAtMg.lean): so that the mask code of the member at the seat (73, 2) has a
message of at least 3570 entries is a closed fact, proved by evaluation in Lean's kernel (`decide
+kernel`, under a raised `maxRecDepth`); then the frame's authors' `noPad_one`
(Honest/Law/Rule/ReaderPays.lean). The bound: `lkAtFull` (Johnson/Desc/K11/Exchange/LkAtFull.lean):
lk = 18.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.PadAtHeadStatement
import Johnson.Desc.ProofFile.Honest.Law.Rule.ReaderPays
import Johnson.Desc.K11.Exchange.LkAtFull
import Johnson.P5J.PlanSixAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc.Sound (Mem xAt msOf)
open VerifiableInference.Desc.First.Close (mlFull)
open Johnson.Desc.First.ForkMerge.Exchange (lkAtFull)

set_option maxRecDepth 1000000 in
/-- The closed fact: in the written list of members, at the written codes. -/
theorem maskCode_long :
    ((xAt (msOf mlFull) (73, 2)).all fun y =>
      decide (3569 + 1 ≤
        (Johnson.G.codesFull2.mask.getD (y.1.l.get y.2).1.maskCode default).ell)) = true := by
  decide +kernel

/-- **The first 3569 places of the mask row are no pad's.** -/
theorem padAtHead : PadAtHead := by
  intro Z D r Zp Np cF x h xM hx
  rw [h.toAtMg.ms_full] at hx
  have hc := maskCode_long
  rw [hx] at hc
  have hl : 3569 + 1 ≤
      (Johnson.G.codesFull2.mask.getD (xM.1.l.get xM.2).1.maskCode default).ell :=
    of_decide_eq_true hc
  have hcs : h.𝔇.cs = Johnson.G.codesFull2 := h.toAtMg.codes_full
  rw [hcs]
  exact noPad_one hl

/-- **The bound.** -/
theorem freeAtHead : FreeAtHead := by
  intro Z D r Zp Np cF x h Bs hB
  have hlk := (lkAtFull Z D r Zp Np cF x h Bs hB).1
  omega

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.maskCode_long
#print axioms ProofFile.Honest.K11.padAtHead
#print axioms ProofFile.Honest.K11.freeAtHead
