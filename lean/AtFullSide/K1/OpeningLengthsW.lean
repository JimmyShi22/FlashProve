-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K1/OpeningLengthsW.lean: THE SHARED "SENDING" (the kind K1): THE OPENING's MESSAGES
NUMBER 0 AND NUMBER 4: HOW MANY ENTRIES THEIR MASK ROWS HAVE, AND THAT BOTH NUMBERS LIE BELOW THE
PLAN's NUMBER OF MESSAGES. For a spender's authors, who must meet two premises of our laws on these
two messages: "n below the messages' number" (mask_in,
Johnson/Desc/ProofFile/Honest/K1/MaskLaw.lean) and "the entry's number lies below rows * length"
(mask_in; msgTxt_mask_slot, Johnson/Desc/ProofFile/Honest/K1/ScriptMaskSlot.lean). PUBLIC DATA
ALONE: plans, shapes, codes' lengths, counts: how long a row is, never what stands in it. Four
theorems; NO DEFINITION. A TRIAL THAT COUNTS IN NO COLUMN.
NO PROPERTY IS CLAIMED.

At the written data (K1.parGF):
  - idxLenW: at message number 4, mask rows times the mask code's length is 256. By evaluation in
    Lean's kernel.
  - idxLenW_bent: A NEGATIVE TEST: at message number 3 that equation is false.
NOT TYPED ANEW: the like at message number 0, which is 8192: the second clause of rowFreeW
(Johnson/Desc/ProofFile/Honest/K1/Law/RowOwnerAtWritten.lean; called here).

Under h (the library's head: A HYPOTHESIS) and O, at the plan at the description's own ground
(K1.firstPar Bs.G₀.first (K1.gpOf Zp)):
  - openingNos_head: 0 and 4 lie below the plan's number of messages (which is five: the sixth
    clause of opening_head, AtFullSide/K1/OpeningStartsW.lean; called here).
  - openingLens_head: mask rows times the mask code's length is 8192 at number 0 and 256 at number
    4: the very term of the two laws' premise.

Limits. THE FULL SIZE ALONE. The two last are CONDITIONAL on h and O, at the format's second hash function.
That any spender's entries lie below 8192 or 256 is not said here: that is a sentence on the
spender's own numbers. Nothing on a run, or on what any coin is. Nothing on soundness, on
completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import AtFullSide.K1.OpeningStartsW
import Johnson.Desc.ProofFile.Honest.K1.Law.RowOwnerAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K1
open ProofFile.Honest ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (parGF)
open Johnson.Prover.Send (shapeAt)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)

/-- At message number 4 the mask rows have 256 entries in all. -/
theorem idxLenW :
    (shapeAt parGF 4).maskRows * (parGF.codes.mask.getD (shapeAt parGF 4).maskCode default).ell =
      256 := by
  decide +kernel

/-- The equation can fail: at message number 3 it is false. -/
theorem idxLenW_bent : decide
    ((shapeAt parGF 3).maskRows * (parGF.codes.mask.getD (shapeAt parGF 3).maskCode default).ell =
      256) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- h AND O ARE PREMISES. **NUMBERS 0 AND 4 LIE BELOW THE PLAN's NUMBER OF MESSAGES.** -/
theorem openingNos_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    0 < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size ∧
      4 < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size := by
  rw [(opening_head h O).2.2.2.2.2]
  exact ⟨by omega, by omega⟩

/-- h AND O ARE PREMISES. **THE MASK ROWS' ENTRIES: 8192 AT NUMBER 0, 256 AT NUMBER 4.** -/
theorem openingLens_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    (shapeAt (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) 0).maskRows *
        ((K1.firstPar Bs.G₀.first (K1.gpOf Zp)).codes.mask.getD
          (shapeAt (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) 0).maskCode default).ell = 8192 ∧
      (shapeAt (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) 4).maskRows *
        ((K1.firstPar Bs.G₀.first (K1.gpOf Zp)).codes.mask.getD
          (shapeAt (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) 4).maskCode default).ell = 256 := by
  rw [K1.eG_atAll h O (K1.pin1_atAll h)]
  exact ⟨rowFreeW.2, idxLenW⟩

end AtFullSide.K1

#print axioms AtFullSide.K1.idxLenW
#print axioms AtFullSide.K1.idxLenW_bent
#print axioms AtFullSide.K1.openingNos_head
#print axioms AtFullSide.K1.openingLens_head
