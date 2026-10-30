-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/RowsOfLaid.lean: WITH THE ENTRY TESTS' FOURTEENTH ROW, «LAID» ITSELF GIVES THE CONDITION
`rowsRead` ON THE PUBLIC FILES. A law file: two calls.

Why. Row 14 of the list of entry tests (Johnson/Desc/Laid/ProofAsks.lean) asks `rowsMadeB` of the
public plan that `Desc.Door.planOf` makes. The row's laws
(Johnson/Desc/First/Link/Law/RowsRunLaws.lean) speak of the public plan Zp that `LaidAt.pub` names.
That the two are one plan is what connects them. Here Lean checks it.

  LaidAt.rowsMade      «laid» ⊢ rowsMadeB Zp = true: at the very Zp of `LaidAt.pub`; at every o
  rowsRead_of_laid     **«laid» at the second hash function · the live test ⊢ rowsRead Z**: the
                       premise hB of `rowsRead_of_laid'` is gone

Limits. The live test (protocolDataWellFormedAt) stays a premise. Nothing on soundness.

-/
import Johnson.Desc.Laid.ProofAsksLaw3
import Johnson.Desc.First.Link.Law.RowsRunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)

variable {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl}

/-- Row 14's yes, at the public plan that «laid» names. -/
theorem LaidAt.rowsMade {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    (L : LaidAt o pol lay KL D r Zp Np cF) :
    VerifiableInference.Desc.LinkJoin.rowsMadeB Zp = true :=
  LPFD.asks_rowsMade L.asks L.pub

/-- **«Laid» and the live test give the condition on the rows.** -/
theorem rowsRead_of_laid {Z : VerifierAndGoals.PublicFiles}
    (hl : FlashProve.protocolDataWellFormedAt OnBytes.secondHashFunction (VerifierAndGoals.asDescriptionFiles Z) = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) : rowsRead Z :=
  rowsRead_of_laid' hl L L.rowsMade

end P5J

#print axioms P5J.LaidAt.rowsMade
#print axioms P5J.rowsRead_of_laid
