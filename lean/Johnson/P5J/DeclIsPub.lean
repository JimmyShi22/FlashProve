-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/DeclIsPub.lean: UNDER LaidAt THE DESCRIPTION's DECLARED ROUNDS ARE THE PUBLIC PART's. Two theorems. FIRST ISSUE.
  Why. The closed letters read the plan's seats at Zp.D (the public part's declared rounds: pseats := planSeats Zp Zp.D.1 · pseatsAll); what the laid value pins, and what the pieces' rounds are tiled from, are THE DESCRIPTION's: (F0T o Zp Np cF).roundsDeclaredByBlocks: the sub-protocols' own rounds in a row. "That these two are one is said by nothing here" (a reader's B; our own old debt).
  LaidAt.decl: (F0T o Zp Np cF).roundsDeclaredByBlocks = Zp.D: the landed decl_of_planOk (an accept of the tests on the plan gives roundsDeclaredByBlocks = plans), and the seated description is made with plans := Zp.D (by unfolding).
  LaidAt.decl₁: the first chain's: cF.blocksInOrder.flatMap (·.rounds) = Zp.D.1.
Limits. An equation. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.LaidOpens
import Johnson.Desc.Sound.ReadsOkProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)

variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The description's declared rounds are the public part's.** -/
theorem LaidAt.decl (L : LaidAt o pol lay KL D r Zp Np cF) : (F0T o Zp Np cF).roundsDeclaredByBlocks = Zp.D :=
  VerifiableInference.Desc.Sound.decl_of_planOk (F0T o Zp Np cF) L.planOk

/-- The first chain's. -/
theorem LaidAt.decl₁ (L : LaidAt o pol lay KL D r Zp Np cF) :
    cF.blocksInOrder.flatMap (·.rounds) = Zp.D.1 := congrArg Prod.fst L.decl

end P5J

#print axioms P5J.LaidAt.decl
#print axioms P5J.LaidAt.decl₁
