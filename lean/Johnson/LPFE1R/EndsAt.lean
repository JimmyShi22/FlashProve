-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/EndsAt.lean: OF THE FIVE NAMED TESTS IN FRONT OF THE HEAD AT THE NAME (`At.Five`,
Johnson/P5J/TestsAtRun.lean) ONE FOLLOWS FROM "LAID": `At.endsThere` (Johnson/P5J/GroupsPaid.lean; =
PlanOk's "groups", by its groups_is). One definition, three theorems. A law file; no running text
imports it.

  `At.ends_at`      LaidAt o pol lay KL D r Zp Np cF ⊢ At.endsThere Zp cF = true: AT EVERY o, AT
                    EVERY THREE PUBLIC FILES: NO SCOPE, NO WRITTEN VALUE, NO PIN: by ends_of_plan
                    (Johnson/LPFE1R/ShapeTie.lean) at LaidAt's own fields "opened" and "planOk".
                    That the end of that theorem IS endsThere at dl := Zp.D.1 is by unfolding:
                    At.pseats Zp is planSeats Zp Zp.D.1; withRows and withTold turn neither index
                    nor w.
  `At.Four`         the five less endsThere.
  `At.five_of_four`, `At.tests_of_four`   so the four give the five under LaidAt; and At.Tests Z
                    from the four at whatever letters the laid value opens.

Limits. It shows none of the four. Nothing on soundness or on hiding.

-/
import Johnson.P5J.TestsAtRun
import Johnson.LPFE1R.ShapeTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open VerifierAndGoals (asDescriptionFiles)
open FlashProve (theProofRun)
open VerifierAndGoals.AtTheName (dpZ)

/-- **endsThere follows from "laid".** -/
theorem At.ends_at {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (L : LaidAt o pol lay KL D r Zp Np cF) : At.endsThere Zp cF = true := by
  obtain ⟨Bs, base, O⟩ := L.opened
  exact VerifiableInference.Desc.LinkJoin.ends_of_plan O L.planOk Zp.D.1

/-- The five named tests less endsThere, at letters. -/
def At.Four (Z : VerifierAndGoals.PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) : Prop :=
  Meaning.namedThere (At.X Zp) (Meaning.sizesOf (At.X Zp)) (At.layout Zp) = true ∧
  seatsNamedC (At.X Zp) (Meaning.sizesOf (At.X Zp)) (At.layout Zp) (At.num Zp) (At.arr Zp)
    (At.N Zp cF) = true ∧
  P5T.seatsFitP (F0T OnBytes.secondHashFunction Zp Np cF) (At.cs Zp) (At.pseats Zp) = true ∧
  P5T.radIsB ((P5T.rowsAt? Zp.pol Z.lay Zp.KL).getD []) Zp.made.proof.1.sends.length
    (At.rad Zp Z.lay) (At.pseats Zp) = true

/-- Under "laid" the four give the five. -/
theorem At.five_of_four {Z : VerifierAndGoals.PublicFiles} {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (L : LaidAt o pol lay KL D r Zp Np cF) (T : At.Four Z Zp Np cF) : At.Five Z Zp Np cF :=
  ⟨T.1, T.2.1, T.2.2.1, At.ends_at L, T.2.2.2⟩

/-- **The head's premise from the four.** -/
theorem At.tests_of_four {Z : VerifierAndGoals.PublicFiles}
    (T : ∀ Zp Np cF, LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np
      cF → At.Four Z Zp Np cF) : At.Tests Z :=
  fun Zp Np cF L => At.five_of_four L (T Zp Np cF L)

end P5J

#print axioms P5J.At.ends_at
#print axioms P5J.At.five_of_four
#print axioms P5J.At.tests_of_four
