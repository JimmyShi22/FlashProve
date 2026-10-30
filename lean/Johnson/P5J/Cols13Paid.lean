-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/Cols13Paid.lean: AtMgA's field cols13 (Johnson/P5J/MgAtAll.lean) is a theorem under the
head AtMg: in scope, where the proof file's value is laid. Five theorems.


Why. cols13 speaks of (At.P13 Zp).lin, the shape of the test on the committed table as it is READ
BACK from the first chain's parameter bytes. The test fullShapeB is a theorem in scope at the shape
as it is SIZED (Lk6.AtPlan.fullShape_pub). That the two shapes are one is no rfl: another file has
shown it (P2R0.lin_sized) from two premises: the public part is the plain road's, and the test at
the shared chain's front (OkD.AtC.front2) accepts; and that this test is a clause of the tests on
the list of rounds of the IOP as written in Lean (P2R0.front2_at_planOk). LaidAt holds both.
  front2_of_laid: LaidAt … Zp Np cF → OkD.AtC.front2 Zp.p.chains = true: P2R0.front2_at_planOk at
      the seated term F0T.
  linOne: **LaidAt … Zp Np cF → Zp.first.lin = Zp.p.chains.made.sized.proof.batch.shape**: at every
      o, at all files: no scope, no pin, no bound on a size. P2R0.lin_sized under LaidAt.
  fullShape13: in scope, under LaidAt at Z's own three files: fullShapeB (At.P13 Zp).lin = true.
  cols13_paid: so 2 ^ (At.P13 Zp).lin.kCol = colsAt numsFull: THE FIELD's OWN LETTERS
      (At.cols13_of).
  AtMg.cols13: the same from the head alone: its fields scope and laid.

Limits. It reads a clause off a yes that is handed in (LaidAt's planOk): it pays nothing toward that
yes. That LaidAt, or AtMg, can be met is not shown here. fullShape13 and what follows: the full size
alone. Nothing on soundness, on an honest prover or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.AtMg
import Johnson.P5J.Cols13
import Johnson.Goal.PlanValues.ProofShapeAtPlain
import Johnson.P2R0R.SizedIsRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)

variable {o : ProofFile.SecondHashFunctionArgument} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl}

/-- Where the value is laid, the test at the shared chain's front has accepted. -/
theorem front2_of_laid {pol lay KL : ByteArray} (L : LaidAt o pol lay KL D r Zp Np cF) :
    VerifiableInference.OnPublicFiles.OkD.AtC.front2 Zp.p.chains = true :=
  P2R0.front2_at_planOk _ _ _ _ _ _ _ _ _ _ _ _ _ L.planOk

/-- **Where the value is laid, the first chain's shape of the test on the committed table, as read
back, is the shape as sized.** -/
theorem linOne {pol lay KL : ByteArray} (L : LaidAt o pol lay KL D r Zp Np cF) :
    Zp.first.lin = Zp.p.chains.made.sized.proof.batch.shape :=
  P2R0.lin_sized L.pub (front2_of_laid L)

variable {Z : VerifierAndGoals.PublicFiles}

/-- In scope, where the value is laid, the shape as read back passes the one test on a shape. -/
theorem fullShape13 (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) :
    Desc.K14.Law.fullShapeB (At.P13 Zp).lin = true := by
  show Desc.K14.Law.fullShapeB Zp.first.lin = true
  rw [linOne L]
  exact Lk6.AtPlan.fullShape_pub hZ L.pub

/-- **AtMgA's field cols13, in its own letters.** -/
theorem cols13_paid (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) :
    2 ^ (At.P13 Zp).lin.kCol = colsAt OnBytes.Flat.numsFull :=
  At.cols13_of Zp (fullShape13 hZ L)

/-- **The same from the head alone.** -/
theorem AtMg.cols13 (h : AtMg o Z D r Zp Np cF) :
    2 ^ (At.P13 Zp).lin.kCol = colsAt OnBytes.Flat.numsFull :=
  cols13_paid h.scope h.laid

end P5J

#print axioms P5J.front2_of_laid
#print axioms P5J.linOne
#print axioms P5J.fullShape13
#print axioms P5J.cols13_paid
#print axioms P5J.AtMg.cols13
