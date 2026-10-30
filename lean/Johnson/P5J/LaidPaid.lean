-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/LaidPaid.lean: THE NAMED TEST "laid" OF PlanOk (laidThere: it walks every element of every matrix's array: it cannot be evaluated at the full size) FROM A TEST THAT WALKS ONCE A MATRIX: namedThere. Two theorems. A joint build of files of several kinds.
  At.laid_paid: from LaidAt (at every SecondHashFunctionArgument o) and namedThere X (sizesOf X) layout = true: laidThere X (sizesOf X) layout = true: Meaning.laidThere_of_named (Johnson/Goal/Meaning/LaidCovered.lean), whose premise reqLayoutOk codes shape layout holds wherever the maker of the IOP as written returns (three_at_pure, Johnson/P5J/InsideAtPure.lean).
  At.PlanOk.of_tests: SO PlanOk FOLLOWS, IN SCOPE, AT OnBytes.secondHashFunction, FROM LaidAt AND FIVE TESTS: namedThere · named · fit · groups · radii.
Limits. It shows none of the five to accept. The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.PlacesPaid
import Johnson.P5J.InsideAtPure
import Johnson.Goal.Meaning.LaidCovered

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)

/-- **"laid" from the test that walks once a matrix.** -/
theorem laid_paid {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} (L : LaidAt o pol lay KL D r Zp Np cF)
    (T : Meaning.namedThere (X Zp) (Meaning.sizesOf (X Zp)) (layout Zp) = true) :
    Meaning.laidThere (X Zp) (Meaning.sizesOf (X Zp)) (layout Zp) = true := by
  obtain ⟨Z, hZ, -, -, hL⟩ := three_at_pure L.value
  have e : Z = Zp := Except.ok.inj (hZ.symm.trans L.pub)
  subst e
  exact Meaning.laidThere_of_named hL T

/-- **PlanOk from LaidAt and five tests, in scope; none walks an array's elements.** -/
theorem PlanOk.of_tests {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (there : Meaning.namedThere (X Zp) (Meaning.sizesOf (X Zp)) (layout Zp) = true)
    (named : seatsNamedC (X Zp) (Meaning.sizesOf (X Zp)) (layout Zp) (num Zp) (arr Zp) (N Zp cF) = true)
    (fit : P5T.seatsFitP (F0T OnBytes.secondHashFunction Zp Np cF) (cs Zp) (pseats Zp) = true)
    (groups : P5T.groupsP (N Zp cF) (nG Zp) (pseats Zp) = true)
    (radii : P5T.radIsB ((P5T.rowsAt? Zp.pol Z.lay Zp.KL).getD []) Zp.made.proof.1.sends.length
      (rad Zp Z.lay) (pseats Zp) = true) :
    PlanOk OnBytes.secondHashFunction Zp Np cF Z.lay :=
  PlanOk.of_five hZ hR L (laid_paid L there) named fit groups radii

end P5J.At

#print axioms P5J.At.laid_paid
#print axioms P5J.At.PlanOk.of_tests
