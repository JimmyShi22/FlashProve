-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/AtName.lean: THE ONE HEAD (AtMg) AT THE NAME: at the goals' own description's own data and run of the proof file. Four theorems. A joint build of several files.

Why. The top statements are stated at VerifierAndGoals.theDescription: its proof file's data are dpZ Z := (dataAtFiles flashProveData Z).DP, its run theProofRun (asDescriptionFiles Z). The kinds' laws end at the constant under AtMg o Z D r Zp Np cF, D | r: letters. So that the two meet WITHOUT A LETTER BETWEEN:
  laid_at_name: where the description is live (protocolDataWellFormed (asDescriptionFiles Z) = true): LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok (theProofData (asDescriptionFiles Z), theProofRun (asDescriptionFiles Z)): the verifier's own value IS laid, and these two ARE what it lays.
  dpZ_live: there dpZ Z = theProofData (asDescriptionFiles Z).
  head_at_name: IN SCOPE, LIVE, WHERE readFiles RETURNS, AND WHERE THE FIVE NAMED TESTS ACCEPT AT WHATEVER LETTERS THE LAID VALUE OPENS: ∃ Zp Np cF, AtMg OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF.
  seat_at_name: under that head: theProofRun (asDescriptionFiles Z) = ((F0T …).pull instanceAsPlainRecord).run · (F0T …).data "proof file" = .ok (dpZ Z) · (F0T …).planOk = true: the three premises on the description in the skeleton's proofFileAt_of_tied (seat_proof_file · hD, at the depth by LaidAt's own data · hp).
Limits. The five tests are a premise, for all letters that the laid value opens (they are evaluated true at the release's own public files: a run, no theorem). At OnBytes.secondHashFunction. The full size alone. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/). Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.AtMg
import Johnson.P5J.GroupsPaid
import Johnson.Goal.Skeleton.ProofAtName

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open VerifierAndGoals (asDescriptionFiles)
open FlashProve (protocolDataWellFormed theProofData theProofRun theProofLaid)
open VerifierAndGoals.AtTheName (dpZ)

variable {Z : VerifierAndGoals.PublicFiles}

/-- **Live: the verifier's own value is laid, and the description's data and run are what it lays.** -/
theorem laid_at_name (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL =
      .ok (theProofData (asDescriptionFiles Z), theProofRun (asDescriptionFiles Z)) := by
  obtain ⟨K, P, -, -, hP, -⟩ := FlashProve.theLive_made (asDescriptionFiles Z) hl
  have e1 := FlashProve.theProofData_ok hP
  have e2 := FlashProve.theProofRun_ok hP
  rw [e1, e2]
  exact hP

/-- Live: the built description's data of the proof file are these. -/
theorem dpZ_live (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) : dpZ Z = theProofData (asDescriptionFiles Z) := by
  show (if protocolDataWellFormed (asDescriptionFiles Z) then theProofData (asDescriptionFiles Z) else FlashProve.emptyRoundsData) = _
  rw [hl]
  rfl

/-- **THE ONE HEAD AT THE NAME.** -/
theorem head_at_name (hZ : VerifierAndGoals.InScope Z = true) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (tests : ∀ Zp Np cF,
      LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF →
      Meaning.namedThere (At.X Zp) (Meaning.sizesOf (At.X Zp)) (At.layout Zp) = true ∧
      seatsNamedC (At.X Zp) (Meaning.sizesOf (At.X Zp)) (At.layout Zp) (At.num Zp) (At.arr Zp)
        (At.N Zp cF) = true ∧
      P5T.seatsFitP (F0T OnBytes.secondHashFunction Zp Np cF) (At.cs Zp) (At.pseats Zp) = true ∧
      At.endsThere Zp cF = true ∧
      P5T.radIsB ((P5T.rowsAt? Zp.pol Z.lay Zp.KL).getD []) Zp.made.proof.1.sends.length
        (At.rad Zp Z.lay) (At.pseats Zp) = true) :
    ∃ Zp Np cF, AtMg OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF := by
  have hL := laid_at_name hl
  rw [← dpZ_live hl] at hL
  refine AtMg.exists_of_laid hZ hR hL fun Zp Np cF L => ?_
  obtain ⟨t1, t2, t3, t4, t5⟩ := tests Zp Np cF L
  exact At.PlanOk.of_tests' hZ hR L t1 t2 t3 t4 t5

/-- **What the skeleton's joining theorem asks of the description, from the head.** -/
theorem seat_at_name {D : WholeD} {r : LPFD.Full.RunPF} {o : ProofFile.SecondHashFunctionArgument} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} (h : AtMg o Z D r Zp Np cF) :
    r = ((F0T o Zp Np cF).pull LPFD.Full.instanceAsPlainRecord).run ∧
      (F0T o Zp Np cF).data "proof file" = .ok D ∧ (F0T o Zp Np cF).planOk = true :=
  ⟨h.laid.run, h.laid.data, h.laid.planOk⟩

end P5J

#print axioms P5J.laid_at_name
#print axioms P5J.dpZ_live
#print axioms P5J.head_at_name
#print axioms P5J.seat_at_name
