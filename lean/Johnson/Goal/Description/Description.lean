-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/Description.lean: `VerifierAndGoals.theDescription`: one closed term with a name.
`theDescriptionO`: the description as a function of what stands in the second hash function's
place: at o: the built D* at the letters `flashProveDataAtSecondHash o` (Lay.lean) and at the further public reading
`VerifierAndGoals.readMoreAtO o` (Johnson/Goal/Reads/ReadAtSecondHashFunction.lean). `theDescription` is that function: it
names no hash function; the goals hand it the format's second one (`VerifierAndGoals.atSecondHashFunction`).
`theDescription_eq`: there it is the built D* at `flashProveData` and the further reading
`VerifierAndGoals.readMoreAt`: a theorem; `atName` carries a law from there to the name.
`theDescription_tie`: a run's call at the plan, the item and the five letters of `flashProveData` and the
format's own hash is the value of its verify. `theDescription_refused`: where the decoders refuse it
is false.
`theDescription_out`: out of the goals' scope it is false. `theDescription_within`: its own parser
asks once. `call_congr`: equal decisions, one call.
Limits. What sits in the three seats is told in KeyFold.lean, ProofFold.lean and LinkDec.lean: as
long as one of them holds a place-holder this is the description by name alone. The provers and the
honest side are hollow. That the three
hypotheses on soundness (AtName.lean) all hold at it is not shown here; where they are proved, and
how far: the head of Johnson/Goal/TopOfThree.lean, limit (1). The tie and the law on
the decoders' refusal stand at `atSecondHashFunction theDescription` alone: they speak of the letters' names
without o (`protocolDataWellFormed`, `thePlan`, …), which are the letters at `OnBytes.secondHashFunction` by definition. No
soundness is claimed.

-/
import Johnson.Goal.Description.Lay
import Johnson.Goal.Tie.TieWhole
import Johnson.Goal.Reads.ReadAtSecondHashFunction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Tie
open PV.Head (cThru sevenThru)
open FlashProve FlashProve

/- Lean compares these names and does not open them. -/
attribute [local irreducible] protocolDataWellFormed theKeyData theProofData theKeyRun theProofRun linkDecisionAtFiles
    theKeyGate theProofGate
  theLinkGate theDeadPlan theClaims theCoding theProvers theNamed
  FlashProve.thePlan FlashProve.theItem

/-- **The description, reading its argument.** -/
def theDescriptionO : SecondHashFunctionType → Description := fun o =>
  descriptionOfDataWithReading (fun Z c => readMoreAtO o recordGround Z c) (flashProveDataAtSecondHash o)

theorem theDescriptionO_eq (o : SecondHashFunctionType) : theDescriptionO o =
    descriptionOfDataWithReading (fun Z c => readMoreAtO o recordGround Z c) (flashProveDataAtSecondHash o) := rfl

/-- **The description.** It reads its argument: the goals hand it the second hash
function (`VerifierAndGoals.atSecondHashFunction`). -/
def theDescription : SecondHashFunctionType → Description := theDescriptionO

/-- At the second hash function the further reading is `readMoreAt`. -/
theorem readMoreAtO_older_fun :
    (fun (Z : PublicFiles) (c : Digest) => readMoreAtO OnBytes.secondHashFunction recordGround Z c) =
      fun Z c => readMoreAt recordGround Z c := by
  funext Z c
  rw [readMoreAtO_older]

/-- **From the further reading `readMoreAt` and `flashProveData` to the name's own two arguments.** -/
theorem atName
    {P : (PublicFiles → Digest → DeterministicAlgorithm (List (_root_.Iop.Dig 256))) → DescriptionData → Prop}
    (h : P (fun Z c => readMoreAt recordGround Z c) flashProveData) :
    P (fun Z c => readMoreAtO OnBytes.secondHashFunction recordGround Z c) (flashProveDataAtSecondHash OnBytes.secondHashFunction) := by
  rw [readMoreAtO_older_fun, theLayAt_older]
  exact h

theorem theDescription_eq : atSecondHashFunction theDescription = descriptionOfDataOnBytes flashProveData :=
  atName (P := fun more L => descriptionOfDataWithReading more L = descriptionOfDataOnBytes flashProveData) (descriptionOfDataOnBytes_eq_descriptionOfDataWithReading flashProveData).symm

/-- What holds of the built D* at `flashProveData` holds of the description where the goals read it. -/
theorem ofBuilt {Q : Description → Prop} (h : Q (descriptionOfDataOnBytes flashProveData)) :
    Q (atSecondHashFunction theDescription) := theDescription_eq.symm ▸ h

/-- The built D*'s own parser asks once, at every further reading and every record of letters:
stated at letters, then called, so that Lean does not open the values. -/
theorem dStarBuiltBy_within
    (more : PublicFiles → Digest → DeterministicAlgorithm (List (_root_.Iop.Dig 256))) (L : DescriptionData) (Z : PublicFiles) :
    Parser.Within ((descriptionOfDataWithReading more L).parse Z) 1 := descriptionOfDataOnBytes_within L Z

/-- Its own parser asks once. -/
theorem theDescription_within (o : SecondHashFunctionType) (Z : PublicFiles) : Parser.Within ((theDescription o).parse Z) 1
    :=
  dStarBuiltBy_within (fun Z c => readMoreAtO o recordGround Z c) (flashProveDataAtSecondHash o) Z

/-- The call at letters: equal decisions, one call. Stated at letters, then called, so that Lean
  does not open the values. -/
theorem call_congr {rK rK' : OnBytes.Flat.RecFull → _root_.Run.PQ.View → _root_.Run.PQ.View →
    _root_.Run.PQ.View → Bool}
    {rP rP' : LPFD.Full.XF × OnBytes.Flat.RecFull → _root_.Run.PQ.View → _root_.Run.PQ.View →
        _root_.Run.PQ.View → Bool}
    {d d' : OnBytes.Flat.RecFull × OnBytes.Flat.RecFull → _root_.Run.PQ.View → Bool} (e1 : rK =
        rK') (e2 : rP = rP')
    (e3 : d = d') (G : OnBytes.Flat.FilesParameters LPFD.Full.XF OnBytes.Flat.RecFull)
    (sp : LPFD.Full.XF → ByteArray × ByteArray) (O :
        ByteArray → ByteArray) (c : ByteArray) (seven : List
        ByteArray)
    (DK DP : OnBytes.Maker.WholeD) (commitment : Commitment) (prompt output : List Token) (f :
        DecodedProof) :
    PV.RunPure.Full.stepsFullAllAt {} G sp O c seven DK DP rK rP d commitment prompt output f.aux
        f.cm f.rcd f.copy f.fT f.e
        f.fB =
      PV.RunPure.Full.stepsFullAllAt {} G sp O c seven DK DP rK' rP' d' commitment prompt output
          f.aux f.cm f.rcd f.copy f.fT
        f.e f.fB := by
  subst e1 e2 e3
  rfl

/-- The tie at the built D* at `flashProveData` and the further reading `readMoreAt`. -/
theorem theBuilt_tie (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true) (live : protocolDataWellFormed
            (asDescriptionFiles Z) = true)
    (B : FormBytes) (commitment : Commitment) (prompt output : List Token) (f : DecodedProof)
    (hf : decodeD (cThru _root_.Fmt.oracle (asDescriptionFiles Z)) B = some f) (s : FastSteps)
    (hs : PV.RunPure.Full.stepsFullAllAt {} (thePlan (asDescriptionFiles Z))
      (PV.MFull.spI (theItem (asDescriptionFiles Z))) _root_.Fmt.oracle
      (cThru _root_.Fmt.oracle (asDescriptionFiles Z))
      (sevenThru _root_.Fmt.oracle recordGround (asDescriptionFiles Z) (cThru _root_.Fmt.oracle (asDescriptionFiles Z)))
      (theKeyData (asDescriptionFiles Z)) (theProofData (asDescriptionFiles Z)) (theKeyRun (asDescriptionFiles Z)) (theProofRun
                                           (asDescriptionFiles Z))
      (linkDecisionAtFiles (asDescriptionFiles Z)) commitment prompt output f.aux f.cm f.rcd f.copy f.fT f.e f.fB =
          some s) :
    s.yes =
      (VerifierAndGoals.verify (descriptionOfDataOnBytes flashProveData) Z ((descriptionOfDataOnBytes flashProveData).parse Z) commitment prompt output
          B).evaluate
        (hashOf _root_.Fmt.oracle) :=
  tie_tenth_oracle flashProveData Z scope live B commitment prompt output f hf s
    ((call_congr (theKeyGate_live _ live) (theProofGate_live _ live) (theLinkGate_live _ live) _ _ _
        _ _ _ _ commitment prompt
      output f).trans hs)

/-- **A run's call, at the plan, the item, these five letters and the format's own hash, is its
verify.** -/
theorem theDescription_tie (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true) (live : protocolDataWellFormed
            (asDescriptionFiles Z) = true)
    (B : FormBytes) (commitment : Commitment) (prompt output : List Token) (f : DecodedProof)
    (hf : decodeD (cThru _root_.Fmt.oracle (asDescriptionFiles Z)) B = some f) (s : FastSteps)
    (hs : PV.RunPure.Full.stepsFullAllAt {} (thePlan (asDescriptionFiles Z))
      (PV.MFull.spI (theItem (asDescriptionFiles Z))) _root_.Fmt.oracle
      (cThru _root_.Fmt.oracle (asDescriptionFiles Z))
      (sevenThru _root_.Fmt.oracle recordGround (asDescriptionFiles Z) (cThru _root_.Fmt.oracle (asDescriptionFiles Z)))
      (theKeyData (asDescriptionFiles Z)) (theProofData (asDescriptionFiles Z)) (theKeyRun (asDescriptionFiles Z)) (theProofRun
                                           (asDescriptionFiles Z))
      (linkDecisionAtFiles (asDescriptionFiles Z)) commitment prompt output f.aux f.cm f.rcd f.copy f.fT f.e f.fB =
          some s) :
    s.yes =
      (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z ((atSecondHashFunction theDescription).parse Z) commitment
          prompt output B).evaluate
        (hashOf _root_.Fmt.oracle) :=
  atName (P := fun more L => s.yes = (VerifierAndGoals.verify (descriptionOfDataWithReading more L) Z
      ((descriptionOfDataWithReading more L).parse Z) commitment prompt output B).evaluate
        (hashOf _root_.Fmt.oracle))
    (theBuilt_tie Z scope live B commitment prompt output f hf s hs)

/-- The same at the built D* at `flashProveData` and the further reading `readMoreAt`. -/
theorem theBuilt_refused (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true) (B : FormBytes)
    (commitment : Commitment) (prompt output : List Token)
    (hdec : decodeD (cThru _root_.Fmt.oracle (asDescriptionFiles Z)) B = none) :
    (VerifierAndGoals.verify (descriptionOfDataOnBytes flashProveData) Z ((descriptionOfDataOnBytes flashProveData).parse Z) commitment prompt output
        B).evaluate (hashOf _root_.Fmt.oracle) = false :=
  verify_descriptionOfDataOnBytes_refused flashProveData Z scope _root_.Fmt.oracle (size_cThru _ _root_.Fmt.size_oracle _)
    (size_sevenThru _ _root_.Fmt.size_oracle _ _ _) commitment prompt output B hdec

/-- Where the decoders refuse it says no. -/
theorem theDescription_refused (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true) (B :
            FormBytes)
    (commitment : Commitment) (prompt output : List Token)
    (hdec : decodeD (cThru _root_.Fmt.oracle (asDescriptionFiles Z)) B = none) :
    (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z ((atSecondHashFunction theDescription).parse Z) commitment prompt
        output B).evaluate
        (hashOf _root_.Fmt.oracle) = false :=
  atName (P := fun more L => (VerifierAndGoals.verify (descriptionOfDataWithReading more L) Z ((descriptionOfDataWithReading more L).parse Z)
      commitment prompt output B).evaluate (hashOf _root_.Fmt.oracle) = false)
    (theBuilt_refused Z scope B commitment prompt output hdec)

/-- Out of the goals' scope it says no. -/
theorem theDescription_out (o : SecondHashFunctionType) (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = false) (hash :
                             VerifiableInference.Hash)
    (B : FormBytes) (commitment : Commitment) (prompt output : List Token) :
    (VerifierAndGoals.verify (theDescription o) Z ((theDescription o).parse Z) commitment prompt output
        B).evaluate hash = false :=
  verify_evaluate_out (theDescription o) Z _ scope hash commitment prompt output B

end VerifierAndGoals
