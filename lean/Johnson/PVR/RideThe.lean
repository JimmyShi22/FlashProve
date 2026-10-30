-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PVR/RideThe.lean: the run of Johnson/PVR/RideAll.lean at the parameters of
`FlashProve.flashProveData` (Johnson/Goal/Description/). `letsThe`, `shares_the`: the eight parameters,
which `flashProveData` has by `rfl`. `letsPlanPlan`, `shares_planPlan`: the three decisions without the
test `protocolDataWellFormed` in front; `flashProveData` has them where `protocolDataWellFormed` accepts. `verdictThe`: the verdict of
`verdictFrom`, and reject where the public files are in scope and `protocolDataWellFormed` rejects them.
`tell3`, `tell1`, `letsTell`, `shares_tell`: the same eight with the three decisions reporting, on
the error stream, that they were reached and what they answered; equal to the plain ones by `rfl`.
`verdictThe_of_shares`, `verdictThe_is_theDescription`, `verdictTell_is_theDescription`: whatever
verdict is given is
`(VerifierAndGoals.verify (atSecondHashFunction theDescription) Z ‹its own parser› commitment prompt output B).evaluate
(hashOf O)`.
Limits. No soundness: the theorem says that the term that runs and `VerifierAndGoals.verify` give one answer.
What `theDescription` holds, and which of its parts are placeholders, its own files say. At the
description's own parser alone. Where `verdictThe` gives `none` nothing is said. This file is a port
of another file (not in this library), without the
variant at which the second hash function reports its calls, without the negative test's variant
whose three decisions always accept, and without its closing prints: these stay in that file. The
definitions and proofs that stay are unchanged but for line breaks. A reference run,
over a set of this project's Lean files, rode that file and another (not in this
library): the tie from that run's print to these theorems is by name and statement, not by bytes.

-/
import Johnson.PVR.RideAll
import Johnson.Goal.Description.Dead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PV.Ride
open VerifierAndGoals FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.Tie OnBytes.RunA
open _root_.Run
open PV.Head (cThru sevenThru)

/-- The eight parameters of `FlashProve.flashProveData`. -/
def letsThe : Lets where
  DK := theKeyData
  DP := theProofData
  runK := theKeyGate
  runP := theProofGate
  dec := theLinkGate
  live := protocolDataWellFormed
  G := thePlan
  it := theItem

theorem shares_the (Z : PublicFiles) : Shares letsThe flashProveData Z := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The whole term that runs, as one constant: `rideOf` at `letsThe`. -/
abbrev rideThe := rideOf letsThe

/-- A decision that reports, on the error stream, that it was reached and what it answered.
`dbgTrace s f` is `f ()` by its definition, so the reporting decision is the decision
(`shares_tell`: `rfl`). -/
def tell3 {α : Type} (name : String) (d : α → PQ.View → PQ.View → PQ.View → Bool) : α → PQ.View →
    PQ.View → PQ.View → Bool :=
  fun a u v w => dbgTrace s!"DECISION|{name}|reached|it answers {if d a u v w then "yes" else "no"}"
      fun _ => d a u v w
def tell1 {α : Type} (name : String) (d : α → PQ.View → Bool) : α → PQ.View → Bool :=
  fun a v => dbgTrace s!"DECISION|{name}|reached|it answers {if d a v then "yes" else "no"}" fun _
      => d a v

/-- `letsThe` with the three decisions reporting. Each decision is evaluated twice where it is
reached: once for the word, once for the answer. -/
def letsTell : Lets where
  DK := theKeyData
  DP := theProofData
  runK := fun Zk => tell3 "the key file's (theKeyGate)" (theKeyGate Zk)
  runP := fun Zk => tell3 "the proof file's (theProofGate)" (theProofGate Zk)
  dec := fun Zk => tell1 "the entry file's (theLinkGate)" (theLinkGate Zk)
  live := protocolDataWellFormed
  G := thePlan
  it := theItem

theorem shares_tell (Z : PublicFiles) : Shares letsTell flashProveData Z := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The whole term that runs where the decisions report. -/
abbrev rideTell := rideOf letsTell

/-- The same with the three decisions taken without the test in front of them. -/
def letsPlanPlan : Lets where
  DK := theKeyData
  DP := theProofData
  runK := theKeyRun
  runP := theProofRun
  dec := linkDecisionAtFiles
  live := protocolDataWellFormed
  G := thePlan
  it := theItem

/-- `flashProveData` has them where `protocolDataWellFormed` accepts the public files. -/
theorem shares_planPlan (Z : PublicFiles) (h : protocolDataWellFormed (asDescriptionFiles Z) = true) : Shares letsPlanPlan flashProveData Z :=
  ⟨rfl, rfl, theKeyGate_live (asDescriptionFiles Z) h, theProofGate_live (asDescriptionFiles Z) h, theLinkGate_live
      (asDescriptionFiles Z) h, rfl, rfl, rfl⟩

/-- The verdict at `theDescription`: that of `verdictFrom`, and reject where the public files are in
scope and `protocolDataWellFormed` rejects them (`theDescription_dead`). -/
def verdictThe (Z : PublicFiles) (O : ByteArray → ByteArray) (B : FormBytes) (r : Except String FastSteps) :
    Option Bool :=
  if InScope Z = true && protocolDataWellFormed (asDescriptionFiles Z) = false then
    if (decide ((cThru O (asDescriptionFiles Z)).size = 32) &&
        ((sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z))).all fun b => decide (b.size =
                                  32))) = true then some false else none
  else verdictFrom Z O B r

/-- Whatever verdict is given is that of `VerifierAndGoals.verify` at `atSecondHashFunction theDescription`, for every `ℓ`
whose parameters are `flashProveData`'s at these public files. -/
theorem verdictThe_of_shares (ℓ : Lets) (Z : PublicFiles) (sh : Shares ℓ flashProveData Z) (O : ByteArray →
                    ByteArray) (B : FormBytes)
    (commitment : Commitment) (prompt output : List Token) (b : Bool)
    (h : verdictThe Z O B (rideOf ℓ Z O B commitment prompt output) = some b) :
    b = (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z ((atSecondHashFunction theDescription).parse Z) commitment
        prompt output B).evaluate (hashOf O) := by
  unfold verdictThe at h
  split at h
  · rename_i hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
      exact (theDescription_dead Z hd.1 hd.2 O hc.1 hc.2 commitment prompt output B).symm
    · cases h
  · exact atName (P := fun more L => b = (VerifierAndGoals.verify (descriptionOfDataWithReading more L) Z ((descriptionOfDataWithReading more
                      L).parse Z) commitment prompt output B).evaluate (hashOf O))
      (verdictFrom_is_verify ℓ flashProveData Z sh O B commitment prompt output b h)

/-- The instance at `letsThe`. -/
theorem verdictThe_is_theDescription (Z : PublicFiles) (O : ByteArray → ByteArray) (B : FormBytes)
    (commitment : Commitment) (prompt output : List Token) (b : Bool)
    (h : verdictThe Z O B (rideOf letsThe Z O B commitment prompt output) = some b) :
    b = (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z ((atSecondHashFunction theDescription).parse Z) commitment
        prompt output B).evaluate (hashOf O) :=
  verdictThe_of_shares letsThe Z (shares_the Z) O B commitment prompt output b h

/-- The same where the three decisions report. -/
theorem verdictTell_is_theDescription (Z : PublicFiles) (O : ByteArray → ByteArray) (B : FormBytes)
    (commitment : Commitment) (prompt output : List Token) (b : Bool)
    (h : verdictThe Z O B (rideOf letsTell Z O B commitment prompt output) = some b) :
    b = (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z ((atSecondHashFunction theDescription).parse Z) commitment
        prompt output B).evaluate (hashOf O) :=
  verdictThe_of_shares letsTell Z (shares_tell Z) O B commitment prompt output b h

end PV.Ride
