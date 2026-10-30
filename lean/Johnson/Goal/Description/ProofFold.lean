-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/ProofFold.lean: the proof file's seat: its rounds' data and its decision.
One
named part of `VerifierAndGoals.theDescription` (Description.lean), in a file of its own.
`proofDataAndDecisionOrRefusalAt o`: THE SEAT: of the three public files alone, the data and the decision, or words;
o stands in the second hash function's place. `theProofDataAt o`, `theProofRunAt o`: its two parts;
where it refuses, the data of three empty lists and the decision that says no to all; `protocolDataWellFormedAt o`
(Live.lean) says no there. `theProofLaid`, `theProofData`, `theProofRun`: these at the format's
second
hash function: the names of which the laws speak.
State: a description's own. In the seat sits `LPFD.Full.proofDataAndDecisionOfPublicFiles` (Johnson/Desc/Laid/ProofFull.lean)
at o
and the three public files: the description that `ProofFile.onlineDescription o` makes of them
(Johnson/Desc/ProofFile/OnlineDescription.lean), with its tests on the plan and the tests of `LPFD.lawsAsk`
(Johnson/Desc/Laid/ProofAsks.lean) asked; its own data; its own run at the instance written of the
request and the entry's record. No decision of the program `verify-on-bytes` stands in it, and no
law on it is imported here.
Limits. The full size alone. Under the frame no digest of the public files can be handed in: the
description's plan stands at a constant (Johnson/Desc/TheCfg.lean). That the proof is bound to the
files' digest is the compiler's side's matter. The description's tests `wantedOk` and `owedOk` are
not asked here, and could not bite: that description lays both lists empty
(Johnson/Desc/ProofFile/Frames1.lean). What has been run with this value is not said here.

-/
import Johnson.Goal.Tie.DescriptionOfData
import Johnson.Desc.Laid.ProofFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Run
open _root_.Iop (Dig)
open LPFD.Full (XF GF sBG sTG saltG KF FsAtR)
open PV.EntryFive (dsF xsF)

/-- **The proof file's seat**, at a function o in the second hash function's place. -/
def proofDataAndDecisionOrRefusalAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) :
    Except String (WholeD × (XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)) :=
  LPFD.Full.proofDataAndDecisionOfPublicFiles o Zk.pol Zk.lay Zk.KL

def theProofDataAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) : WholeD :=
  match proofDataAndDecisionOrRefusalAt o Zk with
  | .ok p => p.1
  | .error _ => FlashProve.emptyRoundsData

def theProofRunAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) : XF × RecFull → PQ.View → PQ.View →
    PQ.View → Bool :=
  match proofDataAndDecisionOrRefusalAt o Zk with
  | .ok p => p.2
  | .error _ => fun _ _ _ _ => false

theorem theProofDataAt_ok {o : VerifierAndGoals.SecondHashFunctionType} {Zk : OnBytes.K.Pub}
    {p : WholeD × (XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)}
    (h : proofDataAndDecisionOrRefusalAt o Zk = .ok p) : theProofDataAt o Zk = p.1 := by
  unfold theProofDataAt
  rw [h]

theorem theProofRunAt_ok {o : VerifierAndGoals.SecondHashFunctionType} {Zk : OnBytes.K.Pub}
    {p : WholeD × (XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)}
    (h : proofDataAndDecisionOrRefusalAt o Zk = .ok p) : theProofRunAt o Zk = p.2 := by
  unfold theProofRunAt
  rw [h]

/-- The seat at the second hash function. -/
def theProofLaid (Zk : OnBytes.K.Pub) :
    Except String (WholeD × (XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)) :=
  proofDataAndDecisionOrRefusalAt OnBytes.secondHashFunction Zk

def theProofData (Zk : OnBytes.K.Pub) : WholeD := theProofDataAt OnBytes.secondHashFunction Zk

def theProofRun (Zk : OnBytes.K.Pub) : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool :=
  theProofRunAt OnBytes.secondHashFunction Zk

theorem theProofData_ok {Zk : OnBytes.K.Pub}
    {p : WholeD × (XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)}
    (h : theProofLaid Zk = .ok p) : theProofData Zk = p.1 := theProofDataAt_ok h

theorem theProofRun_ok {Zk : OnBytes.K.Pub}
    {p : WholeD × (XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)}
    (h : theProofLaid Zk = .ok p) : theProofRun Zk = p.2 := theProofRunAt_ok h

end FlashProve
