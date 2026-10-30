-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/Gates.lean: the three decisions behind the test. One named part of
`VerifierAndGoals.theDescription` (Description.lean), in a file of its own.
State: the true text, over whatever sits in the seats. `theKeyGateAt o`, `theProofGateAt o`,
`theLinkGateAt o`: where `protocolDataWellFormedAt o` says no, each says no to all. `theKeyGate`, `theProofGate`,
`theLinkGate`: these at the second hash function; `theKeyGate_live`, `theProofGate_live`,
`theLinkGate_live`: where `protocolDataWellFormed` says yes, each is the decision itself.

-/
import Johnson.Goal.Description.Live
import Johnson.Goal.Description.LinkDec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Run
open _root_.Iop (Dig)
open LPFD.Full (XF GF sBG sTG saltG KF FsAtR)
open PV.EntryFive (dsF xsF)

def theKeyGateAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) : RecFull → PQ.View → PQ.View → PQ.View →
    Bool :=
  gatedFileDecision (protocolDataWellFormedAt o Zk) (theKeyRunAt o Zk)

def theProofGateAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) : XF × RecFull → PQ.View → PQ.View →
    PQ.View → Bool :=
  gatedFileDecision (protocolDataWellFormedAt o Zk) (theProofRunAt o Zk)

def theLinkGateAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) : RecFull × RecFull → PQ.View → Bool :=
  gatedLinkDecision (protocolDataWellFormedAt o Zk) (linkDecisionAtFiles Zk)

def theKeyGate (Zk : OnBytes.K.Pub) : RecFull → PQ.View → PQ.View → PQ.View → Bool := theKeyGateAt
    OnBytes.secondHashFunction Zk

def theProofGate (Zk : OnBytes.K.Pub) : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool :=
    theProofGateAt OnBytes.secondHashFunction Zk

def theLinkGate (Zk : OnBytes.K.Pub) : RecFull × RecFull → PQ.View → Bool :=
  theLinkGateAt OnBytes.secondHashFunction Zk

theorem theKeyGate_live (Zk : OnBytes.K.Pub) (h : protocolDataWellFormed Zk = true) :
    theKeyGate Zk = theKeyRun Zk := by
  show gatedFileDecision (protocolDataWellFormed Zk) (theKeyRun Zk) = theKeyRun Zk
  rw [h]; rfl

theorem theProofGate_live (Zk : OnBytes.K.Pub) (h : protocolDataWellFormed Zk = true) :
    theProofGate Zk = theProofRun Zk := by
  show gatedFileDecision (protocolDataWellFormed Zk) (theProofRun Zk) = theProofRun Zk
  rw [h]; rfl

theorem theLinkGate_live (Zk : OnBytes.K.Pub) (h : protocolDataWellFormed Zk = true) :
    theLinkGate Zk = linkDecisionAtFiles Zk := by
  show gatedLinkDecision (protocolDataWellFormed Zk) (linkDecisionAtFiles Zk) = linkDecisionAtFiles Zk
  rw [h]; rfl

end FlashProve
