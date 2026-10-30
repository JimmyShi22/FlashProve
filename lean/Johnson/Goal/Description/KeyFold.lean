-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/KeyFold.lean: the key file's seat: its rounds' data and its decision. One
named part of `VerifierAndGoals.theDescription` (Description.lean), in a file of its own.
`keyDataAndDecisionOrRefusalAt o`: THE SEAT: of the three public files alone, the data and the decision, or words;
o stands in the second hash function's place. `theKeyDataAt o`, `theKeyRunAt o`: its two parts;
where it refuses, the data of three empty lists and the decision that says no to all; `protocolDataWellFormedAt o`
(Live.lean) says no there. `theKeyLaid`, `theKeyData`, `theKeyRun`: these at the format's second
hash function: the names of which the laws speak.
State: a description's own. In the seat sits `VerifiableInference.Desc.Key.keyDataAndDecisionAtFixedDigest`
(Johnson/Desc/Key/Slot.lean) at what `publicOfO o` (Johnson/Desc/Ok/PlanWritten/PublicAt.lean) reads
of the public files, and at the layout file: the key file's description at the constant
`VerifiableInference.Desc.fixedConfigurationDigest` (Johnson/Desc/TheCfg.lean), with its tests on the plan, its two
tests `wantedOk` and `owedOk` and the tests of `Key.lawsAsk` (Johnson/Desc/Key/Asks.lean) asked; its
own data; its own run at the key written of the record. No decision of the program
`verify-on-bytes` stands in it, and no law on it is imported here.
Limits. The full size alone. Under the frame no digest of the public files can be handed in: the
description stands at a constant; its four clauses on the digest are idle by that make. That the
proof is bound to the files' digest is the compiler's side's matter. Nobody asks here that the
files' own digest is not 32 zero bytes. The description's parameter bytes are spelled at the
constant: no transcript may be started from them (Johnson/Desc/Key/Slot.lean says so). What has been
run with this value is not said here.

-/
import Johnson.Goal.Tie.DescriptionOfData
import Johnson.Desc.Key.Slot
import Johnson.Desc.Ok.PlanWritten.PublicAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Run
open _root_.Iop (Dig)
open LPFD.Full (XF GF sBG sTG saltG KF FsAtR)
open PV.EntryFive (dsF xsF)

/-- **The key file's seat**, at a function o in the second hash function's place. -/
def keyDataAndDecisionOrRefusalAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) :
    Except String (WholeD × (RecFull → PQ.View → PQ.View → PQ.View → Bool)) :=
  (VerifiableInference.PlanWritten.publicOfO o Zk.pol Zk.KL (some Zk.lay)).bind fun X =>
    VerifiableInference.Desc.Key.keyDataAndDecisionAtFixedDigest X Zk.lay

def theKeyDataAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) : WholeD :=
  match keyDataAndDecisionOrRefusalAt o Zk with
  | .ok p => p.1
  | .error _ => FlashProve.emptyRoundsData

def theKeyRunAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) : RecFull → PQ.View → PQ.View → PQ.View →
    Bool :=
  match keyDataAndDecisionOrRefusalAt o Zk with
  | .ok p => p.2
  | .error _ => fun _ _ _ _ => false

theorem theKeyDataAt_ok {o : VerifierAndGoals.SecondHashFunctionType} {Zk : OnBytes.K.Pub}
    {p : WholeD × (RecFull → PQ.View → PQ.View → PQ.View → Bool)}
    (h : keyDataAndDecisionOrRefusalAt o Zk = .ok p) : theKeyDataAt o Zk = p.1 := by
  unfold theKeyDataAt
  rw [h]

theorem theKeyRunAt_ok {o : VerifierAndGoals.SecondHashFunctionType} {Zk : OnBytes.K.Pub}
    {p : WholeD × (RecFull → PQ.View → PQ.View → PQ.View → Bool)}
    (h : keyDataAndDecisionOrRefusalAt o Zk = .ok p) : theKeyRunAt o Zk = p.2 := by
  unfold theKeyRunAt
  rw [h]

/-- The seat at the second hash function. -/
def theKeyLaid (Zk : OnBytes.K.Pub) :
    Except String (WholeD × (RecFull → PQ.View → PQ.View → PQ.View → Bool)) :=
  keyDataAndDecisionOrRefusalAt OnBytes.secondHashFunction Zk

def theKeyData (Zk : OnBytes.K.Pub) : WholeD := theKeyDataAt OnBytes.secondHashFunction Zk

def theKeyRun (Zk : OnBytes.K.Pub) : RecFull → PQ.View → PQ.View → PQ.View → Bool :=
  theKeyRunAt OnBytes.secondHashFunction Zk

theorem theKeyData_ok {Zk : OnBytes.K.Pub}
    {p : WholeD × (RecFull → PQ.View → PQ.View → PQ.View → Bool)}
    (h : theKeyLaid Zk = .ok p) : theKeyData Zk = p.1 := theKeyDataAt_ok h

theorem theKeyRun_ok {Zk : OnBytes.K.Pub}
    {p : WholeD × (RecFull → PQ.View → PQ.View → PQ.View → Bool)}
    (h : theKeyLaid Zk = .ok p) : theKeyRun Zk = p.2 := theKeyRunAt_ok h

end FlashProve
