-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/ToldTest.lean: a test with code on the proof file's IOP as written in
Lean: at the full size's key, the sub-protocols that stand in front of each of the 25 code switches
of the first chain tell, together, a written number of oracle messages. Definitions alone.

What it is for. The law of the code switch speaks of the number of oracle messages in the verifier's
state in front of the switch. That number is what the sub-protocols in front have told. Laws read it
as a closed number (`n0At`, Johnson/Top/H0/K2Hears/PlaceNums.lean). That the IOP as written tells
just so many is a fact on public data alone: no state and no byte of a proof is in it. It is no
theorem yet, so it is meant to be asked at the run, among the verifier's tests on the public files,
like the test on the written sizes (`sizedPinnedAt`, Johnson/Desc/Ok/PlanWritten/SizedTest.lean).
This file calls it nowhere.

Definitions.
  `toldBy b`: how many oracle messages the sub-protocol b tells: the tenants of the trees that it
    declares, counted.
  `toldBefore bs k`: those of the first k sub-protocols of a list.
  `switchCuts`: the 25 written pairs (k, n): k: the number, from 0, of a code switch among the first
    chain's sub-protocols; n: the messages in front of it.
  `toldPinned key bs`: at the full size's key (`fullKey`, Test.lean): `toldBefore bs k` is n at all
    25 pairs; at every other key: accept. key has to be the key of the strict scan of the public
    parameter file. Do not call this with a key of your own: call `toldPinnedAt`.
  `toldPinnedAt P F`: the form to call: P: the strict scan of the parameter file; F: the IOP as
    written, made of the same public files.

Limits. An accept says nothing of which sub-protocol stands at a number k, of the shared or the
second chain, or of the key file's and the copy's file's IOPs. That P and F are of the same files is
the caller's. At a key other than the full size's nothing is asked. Nothing on soundness.

-/
import Johnson.Desc.Ok.PlanWritten.Test

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open VerifiableInference.Desc

/-- How many oracle messages a sub-protocol tells. -/
def toldBy {S Cl : Type} (b : Block S Cl) : Nat :=
  (b.oracles.flatten.map fun o => o.tenants.length).sum

/-- How many the first k sub-protocols of a list tell. -/
def toldBefore {S Cl : Type} (bs : List (Block S Cl)) (k : Nat) : Nat :=
  ((bs.take k).map toldBy).sum

/-- The 25 code switches of the first chain at the full size: the switch's number among the chain's
sub-protocols, and the oracle messages in front of it. -/
def switchCuts : List (Nat × Nat) :=
  [(16, 7), (30, 14), (44, 22), (58, 29), (72, 37), (86, 44), (100, 52), (114, 59), (128, 67),
    (142, 74), (156, 82), (170, 89), (184, 97), (198, 104), (212, 112), (226, 119), (240, 127),
    (254, 134), (268, 142), (282, 149), (296, 157), (310, 164), (324, 172), (339, 179),
    (353, 185)]

/-- **At the full size's key**: in front of each of the 25 switches the written number of messages
is told. At every other key: accept. Do not call this with a key of your own: call
`toldPinnedAt`. -/
def toldPinned {S Cl : Type} (key : Nat × Nat × Nat) (bs : List (Block S Cl)) : Bool :=
  if key = fullKey then switchCuts.all fun x => toldBefore bs x.1 == x.2 else true

/-- **The test on what the proof file's IOP as written tells.** P: the strict scan of the parameter
file; F: the IOP as written, made of the same public files. -/
def toldPinnedAt {Xi : Type} (P : OnBytes.Model.PolScan) (F : FileDescription Xi) : Bool :=
  toldPinned (keyOfScan P) F.first.blocksInOrder

end VerifiableInference.PlanWritten
