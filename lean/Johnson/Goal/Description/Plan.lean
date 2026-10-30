-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/Plan.lean: the plan's values that the frame lays. One named part of
`VerifierAndGoals.theDescription` (Description.lean), in a file of its own.
State: the planner's text with both hash functions out. `filesParametersOrRefusalAt o`: THE SEAT: the record made
of `plannedAtO o` (Johnson/Desc/Ok/PlanWritten/PublicAt.lean) at the three public files and at the
constant `fixedConfigurationDigest` in the digest's place, or that planner's words. o stands in the second hash
function's place. `thePlanAt o`: its value; the library's fixed record where it refuses;
`protocolDataWellFormedAt o` (Live.lean) says no there. `thePlanLaid`, `thePlan`: at the second hash
function. `fixedConfigurationDigest`: 32 bytes of 1 (Johnson/Desc/TheCfg.lean): one constant for the plan and for
every description that wants a digest.
Why a constant. The frame is a function of the public files alone and is handed no digest. The
compiler's side makes the strings that head the chains anew at the digest that the verifier has
asked of the hash function (`VerifierAndGoals.readMoreAt`). Of the plan, its field cfg and the chains'
parameter bytes hang on the digest: a search through the constants beneath the frame found cfg named
nowhere and the bytes at `OnBytes.Maker.Page.silentKey` and `silentProof` alone, in three fields
that `withPd` overwrites; `FlashProve.verify_is_steps` holds at every function in h₀'s place
there.
Limits. What has been run with this value is not said here.

-/
import Johnson.Goal.Tie.DescriptionOfData
import Johnson.Desc.Ok.PlanWritten.PublicAt
import Johnson.Desc.TheCfg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open OnBytes.Flat OnBytes.Maker
open LPFD.Full (XF)

/-- The constant in the digest's place: 32 bytes of 1 (Johnson/Desc/TheCfg.lean). -/
def fixedConfigurationDigest : ByteArray := VerifiableInference.Desc.fixedConfigurationDigest

/-- **The plan's seat**, at a function o in the second hash function's place. -/
def filesParametersOrRefusalAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) : Except String (FilesParameters XF RecFull) :=
  (VerifiableInference.PlanWritten.plannedAtO o Zk.pol Zk.KL (some Zk.lay) fixedConfigurationDigest).map
    VerifiableInference.OnPublicFiles.bigReq

def thePlanAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) : FilesParameters XF RecFull :=
  match filesParametersOrRefusalAt o Zk with
  | .ok G => G
  | .error _ => OnBytes.K.ArmsAtFiles.bigStandFull

theorem thePlanAt_ok {o : VerifierAndGoals.SecondHashFunctionType} {Zk : OnBytes.K.Pub} {G : FilesParameters XF RecFull}
    (h : filesParametersOrRefusalAt o Zk = .ok G) : thePlanAt o Zk = G := by
  unfold thePlanAt
  rw [h]

def thePlanLaid (Zk : OnBytes.K.Pub) : Except String (FilesParameters XF RecFull) :=
  filesParametersOrRefusalAt OnBytes.secondHashFunction Zk

def thePlan (Zk : OnBytes.K.Pub) : FilesParameters XF RecFull := thePlanAt OnBytes.secondHashFunction Zk

end FlashProve
