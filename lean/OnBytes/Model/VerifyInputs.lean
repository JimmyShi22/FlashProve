-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/VerifyInputs.lean: the inputs from which the result of a call is computed.

The C++ verifier is called as
  cp_verify <config folder> <ivk folder> <request file> <y file> <proof file> [-id <64 hex digits>]
    [-bits N] [-no-proof-of-work] [-next-token] [-policy kind,C,theta,cap,s,sh] [-j N] [-q]
    [-show-stages]
The options -j (threads), -q (fewer lines) and -show-stages (more lines) decide nothing and have no
field here.
It reads eight files: policy.txt, KL.bin and layout.txt in the configuration folder, key.bin and
leaf/<k>.bin in the ivk folder, the request, the reply and the proof. The number k is in the header
of the proof file.

The result of a call is a `Stages.CallEnd` (OnBytes/Model/Stages.lean).

Main definitions: `FileIn`, `Files`, `Options`, `ChainName`.
What is not claimed: no theorem is stated here.
-/
import OnBytes.Model.Stages
import OnBytes.Model.Config

namespace OnBytes.Model.Verify

open OnBytes.Model.Stages

/-- The bytes of a file, or nothing if the file is missing or cannot be read. -/
abbrev FileIn : Type := Option ByteArray

/-- The files of a call. -/
structure Files where
  /-- policy.txt, the parameter file -/
  policy : FileIn
  /-- KL.bin, the quantization scales -/
  KL : FileIn
  /-- layout.txt. The outer `none`: the folder has no such name. The inner `none`: the name is
  there and the file cannot be read -/
  layout : Option FileIn
  /-- key.bin -/
  key : FileIn
  /-- the request file: T token ids, then r and e, as words of four bytes -/
  request : FileIn
  /-- the y file: the one token id that the caller was served -/
  y : FileIn
  /-- the proof file -/
  proof : FileIn
  /-- the entry leaf/<k>.bin. k comes from `entryNumber` (OnBytes/Model/Verify.lean), which does not
  look at this field -/
  entry : FileIn := none

/-- The options of a call. -/
structure Options where
  /-- -id: the commitment's ID as the caller names it, 64 hex digits in upper or lower case. The
  caller takes it from where the commitment is published, before it sends its request, and never
  from the files that it was sent. Without it a whole call ends at best as not a verification -/
  id : Option String := none
  /-- -bits: the requested bits. A call is refused if they exceed the parameter file's target, the
  number of bits at which every round's error is tested, proof of work counted, or if they exceed
  `hashLeast`. Below the threshold (`bar`) a call ends at best as not a verification -/
  bits : Nat := bar
  /-- -next-token: the proof must be about the reply alone -/
  nextToken : Bool := false
  /-- -policy: the acceptance policy that the caller expects: the exact match or a clipped gap. A
  call that passes under a clipped gap and covers a token of the request does not end with a yes:
  it ends as within limits, which can say less. Some named policies are refused by their numbers
  (OnBytes/Model/VerifyHeads.lean, `cpPolicySays`); a policy that passes can still bar no token -/
  policy : Option PolicyNamed := none
  /-- -no-proof-of-work: if at least one round needs its work to reach the target that the parameter
  file sets, all tests still run, but the call can end no better than as not a verification
  (`cpStagesRun`, OnBytes/Model/Stages.lean). Work that the file declares and no round needs changes
  nothing. A call on one file alone takes the option too -/
  noProofOfWork : Bool := false
  deriving Inhabited

/-- The seven chains of a call's files. -/
inductive ChainName where
  /-- the key's one-time chain -/
  | keyOneTime
  /-- the key's shared chain -/
  | keyShared
  /-- the key's second chain -/
  | keySecond
  /-- the entry's chain -/
  | link
  /-- the proof's first chain -/
  | proofFirst
  /-- the proof's shared chain -/
  | proofShared
  /-- the proof's second chain -/
  | proofSecond
  deriving DecidableEq, Repr, Inhabited

/-- A chain's name as it is printed. -/
def ChainName.text : ChainName → String
  | .keyOneTime => "key.one-time"
  | .keyShared => "key.shared"
  | .keySecond => "key.second"
  | .link => "entry"
  | .proofFirst => "first"
  | .proofShared => "shared"
  | .proofSecond => "second"

end OnBytes.Model.Verify
