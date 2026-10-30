-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/LinkDec.lean: the entry file's decision. One named part of
`VerifierAndGoals.theDescription` (Description.lean), in a file of its own.
State: a description's own. `linkDecisionAtFiles`: `Desc.K15.linkDecisionAtParameterFile` (Johnson/Desc/Link/LinkWritten.lean)
at the parameter file: where that file's lines are the written full-size lines, the run of the
entry file's description at the typed parameters, whose declared rounds' entries, and no more, are
held against the written plan's rounds (`linkRoundsMatchPlan`); else the decision that says no to all. No planner
is called, no decision of the program `verify-on-bytes`
stands in it, and no law on it is imported here. It reads neither the layout file nor the
scale file, and no function in a hash function's place.
Limits. The full size alone. The test on the rounds' prices that linkOfFilesV asks of the planner's
plan is not asked here. What has been run with this value is not said here.

-/
import Johnson.Goal.Tie.DescriptionOfData
import Johnson.Desc.Link.LinkWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Run
open _root_.Iop (Dig)

def linkDecisionAtFiles (Zk : OnBytes.K.Pub) : RecFull × RecFull → PQ.View → Bool :=
  _root_.Desc.K15.linkDecisionAtParameterFile Zk.pol

end FlashProve
