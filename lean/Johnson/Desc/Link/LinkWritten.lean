-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Link/LinkWritten.lean: THE ENTRY FILE's ROOT AT THE WRITTEN VALUES (its linkDecisionAtParameterFile is the entry file's decision in VerifierAndGoals.theDescription: linkDecisionAtFiles, Johnson/Goal/Description/LinkDec.lean): BY CONSTANTS REACHED no planner and no hash FUNCTION lies beneath it (frP names the library's recordRead, whose typed digest, a constant, is projected away); BY IMPORT the planner's and the hashes' modules do lie beneath (the file of the slot's own types brings them). The parameter file's first lines are read by the plain reader (Params.readLines)
and held against the library's two written records of lines; at each the link's description is made of THE TYPED PARAMETERS (frP | srP) by linkOfFilesV's own last five lines.
  linkDeclaredRounds P      the blocks' own declared rounds, in a row: what the plan IS wherever the tests on the plan pass (planOkCore: roundsDeclaredByBlocks == plans): a function of P alone
  linkRoundsMatchPlan P plan    WHAT IS LEFT OF tiesOk: the blocks' rounds' entries ARE the written plan's rounds: a closed test: it is the description's fileOk (with plan := linkDeclaredRounds P the clause roundsDeclaredByBlocks == plans compares a list with itself: this test holds the rounds' ENTRIES, and no more, against the written plan)
  linkAt P plan  linkOfFilesV's last five lines at linkDescriptionAt P (linkDeclaredRounds P) (linkRoundsMatchPlan P plan)
  linkWritten    the root, of the parameter file alone
  linkDecisionAtParameterFile     the value for the slot, at the full size
WHAT linkOfFilesV ASKS AND THIS ROOT DOES NOT: entryOk (Johnson/Desc/MadeOk.lean: THE PRICES: chainAll 32 of the planner's PRICED plan: every round holds at the target 128 · the side conditions · work at most 32 bits · smallOk · workPlaced): the
prices stand as closed theorems at the written literal, not in this file: entryPricesWritten (Johnson/Desc/Ok/NumberPrices/EntryAtWritten.lean) · tiesOk's three further clauses (the plan, shape and codes READ BACK out of the parameter bytes are the made ones): there is no reading back here · ITS PLAN IS ANOTHER FILE's (declLOf, Johnson/G/RoundsOfPlanLink.lean), and planOkCore holds the blocks' rounds against it WHOLE (entry · stored parts · trees with their sources): here the stored parts and the
trees' sources are held against no other file's list: what the laws spend of them is held by the kernel at frP | srP (fr_ds | fr_xs | fr_pubAt | fr_opensAt; gathered in linkAt_full | linkAt_small) · linkRoundsMatchPlan COMPARES THE ROUNDS' ENTRIES ALONE: not the plan's entry for the table's own sample, and none of the plan's six settings · A FIFTH: THE PLANNER's OWN REFUSALS (Params.configure's gates,
OnBytes/Params/Gate.lean): of the clauses that read the entry's own values alone nothing is proved here; the others read the other two files' values; in verify() as a whole whatever the plan's own seat still runs refuses there
(a theorem of other files, at the name), not here · THE LAYOUT FILE, KL.bin AND THE PARAMETER FILE BEHIND ITS FIRST LINES ARE NOT READ: this value refuses nothing by reading them.
OBJECT: itself (the value of linkDecisionAtFiles, Johnson/Goal/Description/LinkDec.lean) · USER: entrySoundOfFullD_written (Johnson/Goal/Conditions/EntryAtWritten.lean) · LETTERS: none. Nothing on soundness.
-/
import Johnson.Desc.Link.LinkSlot
import Johnson.Desc.K15.TypedP
import OnBytes.Params.EntryStagesRecord
import OnBytes.Params.EntryStagesRecordSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open OnBytes OnBytes.Params VerifiableInference.Desc
open OnBytes.Flat OnBytes.Slice TypedOracleCompiler.Slice _root_.Run

def linkDeclaredRounds (P : P15) : List Fmt.DeclaredRound := (linkProtocolChain P).blocksInOrder.flatMap (·.rounds)

def linkRoundsMatchPlan (P : P15) (plan : Fmt.Plan) : Bool := decide ((linkDeclaredRounds P).map (·.entry) = plan.rounds)

def linkAt (P : P15) (plan : Fmt.Plan) : Except String Link3 :=
  let F := linkDescriptionAt P (linkDeclaredRounds P) (linkRoundsMatchPlan P plan)
  match F.planWord, F.dsOf "entry file" with
  | some w, _ => .error s!"entry file: {w}"
  | _, .error e => .error e
  | none, .ok ds => .ok ⟨F, ds, F.xsTyped⟩

def linkWritten (pol : ByteArray) : Except String Link3 :=
  match readLines pol with
  | .error e => .error e
  | .ok (l, _) =>
    if l = recordLines then linkAt frP recordPlan
    else if l = smallRecordLines then linkAt srP smallRecordPlan
    else .error "entry file: the parameter file's lines are not written ones"

def linkDecisionAtParameterFile (pol : ByteArray) : RecFull × RecFull → PQ.View → Bool :=
  match readLines pol with
  | .ok (l, _) =>
    if l = recordLines then
      match linkAt frP recordPlan with
      | .ok L => fun rr V => L.F.run (keysOfX frS.P.v 29 1 (anT frS.P.v 1) (recX rr)) V
      | .error _ => fun _ _ => false
    else fun _ _ => false
  | .error _ => fun _ _ => false

end Desc.K15
