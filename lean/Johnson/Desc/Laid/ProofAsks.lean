-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Laid/ProofAsks.lean: **THE DOOR**: THE TESTS THAT THE PROOF FILE's LAWS ASK OF ITS
DESCRIPTION: a list, each test with the words under which it refuses. The verifier's value for the
proof file (Johnson/Desc/Laid/ProofFull.lean | ProofSmall.lean) asks every test of this list, once,
behind the description's own tests on the plan, and refuses at the first that says no.

What belongs here: a premise of a law on the proof file that is a test with code on the description,
on its data or on the three public files (with o, the second hash function, as a letter), that none
of the description's own tests asks, and that no theorem gives at all public files in scope. A
premise that a theorem gives there is a theorem, and does not belong here.

THE RULE: A TEST IS ONLY EVER APPENDED, AT THE END OF THE LIST. No test is taken out, weakened or
moved. So the verifier can only get stricter by a change of this file (`asksYes_append`).
The pins below guard against slips of a pen, not against a hand that means harm: so a new file that
comes in through this one is also to be read whole by somebody other than its writer. (1) and (2)
run with every build:
  (1) by the kernel: whoever appends a test writes the list, as it then stands, out in a file
      Johnson/Desc/Laid/ProofAsksFirst‹n›Tests.lean, never to be turned, which proves that it is a
      prefix of the list here; all pins are modules of the library, so every build compiles them;
  (2) by the kernel: Johnson/Desc/Laid/ProofPassesFirstEightTests.lean: what the VALUE lays has passed every test of
      the first list; at the second list, Johnson/Desc/Laid/ProofFullPins.lean (`laidPOf_pins`).
Nothing in this repository checks that this file declares no name but `LPFD.lawsAsk`, which files
hang beneath the verifier through this file, or that the files beneath it hold definitions alone;
scripts/check.py rejects implemented_by, extern, csimp and initializers anywhere in the library, no
more.
Each test comes with: the law that takes it as a premise; a plant that it alone refuses; the honest
files' yes at both sizes, run again; a line here that says which law needs it.

THE TESTS (first part)
  1 "the rounds declared for these public files are not the rounds written in the verifier":
  `PlanWritten.seatPinnedProof pol F`
  (Johnson/Desc/Ok/PlanWritten/Test.lean): at the full size's key, read off the strict scan of the
  parameter file, the description's rounds and depth of the table are the written ones. Needed by:
  `laidPOf_written` (in scope the laid data are the written data).
  2 to 8 the seven tests of the attention segments' guard, each at every attention segment of the
  public record that `PlanWritten.publicOfO o` makes of the three files
  (Johnson/Desc/First/Att/GuardO.lean: `K5Asks.masks | usual | calls | nums | pos | units | held`;
  the tests themselves: GuardN.lean). Where no public record is made at o, all seven say no. Needed
  by: the law of the attention segments' kind at the description's own entry, which takes the
  guard's yes as a premise (Johnson/Desc/First/Att/GuardAtSeat.lean). They are the first tests that
  read o.
THE TESTS (second part): M is the public plan that the maker of the IOP as written makes of the
three files at o, made once (Johnson/Desc/Laid/DoorHead.lean: `planOf`; `atFull`: asked at the full
size's key alone; `every`: asked at every size; where no plan is made, both say no).
  9 `atFull M PlanWritten.madeRow` (Johnson/Desc/Ok/PlanWritten/MadeTest.lean) and
  10 `atFull M (PlanWritten.cutRow F)` (CutTest.lean beside it): the two pins: what is planned for
  these files, and the IOP's division into sub-protocols, are the values written into the verifier.
  Needed by: `asks_pins` (ProofAsksLaw2.lean) and every law that stands at the written values.
  11 to 13 `every M Desc.K3Asks.digEntry | readsEntry | headEntry`
  (Johnson/Desc/First/Look/K3AsksDoor.lean). Needed by: the laws of the lookups' kind.
THE TESTS (third part)
  14 `every M Desc.LinkJoin.rowsMadeB` (Johnson/Desc/First/Link/RowsRun.lean): the plans of all
  seven chains, written anew from the plan's sizes and the links' arms, agree with the plan's own in
  four of the seven fields of each round (`PlanRound`, OnBytes/Params/Planner.lean): entry, error,
  why and scope. The fields group, rests and wordFault are not compared (`same`,
  Johnson/G/Calls.lean). At every
  sending of the seven chains a decoding radius can be computed for each sampled oracle message;
  and in the first proof chain one shape has one radius. So it can also reject on the key file's
  or the copy's file's chains.
  Needed by: `rowsRead_of_yes` (Johnson/Desc/First/Link/Law/RowsRunLaws.lean): its yes gives the
  condition `rowsRead` on the public files, which laws on the first proof chain take as a premise.
  NO FILE OF THIS LIBRARY SHOWS PUBLIC FILES THAT TESTS 1 TO 13 LET THROUGH AND THIS TEST REJECTS.
  It turns a premise of these laws into a check that the verifier makes. In the goals' scope, where
  the plain road returns at secondHashFunction and the pin of row 9 accepts, its yes follows from one more test,
  armsB (the links' 26 arms are the written ones): rowsMadeB_in_scope
  (Johnson/AtFull/Top/RowFourteen.lean), with rowsWB_true (Johnson/AtFull/Rows/Rows.lean). That
  tests 1 to 13 give armsB is shown by no theorem of this library; armsB is shown at the public part
  of the stored full-size files (publicOfO_zFull_facts, Johnson/AtFull/Public/AtX0.lean, under a
  premise on the layout file's size). Taken out of the list, it makes
  Johnson/Desc/Laid/ProofAsksFirstFourteenTests.lean fail.

-/
import Johnson.Desc.Ok.PlanWritten.Test
import Johnson.Desc.Laid.DoorHead
import Johnson.Desc.Ok.PlanWritten.MadeTest
import Johnson.Desc.Ok.PlanWritten.CutTest
import Johnson.Desc.First.Look.K3AsksDoor
import Johnson.Desc.ProofFile.Pub
import Johnson.Desc.First.Att.GuardO
import Johnson.Desc.First.Link.RowsRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open VerifiableInference
open VerifiableInference.Desc (FileDescription)

/-- **The tests that the laws ask**, of the three public files, the description and its data; o: the
format's second hash function, a letter, handed down from `laidPOf`, so that a test can make the
public record
of the three files anew without naming a hash. -/
def lawsAsk (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription ProofFile.Inst)
    (_D : OnBytes.Maker.WholeD) : List (String × Bool) :=
  let M := Desc.Door.planOf o pol lay KL
  [("the rounds declared for these public files are not the rounds written in the verifier",
    PlanWritten.seatPinnedProof pol F),
   ("an attention segment's lookup has more scalars than the segment has slots left",
    Desc.First.Att.P.K5Asks.masks o pol lay KL),
   ("the attention lookups are not the usual four with one shift",
    Desc.First.Att.P.K5Asks.usual o pol lay KL),
   ("the attention lookups' numbers do not fit the segment's sizes",
    Desc.First.Att.P.K5Asks.calls o pol lay KL),
   ("an attention segment's numbers are not those of its sizes",
    Desc.First.Att.P.K5Asks.nums o pol lay KL),
   ("one of six sizes of an attention segment's tables is 0",
    Desc.First.Att.P.K5Asks.pos o pol lay KL),
   ("an attention segment's pieces do not lie in the lookups as described",
    Desc.First.Att.P.K5Asks.units o pol lay KL),
   ("an attention segment is too large, or a round's count of bad challenges cannot be weighed \
      or is above its share",
    Desc.First.Att.P.K5Asks.held o pol lay KL),
   ("the sizes, the list of rounds, the layout, the oracle messages or the sub-proofs' shapes \
      planned for these public files are not those written into the verifier",
    Desc.Door.atFull M PlanWritten.madeRow),
   ("the IOP's division into sub-protocols at these public files is not the one written into \
      the verifier",
    Desc.Door.atFull M (PlanWritten.cutRow F)),
   ("the public files do not lay the digits of an approximate range proof where its lookup \
      reads them",
    Desc.Door.every M Desc.K3Asks.digEntry),
   ("the public files do not lay an attention step's cells where its lookup reads them",
    Desc.Door.every M Desc.K3Asks.readsEntry),
   ("the public files do not give a call of the output head's lookup room for its keys",
    Desc.Door.every M Desc.K3Asks.headEntry),
   ("the plan for these public files is not consistent: its rounds, its oracle messages with \
      their samples and challenges, or their decoding radii cannot be derived again from its \
      sizes, or one shape of oracle message has two radii",
    Desc.Door.every M Desc.LinkJoin.rowsMadeB)]

end LPFD
