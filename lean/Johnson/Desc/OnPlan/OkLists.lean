-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/OnPlan/OkLists.lean: a test on a planner's answer p: the entries of the plan of the
proof file's shared chain, by which a round's draws are made and its error is counted, have at the
chain's first rounds the names and numbers that the steps of the description ask of a view.
Definitions with code alone; no theorem.

Main names (namespace VerifiableInference.OnPublicFiles.OkD):
  seedNums codes sent: of a sending: the coordinates of a seed's point and the number of seeds, as
    Send.verify (OnBytes/Iop/Send.lean) folds them over the notices that have answers.
  numbersOf e: of an entry: its name; the elements drawn; how many of these must not be 0; the
    positions; their range, where there are positions; the matrix entries; the rows batched.
  frontWant p: these seven, round by round, out of the shape of the test on the table and the codes:
    the shared point; the two rounds of the sending of the folded row; the locations; the two rounds
    of the sending of Omega; the point on the rows of the matrix; the split, where there is one.
  frontS p: the plan's first entries have just these.
  sealS p: the chain's last entry counts no batched rows.
  lists p: **the test**: frontS p and sealS p.

THESE ARE NOT ALL. Not here: the tests on the description's own lists of rounds (that the stretches'
entries, appended in order, are that list, on all three chains; the makers' tests on the lists).
Here stands the share that can be said of the plan's own entries at the shared chain's first rounds.

Where the program asks these: Blk.close holds a round's name, the number of elements that must not
be 0 and the numbers of draws against the plan's next entry, and asks that the entry before counts
no rows that nobody has compared; Blk.closePositions asks the entry's range and at least one
position (OnBytes/Iop/Ground.lean); drawPoint, foldeqVerify (OnBytes/Iop/Foldeq.lean) and
Send.verify ask the numbers of the shape. That no matrix entry is drawn in these rounds, and that a
round in which the verifier says nothing draws nothing, is asked here and by the steps, of a view;
the program's calls at these rounds do not ask it.

BY ITSELF frontS PASSES A PLAN WHOSE SHAPE COUNTS NO COLUMN AND WHOSE ENTRY "LOC" DRAWS NO POSITION:
that the shape counts a column is asked by linFits (OkD.shape, Johnson/Desc/OnPlan/OkDesc.lean).

Not read: an entry's bytes of the prover's message, its roots, its sample answers, its bits of work.

What is not claimed. THAT THE TEST SAYS YES AT ANY p: nothing is evaluated here. Nothing on the
rounds behind these, on the first or the second chain. Nothing on soundness, on an honest prover or
on hiding.

-/
import Johnson.Desc.OnPlan.OkDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.OkD
open OnBytes

/-- Of a sending: the coordinates of a seed's point, and the number of seeds. -/
def seedNums (codes : Codes) (sent : Array OracleNotice) : Nat × Nat :=
  let shapes := (sent.toList.map (·.shape)).filter fun s => s.answers != 0
  (shapes.foldl (fun b s => max b (Send.cube codes s).bits) 0,
    shapes.foldl (fun a s => max a s.answers) 0)

/-- Name; elements drawn; of these not 0; positions; their range; matrix entries; rows batched. -/
def numbersOf (e : Fmt.Entry) : String × Nat × Nat × Nat × Nat × Nat × Nat :=
  (e.name, e.drawE, e.drawNZ, e.poss, if e.poss == 0 then 0 else e.logN, e.trits, e.rows)

/-- The two rounds of a sending. -/
def sendWant (codes : Codes) (sent : Array OracleNotice) :
    List (String × Nat × Nat × Nat × Nat × Nat × Nat) :=
  [("SEND seed", ((seedNums codes sent).1 + 1) * (seedNums codes sent).2, (seedNums codes sent).2,
      0, 0, 0, 0),
   ("SEND answer", 0, 0, 0, 0, 0, 0)]

/-- What the steps ask at the shared chain's first rounds. -/
def frontWant (p : Model.Verify.Planned) : List (String × Nat × Nat × Nat × Nat × Nat × Nat) :=
  [("LIN point", (linS p).kCol, 0, 0, 0, 0, 0)] ++ sendWant (codesS p) (sentU p) ++
    [("LOC", 0, 0, (linS p).fold.columns,
      if (linS p).fold.columns == 0 then 0 else (linS p).fold.index.code.logN,
      0, 0)] ++
    sendWant (codesS p) (sentO p) ++ [("LIN zeta", (linS p).kRow, 0, 0, 0, 0, 0)] ++
    if (linS p).sharedSplitNeeded then [("SPLIT", 0, 0, 0, 0, 0, 0)] else []

/-- The plan's first entries have just these names and numbers. -/
def frontS (p : Model.Verify.Planned) : Bool :=
  (p.chains.proof.shared.given.rounds.take (frontWant p).length).map numbersOf == frontWant p

/-- The chain's last entry counts no batched rows. -/
def sealS (p : Model.Verify.Planned) : Bool :=
  (p.chains.proof.shared.given.rounds.getLast?.map (·.rows == 0)).getD false

/-- **The test on the lists of rounds, as far as it is said at the plan's own entries.** -/
def lists (p : Model.Verify.Planned) : Bool := frontS p && sealS p

end VerifiableInference.OnPublicFiles.OkD
