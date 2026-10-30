-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/ReadsAtWritten.lean: at the library's written full-size values the public test
on queried positions accepts at all 52 jobs of the kind K1 on the proof file's first chain; and it
accepts at every description and public part that have these values.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has.
  lotsReadsB_of_written
                        Let F be a description whose declared rounds are the written value DW
                        (Johnson/AtFull/Pub/PubOfMade.lean), whose first chain's rows are the
                        written cutFirstFull (Johnson/Desc/Ok/PlanWritten/CutLit.lean) and whose
                        first chain's members have as many lists of oracle messages as rounds. Let
                        the public numbers of lotPars Z G be parsW. Then lotsReadsB F Z G = true.
  lotPars_written       The public numbers of lotPars Z G are parsW, if G.first and Z.first have the
                        library's full-size codes and shapes (K1.LikeFull), K1.gpOf Z is gpFull and
                        the segments' views are viewW.
  readsW                The test on the two tables accepts at every entry of parsW. Checked by
                        evaluation in Lean's kernel, as are the next seven.
  readsW_rejects        Negative tests: with one more position sampled for tree 0, for tree 2 or for
                        tree 82 the test rejects.
  treesW                The trees in front of the 52 places are 0; 3 l + 2 and 3 l + 3 for l below
                        25; and 82.
  laidW                 At each of the 52 the trees can be laid and every message lies in a tree, so
                        the test skips no message. askedW: every message is asked at a tree for
                        which positions are sampled.
  drawnW                The positions sampled for the trees 0 to 82, and for the number 83: 219, 55,
                        75 times 219, 55, 55, 55, 46, 44, 55, and 0.
  tabW_length, parsW_length
                        the written declared rounds open trees 100 times; parsW has 52 entries.
  parsW, tabW           the written public numbers (over K1.qFull, gpFull, viewW, wMsgFull); the
                        table of openings of DW.

How it fits. ReadsAtLive.lean shows that the premises of the first two hold in the goals' scope
wherever the library's gate accepts. ReadsTabLaws.lean and LotParsView.lean carry the test to the
tables. Statements on public data: no distribution is named. Meant as steps toward index privacy
(Johnson/WholeKey/Statement.lean); nothing in this folder derives index privacy from them. Not one
of the release's goal statements.

Limits. That a description of given public files has these written values is not shown here. The
written values were printed by programs (their files' heads say how); here they are plain data.
askedW shows that every message is asked at a tree for which positions are sampled: none at the
number 83 or beyond, where the test would accept idly. The test has no slack where that was tried
(readsW_rejects). All limits of ReadsTab.lean.
-/
import Johnson.SendSim.Seat.ReadsTabLaws
import Johnson.SendSim.Seat.LotParsView
import Johnson.AtFull.Pub.PubOfMade
import Johnson.AtFull.Desc.Lots.K1.Written
import Johnson.HB.LLHARD.PlanAtQFull

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At
open VerifiableInference.Desc.K1 (qFull)
open VerifiableInference.Desc.K13.Law (gpFull wMsgFull wMsg_written)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open Johnson.AtFull.Desc.K1Lot (segView viewW)
open Johnson.AtFull.Pub (DW)

/-! ## The written values -/

/-- The public numbers of the 52 jobs at the library's written full-size values. -/
def parsW : List K1.Par := parsOf qFull gpFull viewW [K1.parW qFull gpFull 4 wMsgFull]

/-- The table of openings at the written declared rounds. -/
def tabW : List ((Nat × Nat) × Nat) := readsTab DW

/-! ## Closed facts, checked by evaluation in Lean's kernel -/

set_option maxRecDepth 1000000 in
/-- The written declared rounds open trees 100 times. -/
theorem tabW_length : tabW.length = 100 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- There are 52 jobs. -/
theorem parsW_length : parsW.length = 52 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The trees in front of the 52 places. The chain has 83 trees (by inspection, not proved); that
each message is asked at a tree for which positions are sampled is askedW. -/
theorem treesW : parsW.map (fun P => treesAt cutFirstFull P.place) =
    0 :: ((List.range 25).flatMap fun l => [3 * l + 2, 3 * l + 3]) ++ [82] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- At each of the 52 jobs the trees can be laid, and every message lies in a tree: so the test
skips no message. -/
theorem laidW : (parsW.all fun P => (Own.treesMade P.codes P.sent).isSome &&
    (List.range P.sent.size).all fun k =>
      (((Own.treesMade P.codes P.sent).getD {}).tree[k]?).isSome) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The positions that are sampled for each of the first chain's trees, and for the number behind
the last. -/
theorem drawnW : (List.range 84).map (drawnTab tabW) =
    [219, 55] ++ List.replicate 75 219 ++ [55, 55, 55, 46, 44, 55, 0] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Every message of the 52 jobs is asked at a tree for which positions are sampled: none at the
number 83 or beyond, where the test would accept idly. -/
theorem askedW : (parsW.all fun P => (List.range P.sent.size).all fun k =>
    match ((Own.treesMade P.codes P.sent).getD {}).tree[k]? with
    | none => false
    | some τ => drawnTab tabW (treesAt cutFirstFull P.place + τ) != 0) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **The test accepts at all 52 jobs.** -/
theorem readsW :
    (parsW.all fun P => readsWithinT tabW P (treesAt cutFirstFull P.place)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Negative tests: one more position sampled for tree 0, for tree 2 or for tree 82 makes the test
reject. -/
theorem readsW_rejects :
    ([0, 2, 82].map fun n => parsW.all fun P =>
      readsWithinT (((0, n), 1) :: tabW) P (treesAt cutFirstFull P.place)) =
      [false, false, false] := by
  decide +kernel

/-! ## From the written values to a description -/

/-- The jobs' public numbers are the written ones, where the parameters have the library's full-size
codes and shapes, the plan's two numbers are the written ones, and the segments' views are the
written ones. -/
theorem lotPars_written {Z : ProofFile.Pub} {G : ProofFile.Ground} (hG : K1.LikeFull G.first)
    (hZ : K1.LikeFull Z.first) (hg : K1.gpOf Z = gpFull)
    (hv : (G.built.toList.zipIdx.map fun x => (x.2, segView G x)) = viewW) :
    (lotPars Z G).map (·.1) = parsW := by
  have hw : wGp Z = gpFull := hg
  rw [lotPars_view, hv, hg, parsOf_full hG, (K1.wMsg_full hZ).trans wMsg_written, hw]
  show parsOf qFull gpFull viewW [K1.parW Z.first gpFull 4 wMsgFull] = _
  rw [K1.parW_full hZ]
  rfl

/-- **The test on queried positions accepts over the two lists**, at a description whose declared
rounds and first chain's rows are the written ones, whose members have as many lists of oracle
messages as rounds, and at jobs whose public numbers are the written ones. -/
theorem lotsReadsB_of_written {Xi : Type} {F : FileDescription Xi} {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (hd : F.roundsDeclaredByBlocks = DW) (hc : cutOf F.first.blocksInOrder = cutFirstFull)
    (hs : ∀ b ∈ F.first.blocksInOrder, b.oracles.length = b.rounds.length)
    (hP : (lotPars Z G).map (·.1) = parsW) : lotsReadsB F Z G = true := by
  rw [lotsReadsB_map, hP]
  simp only [readsWithinB_tab, treesOf_cut _ hs, hd, hc]
  exact readsW

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.askedW
#print axioms OnBytes.SendSim.Seat.readsW
#print axioms OnBytes.SendSim.Seat.readsW_rejects
#print axioms OnBytes.SendSim.Seat.lotPars_written
#print axioms OnBytes.SendSim.Seat.lotsReadsB_of_written
