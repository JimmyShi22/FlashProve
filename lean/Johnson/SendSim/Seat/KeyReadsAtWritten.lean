-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/KeyReadsAtWritten.lean: at the library's written full-size values the public
test on queried positions accepts at the three sub-protocols of the kind K1 in a key file's first
chain; and it accepts at every key file's description whose source and numbers have these values.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". There the description is the proof
file's; here it is the key file's Key.descriptionFromSource. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file has.
  keyReadsB F ps      the test: readsWithinB (ReadsTest.lean) accepts at each entry of ps, at the
                      number of trees in front of the first member of F's first chain at the entry's
                      place.
  keyReads_of_pins    If the source X and the numbers N and P have the library's written full-size
                      values (ChainPins X N P, Johnson/HB/LLHARD/KB4/Frame.lean), then keyReadsB
                      (Key.descriptionFromSource X N P) (keyPars X) = true.
  keyPars_written     Under ChainPins, keyPars X is the closed list keyParsW.
  keyReadsW           The test on the two tables of ReadsTab.lean accepts at every entry of
                      keyParsW. Checked by evaluation in Lean's kernel, as are the next seven.
  keyReadsW_rejects   Negative tests: with one more position sampled for tree 0, for tree 1 or for
                      tree 5 the test rejects.
  keyTreesW           The trees in front of the three places are 0, 1 and 5.
  keyLaidW, keyAskedW
                      At each of the three the trees can be laid and every message lies in a tree;
                      every message is asked at a tree for which positions are sampled.
  keyDrawnW           The positions sampled for the first chain's trees 0 to 5, and for the number
                      6: 49, 49, 39, 33, 25, 49, and 0.
  tabKW_length, keyParsW_places
                      the written declared rounds open trees 23 times; keyParsW has three entries,
                      at the three places.
  keyParsAt, keyParsW, tabKW
                      keyPars' definition as a function of what it reads of a source; its value at
                      the library's written values (oneFull, declKeyFull, toldKeyFull); the table of
                      openings of declKeyFull.

How it fits. Under ChainPins the library proves that the description's first chain and its declared
rounds are closed terms (first_of, decl_of, Frame.lean). ReadsTabLaws.lean carries the test to two
short tables. KeyReadsAtLive.lean shows that ChainPins holds in the goals' scope wherever the key
file's makers return. Statements on public data: no distribution is named. Meant as steps toward
index privacy (Johnson/WholeKey/Statement.lean); nothing in this folder derives index privacy from
them. Not one of the release's goal statements.

Limits. That a key file's description of given public files has these values is not shown here.
These senders' trees are read partly in the key file's other chains; the table holds the openings of
all three chains. The test has no slack where that was tried (keyReadsW_rejects). Three of the first
chain's six trees. The count is of one execution of the key file's description. All limits of
ReadsTab.lean and of AtKey.lean.
-/
import Johnson.SendSim.Seat.AtKeyPars
import Johnson.SendSim.Seat.ReadsTabLaws
import Johnson.HB.LLHARD.KB4.Frame
import Johnson.HB.LLHARD.KB4.CBlocks

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At
open VerifiableInference.Desc.Key (groupsTold rootsAt rootsBefore lastSendRound)
open VerifiableInference.PlanWritten (cutOf)
open Johnson.KB4 (WK oneAt oneFull toldKeyFull ChainPins)
open Johnson.KB8 (declKeyFull)

/-- The public test on queried positions over a list of public numbers, at a description's first
chain. -/
def keyReadsB {Xi : Type} (F : FileDescription Xi) (ps : List (K1.Par × (Nat → Option Ride))) : Bool :=
  ps.all fun x =>
    readsWithinB F x.1 (treesOf F.first.blocksInOrder (F.first.blocksInOrder.takeWhile (·.place != x.1.place)))

/-- keyPars' definition, of what it reads of a source. -/
def keyParsAt (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root) :
    List (K1.Par × (Nat → Option Ride)) :=
  [(K1.parIdx one (groupsTold told 0 (rootsAt D 0)), rideOf none),
   (K1.parMsg one (groupsTold told (rootsBefore D 2) (rootsAt D 2)),
     rideOf (msgFold one.ranges))] ++
    ((linMessageW one.lin).map fun msg =>
      (K1.parWKey one msg
          (groupsTold told (rootsBefore D (lastSendRound D)) (rootsAt D (lastSendRound D))),
        rideOf (wFold one.lin))).toList

theorem keyPars_at (Xs : Key.Source) :
    keyPars Xs = keyParsAt Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 := rfl

/-- It reads five fields of the one-time chain's values. -/
theorem keyParsAt_five (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root) :
    keyParsAt one D told =
      keyParsAt (oneAt one.given.plan.samples one.indexMasks one.ranges one.codes one.lin) D
        told := rfl

/-! ## The written values -/

/-- The three public numbers at the library's written full-size values. -/
def keyParsW : List (K1.Par × (Nat → Option Ride)) :=
  keyParsAt oneFull declKeyFull.1 toldKeyFull.1

/-- The table of openings at the key file's written declared rounds. -/
def tabKW : List ((Nat × Nat) × Nat) := readsTab declKeyFull

theorem keyPars_written {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}
    (h : ChainPins X N P) : keyPars X = keyParsW := by
  rw [keyPars_at, keyParsAt_five, h.samples, h.idx, h.ranges, h.codes, h.lin, h.D₁, h.told₁]
  rfl

/-! ## Closed facts, checked by evaluation in Lean's kernel -/

set_option maxRecDepth 1000000 in
/-- The written declared rounds open trees 23 times. -/
theorem tabKW_length : tabKW.length = 23 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- There are three entries, at the three places. -/
theorem keyParsW_places : keyParsW.map (·.1.place) =
    [⟨1, none, 1, .K1⟩, ⟨1, none, 2, .K1⟩, ⟨1, none, 14, .K1⟩] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The trees in front of the three places. The chain has six trees (by inspection, not proved). -/
theorem keyTreesW :
    keyParsW.map (fun x => treesAt (cutOf WK.first.blocksInOrder) x.1.place) = [0, 1, 5] := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At each of the three the trees can be laid, and every message lies in a tree. -/
theorem keyLaidW : (keyParsW.all fun x => (Own.treesMade x.1.codes x.1.sent).isSome &&
    (List.range x.1.sent.size).all fun k =>
      (((Own.treesMade x.1.codes x.1.sent).getD {}).tree[k]?).isSome) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The positions that are sampled for each of the first chain's six trees, and for the number
behind the last. -/
theorem keyDrawnW : (List.range 7).map (drawnTab tabKW) = [49, 49, 39, 33, 25, 49, 0] := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Every message of the three is asked at a tree for which positions are sampled. -/
theorem keyAskedW : (keyParsW.all fun x => (List.range x.1.sent.size).all fun k =>
    match ((Own.treesMade x.1.codes x.1.sent).getD {}).tree[k]? with
    | none => false
    | some τ => drawnTab tabKW (treesAt (cutOf WK.first.blocksInOrder) x.1.place + τ) != 0) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The test accepts at all three.** -/
theorem keyReadsW : (keyParsW.all fun x =>
    readsWithinT tabKW x.1 (treesAt (cutOf WK.first.blocksInOrder) x.1.place)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Negative tests: one more position sampled for tree 0, for tree 1 or for tree 5 makes the test
reject. -/
theorem keyReadsW_rejects :
    ([0, 1, 5].map fun n => keyParsW.all fun x =>
      readsWithinT (((0, n), 1) :: tabKW) x.1 (treesAt (cutOf WK.first.blocksInOrder) x.1.place)) =
      [false, false, false] := by
  decide +kernel

/-! ## From the written values to a description -/

/-- The written first chain's members have as many lists of oracle messages as rounds. -/
theorem WK_lengths : ∀ b ∈ WK.first.blocksInOrder, b.oracles.length = b.rounds.length := fun b hb => by
  have h := List.all_eq_true.1 Johnson.KB4.WK_first b hb
  rw [Bool.and_eq_true] at h
  have h2 := h.2
  unfold Block.shaped at h2
  rw [Bool.and_eq_true] at h2
  exact beq_iff_eq.1 h2.1

/-- **The test on queried positions accepts at the three sub-protocols of the kind K1 in the first
chain of a key file's description**, where the source and the numbers have the library's written
full-size values. -/
theorem keyReads_of_pins {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}
    (h : ChainPins X N P) : keyReadsB (Key.descriptionFromSource X N P) (keyPars X) = true := by
  have hfl : (Key.descriptionFromSource X N P).first.blocksInOrder = WK.first.blocksInOrder :=
    congrArg (·.blocksInOrder) (Johnson.KB4.first_of h)
  have hs : ∀ b ∈ (Key.descriptionFromSource X N P).first.blocksInOrder, b.oracles.length = b.rounds.length := by
    rw [hfl]
    exact WK_lengths
  unfold keyReadsB
  rw [keyPars_written h]
  simp only [readsWithinB_tab, treesOf_cut _ hs]
  rw [Johnson.KB4.decl_of h, hfl]
  exact keyReadsW

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.keyReadsW
#print axioms OnBytes.SendSim.Seat.keyReadsW_rejects
#print axioms OnBytes.SendSim.Seat.keyReads_of_pins
