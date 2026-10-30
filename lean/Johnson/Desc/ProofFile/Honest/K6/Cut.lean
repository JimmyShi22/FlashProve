-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Cut.lean: tests that hold the counts and the readers of the honest
side of the sub-protocol "the output head's own rounds" (Honest/K6/Ask.lean, Honest/K6/Part.lean)
against the verifier's text's own list of rounds (Johnson/Desc/Kinds/Head.lean, through
HeadKind.lean), and five small theorems on the block that the lot seats and on the halves that its
honest side lays. Definitions with code, tests by evaluation, theorems by unfolding.

  `headCutOwn`      the cut into parts as the maker of the book of coins reads it off the names of
                    the sub-protocol's own rounds (`cutOfNames`, Honest/BookOf.lean)
  `headScalarsOwn`  how many scalars each part sends, off the same rounds' entries
  `headSeated_is`, `headLot_seated`, `headLot_cut`, `headLot_halves`, `headLot_unfit`   the block
                    that the lot seats stands at piece 4 of the last link (number
                    `G.built.size - 1`; `headSeated_is`: at any link), has the rounds of
                    `headParAt`, and is cut as these rounds are; the half that the lot's honest side
                    lays there is `headHalf`; where the test on the public data says no it lays none
  `spentOf`         how many mask entries of the extension field a part spends
  `headSplit`, `headPerRound`   how many scalars each round of each part sends, by the parts' shapes
  `headParOf`       public numbers for the tests: four sizes; all else is 0 or a stand-in
  `headDraws`       a round's name and how many elements it draws
  `headFitsAt`      all counts at one choice of public numbers, as one yes or no
  `headTiny`, `headSmall`, `headFull`   the three sizes
  `headLabel`, `headDrawnAt`, `headFrontAt`, `headHeardAt`, `headAskAt`, `sameSum`, `headPVAt`
                    labelled challenges and a made-up input, for the tests of the readers
  `skelInFront`     of a list of skeletons: the rounds in front of a place, and at it
  `headCutLine`, `headCutLines`   the counts at three sizes and the written data's two numbers, as
                    four lines of text; no line here evaluates them

1 The counts, at each of three sizes. The cut that Ask.lean writes as a formula is the cut read off
the rounds' names. Each part has as many moves as the cut gives it rounds. Each part spends as many
mask entries as its rounds send scalars, none of the base field, takes no coin of its own and
carries none. The cut's eight parts add up to all the rounds. Round by round, the shapes of the four
calls and the two rounds of hidden scalars send as many scalars as the rounds' entries say. Each
simulator takes as many coins as its part's rounds send scalars, and its address is the part's. The
three rounds whose challenges later parts read by number (the point on the positions, the two
batching elements) bear the names and draw the numbers of elements that Ask.lean's readers suppose.

2 The block. The five `example`s say, for every seat, link, piece and choice of public numbers, that
the two lists read off the rounds are `partsCut` and `partsScalars` of the block of `Head.kind`,
that its place is `headPlace`, and that `Head.kindWithJoin`'s block and the block with the seat's
tests keep cut and place: by unfolding. The theorems say of every block that the lot seats its
place, its rounds and its cut (not the scalars).

3 The readers. Every challenge of a list bears its own number as a label, three stand in front of
the sub-protocol, and each of the sub-protocol's rounds draws as many elements as its own entry
says. At these lists each of Ask.lean's readers finds the labels that it should, and each sum,
claimed sum and list of hidden scalars of Part.lean is the core's
(Johnson/Desc/K6/Honest/Tables.lean) at these labels written out. So the front of a list taken for
its end is seen here; no line tries a part's number that is written wrongly in Part.lean. For the
two sums at the lookup's point the core's side is laid by `HeadAsk.given`, which is the honest
side's own: of it these lines see the lookup's point's coordinates on the positions alone (another
point than the one that the sub-protocol's first round draws).

4 At the written data of the full-size example (Johnson/Desc/ProofFile/Law/Skel/Full/Data.lean, the
first chain's flat list as skeletons): one member stands at `headPlace 24 4`, it has as many rounds
as the cut adds up to at that size, and the number of rounds in front of it is a written number
here.

A line marked "control" tests nothing of the honest side's row: it holds the verifier's rounds, the
written data, the core's sums or a made-up part against written numbers or against each other, so
that the lines beside it mean what they seem to.

Limits. Evaluations at three sizes, the readers at one; for all sizes nothing but the theorems and
the `example`s is shown. The description's own member at the place wraps the lot's block once more:
nothing here speaks of that member. The written data of the full size were printed off the
description's makers and are held against them by no theorem that this file calls; for the size
called "small" no such data are at hand, so its number of rounds in front is held nowhere. The
number of rounds in front enters no definition of the honest side: the parts count from the end of
what was heard. The sizes called "small" and "full" are laid here by hand (the logarithm of the
number of positions, the number of features); nothing here reads them off a parameter file. AT ALL
THREE SIZES the logarithm of the features in a block (1), the vocabulary (5) and the bits of work
(0) ARE STAND-INS: "full" has the full size's positions and features alone.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Side
import Johnson.Desc.ProofFile.Honest.BookOf
import Johnson.Desc.Kinds.HeadKind
import Johnson.Desc.ProofFile.Law.Skel.Full.Data

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes (E zeroE)
open VerifiableInference.Desc (Place Block Claim)
open VerifiableInference.Desc.Kinds (Point halves Head.Par Head.Seat Head.kind Head.kindWithJoin
  Head.tested Head.seatedClaims Head.blockClaims Head.parOf)
open VerifiableInference.Desc.Kinds.Head.Honest (PairSum wScalars pScalars sqSum prSum nmSum lgSum
  prLead nmLead lgLead)

/-! ## 1 The cut and the scalars, read off the sub-protocol's own rounds -/

/-- **The cut read off the rounds' names**: each part's number of rounds. -/
def headCutOwn (p : Head.Par) : List Nat := cutOfNames .K6 (p.rounds.map (·.entry.name))

/-- **The scalars read off the rounds' entries**: how many each part sends. -/
def headScalarsOwn (p : Head.Par) : List Nat := sumsBy (p.rounds.map scalarsIn) (headCutOwn p)

-- the two lists are those of the block of `Head.kind`, and its place is the row's
example {S Cl : Type} (cl : _ → Cl) (L : Head.Seat S) (link piece : Nat) (p : Head.Par) :
    partsCut (Head.kind cl L link piece p) = headCutOwn p := rfl
example {S Cl : Type} (cl : _ → Cl) (L : Head.Seat S) (link piece : Nat) (p : Head.Par) :
    partsScalars (Head.kind cl L link piece p) = headScalarsOwn p := rfl
example {S Cl : Type} (cl : _ → Cl) (L : Head.Seat S) (link piece : Nat) (p : Head.Par) :
    (Head.kind cl L link piece p).place = headPlace link piece := rfl
-- `Head.kindWithJoin`'s block, and a block with the seat's tests, keep cut and place
example {S Cl : Type} (look : _) (L : Head.Seat S) (link piece : Nat) (p : Head.Par) :
    partsCut (Head.kindWithJoin (Cl := Cl) look L link piece p) = headCutOwn p ∧
      (Head.kindWithJoin (Cl := Cl) look L link piece p).place = headPlace link piece := ⟨rfl, rfl⟩
example {Cl : Type} (ok : Bool) (start : _) (before : List (Nat × Nat)) (b : Block _ Cl) :
    partsCut (Head.tested ok start before b) = partsCut b ∧
      (Head.tested ok start before b).place = b.place := ⟨rfl, rfl⟩

/-- The block with true claims, as a lot seats it, stands at piece 4 of the link and has the rounds
of the place's public numbers. By unfolding. -/
theorem headSeated_is {W : OnBytes.Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block VerifiableInference.Desc.First.S Claim} (h : Head.seatedClaims W l ms = some b) :
    b.place = headPlace l 4 ∧
      b.rounds = (Head.parOf W.hS
        ((OnBytes.Params.settingOf W.P.frame).workOf .field .request)).rounds := by
  unfold Head.seatedClaims Head.blockClaims at h
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 hc
  exact ⟨rfl, rfl⟩

/-- **Every block that the lot seats** stands at piece 4 of the last link and has the rounds of the
public numbers at which the lot's honest side lays its row. By unfolding. It says nothing where the
lot seats no block. -/
theorem headLot_seated (Z : Pub) (G : Ground) {b : Block VerifiableInference.Desc.First.S Claim}
    (h : b ∈ P4.k6Hear Z G) :
    b.place = headPlace (G.built.size - 1) 4 ∧ b.rounds = (headParAt G).rounds := by
  unfold P4.k6Hear at h
  obtain ⟨ms, -, hs⟩ := Option.bind_eq_some_iff.1 (Option.mem_toList.1 h)
  exact headSeated_is hs

/-- So it is cut as these rounds are. -/
theorem headLot_cut (Z : Pub) (G : Ground) {b : Block VerifiableInference.Desc.First.S Claim}
    (h : b ∈ P4.k6Hear Z G) : partsCut b = headCutOwn (headParAt G) := by
  obtain ⟨hp, hr⟩ := headLot_seated Z G h
  unfold partsCut headCutOwn
  rw [hp, hr]
  rfl

/-- **Each half that the lot's honest side lays** is the sub-protocol's half at piece 4 of the last
link and at the public numbers of `headParAt`. By unfolding. -/
theorem headLot_halves {W₀ Rc Tr X : Type} (fits : Pub → Ground → Bool)
    (wit : Pub → Ground → Local W₀ Rc Inst Tr → HeadAsk) (Z : Pub) (G : Ground) :
    ∀ h ∈ (headLot (X := X) fits wit).halves Z G,
      h = headHalf (wit Z G) (G.built.size - 1) 4 (headParAt G) := by
  intro h hh
  by_cases hf : fits Z G = true
  · have e : (headLot (X := X) fits wit).halves Z G = (P4.k6Hear Z G).map _ := if_pos hf
    rw [e] at hh
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hh
    unfold headHalf
    rw [(headLot_seated Z G hb).1]
  · have e : (headLot (X := X) fits wit).halves Z G = [] := if_neg hf
    rw [e] at hh
    simp at hh

/-- **Where the test on the public numbers says no, no half is laid.** -/
theorem headLot_unfit {W₀ Rc Tr X : Type} (fits : Pub → Ground → Bool)
    (wit : Pub → Ground → Local W₀ Rc Inst Tr → HeadAsk) (Z : Pub) (G : Ground)
    (hf : fits Z G = false) : (headLot (X := X) fits wit).halves Z G = [] :=
  if_neg (by rw [hf]; exact Bool.false_ne_true)

/-! ## 2 The counts -/

/-- How many mask entries of the extension field a part spends (the counts `.e`). The base field's
(`.f`) are passed over: `headFitsAt` tests that these are 0. -/
def spentOf {V W X : Type} (q : Part V W X) : Nat := q.spends.foldl (fun n s => n + s.2.e) 0

/-- A list cut into stretches of given lengths. -/
def headSplit : List Nat → List Nat → List (List Nat)
  | _, [] => []
  | l, k :: ks => l.take k :: headSplit (l.drop k) ks

/-- How many scalars each round of each part sends: by the four calls' shapes; a round of hidden
scalars: as many as it spends entries; a round that sends nothing: none. Which of the eight are
calls is written here by hand; a part that lacks counts 0. -/
def headPerRound (p : Head.Par) (at_ : Place) : List (List Nat) :=
  let ps := headParts p at_
  let one (i : Nat) : List Nat := [((ps[i]?).map spentOf).getD 0]
  [one 0, one 1, scalarsOf (headSquaresJob p).shape, one 3, one 4,
   scalarsOf (headProductsJob p).shape, scalarsOf (headNormedJob p).shape,
   scalarsOf (headLogitsJob p).shape]

/-- Public numbers for the tests: the logarithms of the numbers of positions and of features in a
block, the numbers of features and of vocabulary entries, the bits of work. All else is 0 or a
stand-in: no count reads it. -/
def headParOf (lt ls d V work : Nat) : Head.Par :=
  { sizes := { lt, ls, d, MF := 0, KF := 0, epsF := 0, V, sh := 7, F := 24 }
    policy := ⟨0, 0, 0⟩, sT := 0, floor := 0, work, before := [] }

/-- Round number n of the sub-protocol: its name and how many elements it draws. -/
def headDraws (p : Head.Par) (n : Nat) : Option (String × Nat) :=
  (p.rounds[n]?).map fun r => (r.entry.name, r.entry.drawE)

/-- **All counts at one choice of public numbers.** at_: any place. -/
def headFitsAt (p : Head.Par) (at_ : Place) : Bool :=
  let ps := headParts p at_
  let ss : List (Sim Unit) := headSims p at_
  headCut p == headCutOwn p
    && ps.map (·.moves.length) == headCutOwn p
    && ps.map spentOf == headScalarsOwn p
    && headPerRound p at_ == headSplit (p.rounds.map scalarsIn) (headCutOwn p)
    && ps.all (fun q => q.takes == ⟨0, 0⟩ && q.carries.isEmpty && q.spends.all (·.2.f == 0))
    && ss.map (·.takes) == (headScalarsOwn p).map (⟨0, ·⟩)
    && ss.map (·.addr) == (List.range ps.length).map (⟨at_, ·⟩)
    && headDraws p 0 == some ("ZERO", headLt p)
    && headDraws p 1 == some ("BAT-sigma", 1)
    && headDraws p (headInFront p 4) == some ("BAT-sigma", 1)
    && headInFront p 8 == p.rounds.length

/-- Three sizes: a tiny one; one with 2^6 positions and 2^9 features with padding; one with 2^10
positions and 5,120 features. In all three the block's logarithm (1), the vocabulary (5) and the
bits of work (0) are stand-ins. -/
def headTiny : Head.Par := headParOf 2 1 6 5 0
def headSmall : Head.Par := headParOf 6 1 500 5 0
def headFull : Head.Par := headParOf 10 1 5120 5 0

#guard headFitsAt headTiny (headPlace 0 4)
#guard headFitsAt headSmall (headPlace 4 4)
#guard headFitsAt headFull (headPlace 24 4)
#guard headFitsAt (headParOf 2 1 6 5 17) (headPlace 0 4)
-- control, at the tiny size alone: other bits of work turn no cut; another block's size,
-- vocabulary and bits of work turn no count of scalars
#guard headCutOwn (headParOf 2 1 6 5 17) == headCutOwn headTiny
  && headScalarsOwn (headParOf 2 2 6 9 17) == headScalarsOwn headTiny

-- controls: the verifier's rounds, cut and counted, as written numbers
#guard headCutOwn headTiny == [1, 1, 8, 1, 1, 5, 5, 8]
#guard headScalarsOwn headTiny == [0, 9, 15, 0, 7, 12, 10, 16]
#guard headCutOwn headSmall == [1, 1, 18, 1, 1, 9, 9, 18]
#guard headScalarsOwn headSmall == [0, 9, 35, 0, 7, 20, 18, 36]
#guard headCutOwn headFull == [1, 1, 26, 1, 1, 13, 13, 26]
#guard headScalarsOwn headFull == [0, 9, 51, 0, 7, 28, 26, 52]
#guard [headTiny, headSmall, headFull].map (fun p =>
  (p.rounds.length, (headScalarsOwn p).foldl (· + ·) 0)) == [(30, 69), (58, 125), (82, 173)]
#guard headSplit (headTiny.rounds.map scalarsIn) (headCutOwn headTiny) ==
  [[0], [9], [1, 2, 2, 2, 2, 2, 2, 2], [0], [7], [2, 2, 2, 2, 4], [2, 2, 2, 2, 2],
   [2, 2, 2, 2, 2, 2, 2, 2]]
-- the honest side's runs: their names at one place, and their counts
#guard (headParts headTiny (headPlace 0 4)).map (·.spends.map (·.1)) ==
  [[], ["the segment's mask row to 1.0.4.1: scalars"],
   ["the segment's mask row to 1.0.4.2: sum", "the segment's mask row to 1.0.4.2: ends"], [],
   ["the segment's mask row to 1.0.4.4: scalars"],
   ["the segment's mask row to 1.0.4.5: sum", "the segment's mask row to 1.0.4.5: ends"],
   ["the segment's mask row to 1.0.4.6: sum", "the segment's mask row to 1.0.4.6: ends"],
   ["the segment's mask row to 1.0.4.7: sum", "the segment's mask row to 1.0.4.7: ends"]]
#guard (headParts headTiny (headPlace 0 4)).map (·.spends.map (·.2.e)) ==
  [[], [9], [13, 2], [], [7], [8, 4], [8, 2], [14, 2]]

-- THE TESTS CAN FAIL. The rows of one size do not fit the rounds of another: one position's bit
-- more; one feature more where that brings a bit (8 to 9), and none where it does not (6 to 8).
#guard headCut headTiny != headCutOwn (headParOf 3 1 6 5 0)
#guard headCut (headParOf 2 1 8 5 0) != headCutOwn (headParOf 2 1 9 5 0)
#guard headCut headTiny == headCutOwn (headParOf 2 1 8 5 0)
#guard (headParts headTiny (headPlace 0 4)).map spentOf != headScalarsOwn (headParOf 3 1 6 5 0)
-- a part left out, the row in reverse: each is seen
#guard ((headParts headTiny (headPlace 0 4)).eraseIdx 3).map (·.moves.length) != headCutOwn headTiny
#guard (headParts headTiny (headPlace 0 4)).reverse.map spentOf != headScalarsOwn headTiny
-- control (a made-up round of ten, no part of the row): a scalar more in such a round is seen
#guard spentOf (scalarsPart (V := Unit) (W := Unit) (X := Unit) "" 10 fun _ _ => []) !=
  (headScalarsOwn headTiny).getD 1 0
-- a made-up shape (three leads, two end values) with the total of the products' call (one lead,
-- four end values) and another split
#guard runOf (pointShape 3 2 2) == runOf (headProductsJob headTiny).shape
  && scalarsOf (pointShape 3 2 2) != (headSplit (headTiny.rounds.map scalarsIn)
    (headCutOwn headTiny)).getD 5 []
-- controls: the batching element of the seven products is not drawn one round earlier or later
#guard headDraws headTiny (headInFront headTiny 4 - 1) == some ("LINE", 1)
#guard headDraws headTiny (headInFront headTiny 4 + 1) == some ("PSC epsilon", 1)

/-! ## 3 The readers, at labelled challenges -/

/-- The label of element number j of challenge number n. Labels are distinct while a challenge draws
fewer than 100 elements. -/
def headLabel (n j : Nat) : E := E.ofTriple ((100 * n + j).toUInt64, 0, 0)

/-- Challenge number n, with k labelled elements. -/
def headDrawnAt (n k : Nat) : Fmt.Drawn :=
  ⟨(List.range k).map fun j => ((100 * n + j).toUInt64, 0, 0), [], [], none⟩

/-- Three challenges in front of the sub-protocol, with the numbers 90, 91, 92; three elements each.
-/
def headFrontAt : List Fmt.Drawn := [headDrawnAt 90 3, headDrawnAt 91 3, headDrawnAt 92 3]

/-- **What is heard in front of part number i**: the three; then the sub-protocol's own rounds in
front of the part, as many as the cut READ OFF THE ROUNDS gives, each under its number and with as
many elements as its entry draws. -/
def headHeardAt (p : Head.Par) (i : Nat) : List Fmt.Drawn :=
  headFrontAt ++ ((p.rounds.take (((headCutOwn p).take i).foldl (· + ·) 0)).zipIdx.map fun r =>
    headDrawnAt r.2 r.1.entry.drawE)

/-- A made-up input. No cell and no weight is 0. The lookup's point, and every call's key point, are
all elements heard in front, in order: so the lookup's point's coordinates on the positions are the
last `lt` elements heard before the sub-protocol began. -/
def headAskAt : HeadAsk :=
  { request := { tok := fun _ => 0, r := 0, e := 4 }, y := 1
    cells := { cell := fun _ f t => ((f + 2 * t + 1 : Nat) : Int)
               Wh := fun k v => ((k + 3 * v + 1 : Nat) : Int)
               stream := fun f t => ((3 * f + t + 1 : Nat) : Int) }
    lookup := fun front =>
      ((front.flatMap elemsOf).toArray, fun _ => (front.flatMap elemsOf).toArray) }

/-- Two sums are the same: points, pairs, the number of maps, and each map at the indices below n.
-/
def sameSum (s t : PairSum) (n : Nat) : Bool :=
  s.z == t.z && s.pairs == t.pairs && s.maps.length == t.maps.length &&
    (s.maps.zip t.maps).all fun x => (List.range n).all fun i => x.1 i == x.2 i

/-- The point on the positions that the sub-protocol's first round draws, by its labels: two
coordinates, the tiny size's. -/
def headPVAt : Point := #[headLabel 0 0, headLabel 0 1]

-- Ask.lean's readers find their labels in front of each part that reads them
#guard [1, 2, 4, 5].all fun i => headPV (headOwn headTiny i (headHeardAt headTiny i)) == headPVAt
#guard headGam (headOwn headTiny 2 (headHeardAt headTiny 2)) == headLabel 1 0
#guard headOm headTiny (headOwn headTiny 5 (headHeardAt headTiny 5)) == headLabel 11 0
#guard (List.range 9).all fun i => headFront headTiny i (headHeardAt headTiny i) == headFrontAt
-- near idle (the two halves of a list make the list, wherever it is cut): it sees only that both
-- readers cut at one number
#guard (List.range 9).all fun i =>
  headFront headTiny i (headHeardAt headTiny i) ++ headOwn headTiny i (headHeardAt headTiny i)
    == headHeardAt headTiny i
-- Part.lean's values and sums are the core's at these labels, written out
#guard headNine headTiny headAskAt (headHeardAt headTiny 1) ==
  (let _ := headTiny.sizes; wScalars headAskAt.cells headPVAt)
#guard headSeven headTiny headAskAt (headHeardAt headTiny 4) ==
  (let _ := headTiny.sizes; pScalars headAskAt.cells headPVAt)
#guard sameSum (headSquaresSum headTiny headAskAt (headHeardAt headTiny 2))
  (let _ := headTiny.sizes; sqSum headAskAt.cells headPVAt (headLabel 1 0)) 32
#guard sameSum (headProductsSum headTiny headAskAt (headHeardAt headTiny 5))
  (let _ := headTiny.sizes; prSum headAskAt.cells headPVAt (headLabel 11 0)) 4
#guard headProductsLead headTiny headAskAt (headHeardAt headTiny 5) ==
  (let _ := headTiny.sizes; prLead headAskAt.cells headPVAt (headLabel 11 0))
#guard sameSum (headNormedSum headTiny headAskAt (headHeardAt headTiny 6))
  (let _ := headAskAt.given headTiny headFrontAt; nmSum headAskAt.cells) 4
#guard headNormedLead headTiny headAskAt (headHeardAt headTiny 6) ==
  (let _ := headAskAt.given headTiny headFrontAt; nmLead headAskAt.cells)
#guard sameSum (headLogitsSum headTiny headAskAt (headHeardAt headTiny 7))
  (let _ := headAskAt.given headTiny headFrontAt; lgSum headAskAt.cells.toCells) 32
#guard headLogitsLead headTiny headAskAt (headHeardAt headTiny 7) ==
  (let _ := headAskAt.given headTiny headFrontAt; lgLead headAskAt.cells.toCells)
-- the four sums' points, by their labels
#guard (headSquaresSum headTiny headAskAt (headHeardAt headTiny 2)).z ==
  (halves 3).toList ++ [headLabel 0 0, headLabel 0 1]
#guard (headProductsSum headTiny headAskAt (headHeardAt headTiny 5)).z ==
  [headLabel 0 0, headLabel 0 1]
#guard (headNormedSum headTiny headAskAt (headHeardAt headTiny 6)).z ==
  [headLabel 92 1, headLabel 92 2]
#guard (headLogitsSum headTiny headAskAt (headHeardAt headTiny 7)).z ==
  [headLabel 92 1, headLabel 92 2] ++ (halves 3).toList
-- THESE TESTS CAN FAIL. What is heard in front of the next part, handed to a part's function: each
-- of the nine finds other labels. (No line tries a part's number that is written wrongly.)
#guard headNine headTiny headAskAt (headHeardAt headTiny 2) !=
  headNine headTiny headAskAt (headHeardAt headTiny 1)
#guard headSeven headTiny headAskAt (headHeardAt headTiny 5) !=
  headSeven headTiny headAskAt (headHeardAt headTiny 4)
#guard !sameSum (headSquaresSum headTiny headAskAt (headHeardAt headTiny 3))
  (headSquaresSum headTiny headAskAt (headHeardAt headTiny 2)) 32
#guard !sameSum (headProductsSum headTiny headAskAt (headHeardAt headTiny 6))
  (headProductsSum headTiny headAskAt (headHeardAt headTiny 5)) 4
#guard !sameSum (headNormedSum headTiny headAskAt (headHeardAt headTiny 7))
  (headNormedSum headTiny headAskAt (headHeardAt headTiny 6)) 4
#guard !sameSum (headLogitsSum headTiny headAskAt (headHeardAt headTiny 8))
  (headLogitsSum headTiny headAskAt (headHeardAt headTiny 7)) 32
#guard headProductsLead headTiny headAskAt (headHeardAt headTiny 6) !=
  headProductsLead headTiny headAskAt (headHeardAt headTiny 5)
#guard headNormedLead headTiny headAskAt (headHeardAt headTiny 7) !=
  headNormedLead headTiny headAskAt (headHeardAt headTiny 6)
#guard headLogitsLead headTiny headAskAt (headHeardAt headTiny 8) !=
  headLogitsLead headTiny headAskAt (headHeardAt headTiny 7)
-- controls: at another batching element the core's sums are others
#guard !sameSum (let _ := headTiny.sizes; sqSum headAskAt.cells headPVAt (headLabel 1 0))
  (let _ := headTiny.sizes; sqSum headAskAt.cells headPVAt (headLabel 2 0)) 32
#guard !sameSum (let _ := headTiny.sizes; prSum headAskAt.cells headPVAt (headLabel 11 0))
  (let _ := headTiny.sizes; prSum headAskAt.cells headPVAt (headLabel 10 0)) 4
-- none of the nine, the seven and the three claimed sums is 0: the lines above on these are not met
-- by empty hands
#guard (headNine headTiny headAskAt (headHeardAt headTiny 1)).all (· != zeroE)
  && (headSeven headTiny headAskAt (headHeardAt headTiny 4)).all (· != zeroE)
  && headProductsLead headTiny headAskAt (headHeardAt headTiny 5) != zeroE
  && headNormedLead headTiny headAskAt (headHeardAt headTiny 6) != zeroE
  && headLogitsLead headTiny headAskAt (headHeardAt headTiny 7) != zeroE

/-! ## 4 At the written data of the full-size example -/

/-- Of a list of skeletons: how many rounds stand in front of the first member at a place, and how
many that member has. -/
def skelInFront : List ProofFile.Sk.Skel → Place → Option (Nat × Nat)
  | [], _ => none
  | k :: ks, a =>
    if k.place == a then some (0, k.nRounds)
    else (skelInFront ks a).map fun x => (x.1 + k.nRounds, x.2)

-- the member at the row's place has as many rounds as the row at that size
#guard (skelInFront ProofFile.Sk.Full.flatW (headPlace 24 4)).map (·.2) ==
  some ((headCut headFull).foldl (· + ·) 0)
-- controls: the number of rounds in front; one member at the place; one of this sort in the list
#guard skelInFront ProofFile.Sk.Full.flatW (headPlace 24 4) == some (47369, headFull.rounds.length)
#guard (ProofFile.Sk.Full.flatW.filter fun k => k.place == headPlace 24 4).length == 1
#guard (ProofFile.Sk.Full.flatW.filter fun k => k.place.kind == .K6).length == 1
-- it can fail: no member of this sort stands at the piece beside it
#guard skelInFront ProofFile.Sk.Full.flatW (headPlace 24 5) == none

/-! ## 5 The counts as lines of text -/

/-- One size's line. -/
def headCutLine (name : String) (p : Head.Par) : String :=
  s!"{name}: lt {headLt p} · lPd {headLPd p} · rounds {p.rounds.length} · " ++
  s!"the cut {headCutOwn p} · " ++
  s!"scalars {headScalarsOwn p} · in all {(headScalarsOwn p).foldl (· + ·) 0} · " ++
  s!"all counts fit: {headFitsAt p (headPlace 0 4)}"

/-- **The counts at three sizes, and a fourth line on the written data.** -/
def headCutLines : List String :=
  [headCutLine "tiny" headTiny, headCutLine "small" headSmall, headCutLine "full" headFull,
   s!"full, written data: (rounds in front, rounds) " ++
     s!"{skelInFront ProofFile.Sk.Full.flatW (headPlace 24 4)}"]

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.headSeated_is
#print axioms ProofFile.Honest.K6.headLot_seated
#print axioms ProofFile.Honest.K6.headLot_cut
#print axioms ProofFile.Honest.K6.headLot_halves
#print axioms ProofFile.Honest.K6.headLot_unfit
