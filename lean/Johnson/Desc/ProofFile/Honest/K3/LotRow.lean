-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/LotRow.lean: the honest side of the kind "lookup" (K3): the kind's
row (Honest/K3/Row.lean) seated at all lookups of a proof file's first chain (Honest/K3/Lot.lean),
as the lot's honest side and as sides (Honest/Side.lean). Definitions with code, and tests by
evaluation at synthetic lists; no theorem.

Terms. Honest/K3/GLOSSARY.md ("row", "lot", "site", "filling", "half", "book, coins", "agree at the
run"). In this file: a sheet is a list of lines of text, as in Honest/K3/LotSheet.lean.

What is defined.
  `theReads`: how the run's points are read off the challenges: the two functions `ptsOf` and
    `pointsAt` of Honest/K3/Heard.lean.
  `Fill`: the two letters that are left: for each site the stages' summands, and how the
    small structure is made of the chain's input.
  `rowLot`: the lot's honest side at such letters: at each site the row there.
  `whoOf`: which lookup a site is, in the words of Honest/K3/Wit.lean.
  `specFill`, `lookLot`: the lot's honest side at the specification's summands.
  `fastFill`, `lookLotFast`: the same with summands that fold tables: of this one the part is made
    (`theLot`, Honest/K3/LotFilled.lean).
  `rowPairs`, `rowSides`: at each site the row with the forms of simulators beside its parts; and
    that beside the description's own member at the place (`Side.seated`).
  `sideTests`: the tests on the sides, each with its name.
  `coinTests`: the tests on the stretches of coins that the rows state, each with its name.
  `rowSheet`, `rowSheetLines`: the sheet of LotSheet.lean at this lot, with the sides' tests behind
    it.
  `idleFill`, `idleSources`: letters and sources that hold nothing, for the tests on numbers alone.

Two fillings, one name. `lookLot` and `lookLotFast` bear the same lot's name: only one of them may
stand in a list of lots' honest sides at a time (two halves would stand at each place: the frame
rejects). Which of the two is the part is said in LotFilled.lean: `theLot`, at the summands that
fold tables. That the two send the same is not proved: `site_agree` (Honest/K3/FastLaw/Sites.lean)
shows, conditional on `Fit`, that the two fillings' summands agree at the run at every lookup of a
public part; that the same rounds follow is a statement that is not proved there;
Honest/K3/JobsFastIsSpec.lean [not in this library] compares the two by evaluation at a small
lookup.

The specification's numbers. `specJobsF` takes the shape and two numbers, lm and jLK (the docstring
of `Fo.numsF`, OnBytes/Tie/Pv/Lookup/Forest/FoV.lean: "lm (the planes' matrix has 2^lm rows) and jLK
(the lookup's first slot) are the caller's"). Here lm := the place's own lm and jLK := the place's
own first slot (`First.Look.P.lm`, `P.first`, Johnson/Desc/First/Look/LookKind.lean), which
`First.Look.lookAt` sets as X.y.h.lmb at the layers, a.S.cf.lmb at attention, X.hS.lmbH at the head:
the fields at which Johnson/HonestTrace/LookAt.lean states its hypotheses (`premF_G`: P.y.h.lmb;
`premF_A`: S.cf.lmb; `premF_H`: P.h.lmbH; jLK is free there); at the digits `lookAt` sets 5. No
summand reads lm or jLK: a wrong one would show in nothing that is sent and in no test here: only
a theorem that ties the row to these statements can catch it.

Every row is seated at the small structure `Ask` (Honest/K3/Stages.lean): a function of the
challenges in front of the part. The summands are written at `Hidden` and carried over by
`LookJobs.asked`.

How the tests can fail. The last section shows them failing: a side whose member has a round more; a
row put beside another place's member. One of the six, "no part takes a coin of its own or carries
one", is never seen to reject in this file.

Imported. Honest/Side.lean lies beneath this file.

Limits. The two letters are arguments: nothing here says what they hold, and the tests read no value
that a part sends: places, numbers of rounds, addresses alone. A site at whose place the list has no
member has no side: `sideTests` says so. The forms of simulators are data: nothing is said of what
they are good for.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.LotSheet
import Johnson.Desc.ProofFile.Honest.K3.Row
import Johnson.Desc.ProofFile.Honest.K3.Heard
import Johnson.Desc.ProofFile.Honest.K3.Wit
import Johnson.Desc.ProofFile.Honest.K3.JobsSpec
import Johnson.Desc.ProofFile.Honest.K3.JobsFast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open VerifiableInference.Desc (Block)

variable {V W X Pb S Cl : Type}

/-- How the run's points are read off the challenges. -/
def theReads : Reads := ⟨ptsOf, pointsAt⟩

/-- **The two letters that are left**, site by site. Here W is the chain's input. -/
structure Fill (W : Type) where
  /-- the stages' summands -/
  jobs : Site → LookJobs Hidden
  /-- the small structure, of the chain's input -/
  wit : Site → W → Ask

/-- **The lot's honest side**: at each site the kind's row, seated. -/
def rowLot (A : Fill W) : HLot V W X :=
  lotBy fun s => (proverSideOfLookupInChainAtOneOwner theReads (A.jobs s).asked (A.wit s) s.at_).parts

/-! ## The two fillings -/

/-- Which lookup a site is. Where a round is named that samples the matrix: the lookup on the
digits, with that round's number. It does not read the field digits: a site that `siteAt` makes
names such a round at the digits and at no other address (`siteAt_rng`, Honest/K3/LotLaw.lean). -/
def whoOf (s : Site) : Who :=
  match s.rng with
  | some r => .digits s.link r
  | none =>
    match s.caller with
    | .layers => .layers s.group
    | .attention => .attention s.group
    | .head => .head

variable {W₀ Rc Xi Tr : Type}

/-- The letters at the specification's summands. Here src says where keys and bits come from. -/
def specFill (src : Sources W₀ Xi Tr) : Fill (Local W₀ Rc Xi Tr) :=
  { jobs := fun s => specJobsF s.shape s.p.lm s.p.first
    wit := fun s => askOf src (whoOf s) }

/-- The letters at summands that fold tables; the table's rows are read off the face. -/
def fastFill (src : Sources W₀ Xi Tr) : Fill (Local W₀ Rc Xi Tr) :=
  { jobs := fun s => fastJobs s.at_.face (Fast.rowOfFace s.at_.face)
    wit := fun s => askOf src (whoOf s) }

/-- The lot's honest side at the specification's summands, at letters for the sources of keys and
bits. The part itself is `theLot` (Honest/K3/LotFilled.lean). -/
def lookLot (src : Sources W₀ Xi Tr) : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  rowLot (specFill src)

/-- The same at summands that fold tables: in the place of `lookLot`, never beside it. -/
def lookLotFast (src : Sources W₀ Xi Tr) : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  rowLot (fastFill src)

/-! ## The sides -/

/-- The seated row at a site, each part with the form of a simulator beside it. -/
def rowPairs (A : Fill W) (s : Site) : List (Part V W X × Sim Pb) :=
  lookPairs theReads (A.jobs s).asked (A.wit s) s.at_

/-- **The sides**: at each site the row beside the member of bs that stands at the place; nothing
where none does. Here bs is the description's first chain as a flat list. -/
def rowSides (A : Fill W) (bs : List (Block S Cl)) (sites : List Site) :
    List (Site × Option (Side S Cl V W X Pb)) :=
  sites.map fun s => (s, Side.seated bs s.at_.place (rowPairs A s))

/-- **The tests on the sides**, each with its name. -/
def sideTests (l : List (Site × Option (Side S Cl V W X Pb))) : List (String × Bool) :=
  l.flatMap fun x =>
    let at' := s!"link {x.1.link}, " ++ (if x.1.digits then "digits" else "calls") ++ ": "
    [(at' ++ "a member stands at the place", x.2.isSome),
     (at' ++ "the side fits: a move a round, each form at its part's address",
        x.2.any Side.fits),
     (at' ++ "a form beside every part",
        x.2.any fun σ => σ.row.length == (stages x.1.at_.face).length)]

/-- **The tests on the stretches of coins that the rows state**, each with its name. Here l holds
each site with the half at its place. -/
def coinTests (l : List (Site × Placed V W X)) : List (String × Bool) :=
  let names := l.flatMap fun x => x.2.parts.flatMap fun p => p.spends.map (·.1)
  [("no two stretches bear one name", names.eraseDups.length == names.length)] ++
  l.flatMap fun x =>
    let at' := s!"link {x.1.link}, " ++ (if x.1.digits then "digits" else "calls") ++ ": "
    let due := x.2.parts.flatMap fun p => p.spends.map (·.2)
    [(at' ++ "the row spends a coin for each hidden value, and none of the base field",
        (due.map (·.e)).sum == x.1.at_.face.slots && (due.map (·.f)).sum == 0),
     (at' ++ "no part takes a coin of its own or carries one",
        x.2.parts.all fun p => p.takes.f == 0 && p.takes.e == 0 && p.carries.isEmpty)]

/-- The sheet at this lot, with the sides' tests behind it. Pb is set to Unit: the tests read no
form's answer. -/
def rowSheet (A : Fill W) (Z : Pub) (G : Ground) (bs : List (Block S Cl)) : List String :=
  let sites := lookSites Z
  let ts := sideTests (rowSides (V := W) (X := Unit) (Pb := Unit) A bs sites)
  let cs := coinTests (sites.zip ((rowLot (V := W) (X := Unit) A).halves Z G))
  sheetOf Z G bs (rowLot (V := W) (X := Unit) A) ++
    [s!"SIDES: yes {ts.length - (failing ts).length} of {ts.length}"] ++
    (failing ts).map ("NO: " ++ ·) ++
    [s!"COINS: yes {cs.length - (failing cs).length} of {cs.length}"] ++
    (failing cs).map ("NO: " ++ ·)

/-- The same, as a function of the three public files. Here o stands for the format's second hash function.
-/
def rowSheetLines (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (A : Fill W) : List String :=
  match pureRoad.pub o pol lay KL with
  | .error e => ["NO PUBLIC PART: " ++ e]
  | .ok Z =>
    match blankBy pureRoad.links Z with
    | none => ["NO RECORDS OF THE SEGMENTS for a request of zeros"]
    | some G =>
      match onlineDescription o pol lay KL with
      | .error e => ["NO DESCRIPTION: " ++ e]
      | .ok F => rowSheet A Z G F.first.blocksInOrder

/-- Letters that hold nothing: summands that are empty lists, a structure of zeros. For the tests on
numbers alone: a row at these letters sends no honest message. -/
def idleFill : Fill W :=
  { jobs := fun _ => ⟨fun _ => ⟨fun _ _ _ => [], fun _ _ _ _ => [], fun _ _ _ => []⟩⟩
    wit := fun _ _ _ => ⟨fun _ _ _ => OnBytes.zeroE, fun _ _ => OnBytes.zeroE⟩ }

/-- Sources that hold zeros. For the tests on numbers alone. -/
def idleSources : Sources Unit Unit Unit :=
  let z : LookIn := ⟨fun _ _ => 0, fun _ _ => 0⟩
  { cells := fun _ => ⟨fun _ _ _ _ => 0⟩, weights := fun _ => ⟨fun _ _ => 0⟩
    layers := fun _ _ _ => z, attention := fun _ _ => z, head := fun _ _ _ => z
    digits := fun _ _ _ => z }

/-! ## Tests at synthetic lists -/

namespace LotToy

def sidesAt (bs : List (Block Unit Unit)) (ss : List Site) :
    List (Site × Option (Side Unit Unit Unit Unit Unit Unit)) :=
  rowSides (idleFill : Fill Unit) bs ss

-- the kind's own row at the synthetic chain: the lot's tests pass with it as with the stand-in
#guard red chain sites lotName
  (sites.map fun s => proverSideOfLookupInChainAtOneOwner theReads ((idleFill (W := Unit)).jobs s).asked
    ((idleFill (W := Unit)).wit s) s.at_) == []
-- the sides: all pass
#guard failing (sideTests (sidesAt chain sites)) == []
#guard (sideTests (sidesAt chain sites)).length == 6
-- the first lookup's member has a round more: that side does not fit
#guard failing (sideTests (sidesAt (chain 3 1) sites)) ==
  ["link 0, calls: the side fits: a move a round, each form at its part's address"]
-- a site at a place without a member: all three
#guard (failing (sideTests (sidesAt chain
    [{ site false 3 with at_ := ⟨pl 0 5, face, 3⟩ }]))).length == 3
-- a row made for one place, put beside another place's member: the forms' addresses
#guard ((Side.seated chain (pl 0 7) (rowPairs (idleFill : Fill Unit) (site false 3)) :
    Option (Side Unit Unit Unit Unit Unit Unit)).map Side.fits) == some false

-- Which lookup: the four sorts; at the digits the link's number and the matrix's round, whoever
-- calls
#guard whoOf (site false 3) == .layers 0
#guard whoOf { site false 3 with caller := .attention, group := 4 } == .attention 4
#guard whoOf { site false 3 with caller := .head } == .head
#guard whoOf { site true 9 with caller := .head, link := 6 } == .digits 6 8

/-- Each site with the kind's row at letters that hold nothing. -/
def seated (ss : List Site) : List (Site × Placed Unit Unit Unit) :=
  ss.map fun s => (s, proverSideOfLookupInChainAtOneOwner theReads ((idleFill (W := Unit)).jobs s).asked
    ((idleFill (W := Unit)).wit s) s.at_)

-- The coins: all pass; 1 + 2 * 2 tests
#guard failing (coinTests (seated sites)) == []
#guard (coinTests (seated sites)).length == 5
-- the same place twice: the names clash
#guard failing (coinTests (seated [site false 3, site false 3])) ==
  ["no two stretches bear one name"]
-- the stand-in's row takes no coin: the count
#guard failing (coinTests
    [(site false 3, (⟨pl 0 2, idleRow (site false 3).at_⟩ : Placed Unit Unit Unit))]) ==
  ["link 0, calls: the row spends a coin for each hidden value, and none of the base field"]

end LotToy

end ProofFile.Honest.K3
