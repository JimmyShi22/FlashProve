-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/SeatFits.lean: the honest side of the kind "lookup" (K3): "fits",
as one test with code on public data at the seat, and the lot's honest side that gives a half only
where the test accepts. Definitions; nothing is proved here.

Terms. Honest/K3/GLOSSARY.md ("fit", "seat", "site", "lot", "half", "book, coins", "mark", "test by
evaluation"). In this file: "RNG" is the plan's name of the round that samples the matrix of a
link's smallness test.

Why. The functions of a lookup's parts are total: where a list is shorter than the number at which
it is read they go on with a padding value, without a warning. The rule for the honest side:
such a definition carries "fits" as a named
public hypothesis into every theorem on a coin. For a part's moves that hypothesis is a test with
code on public data, asked by whoever seats the part (Honest/SeatTests.lean has the first such test,
`readsInFront`).

Where a theorem on a coin is stated it takes `k3Fits` as a hypothesis, and with it every list that
it gathers: four clauses of `siteTests` (Honest/K3/Lot.lean), `ownerTests`
(Honest/K3/LotOwners.lean), `shapeTests` (Honest/K3/LotFilled.lean), `publicTests`
(Honest/K3/LotPublic.lean), the tests of Honest/K3/WitFits.lean; the heads of Lot.lean,
LotOwners.lean and LotFilled.lean do not say so themselves. A theorem on a coin that rests on one of
the shapes below bears `k3Fits` by name; with it `lotFits`; and a theorem on the head's lookups
bears `reqFitsB` at the instance's own data. This file holds no theorem.

What is defined.
  `stageReads f s`: which rounds of the lookup's own row the summand of stage s reads challenges of:
    stretches (first round, counted from the row's first; how many). Helpers: `readsTwo`,
    `readsTab`.
  `rowReads f` (`rowReadsBy`): every such stretch ends in front of the stage's own first round: on
    the face alone.
  `rowReadsAt bs a`: the same by `readsInFront`, at the chain's own list of sub-protocols.
  `rngTrits bs s`: how many matrix entries the round declares that samples the link's matrix.
  `seatTestsAt`, `seatTests`, `planTestsAt`, `planTests`: the tests on the seat's numbers; on the
    link's plan.
  `declFits es bs s`: the member at the site's place declares just the entries es.
  `lmFits X s`: the site's number of row bits of the planes is the layout's, by the site's sort.
  `planFits bs s`: the member at the site's place passes its own test on the plan.
  `k3Tests Z bs s`: the tests at a site, each with its name; `k3Fits`: all accept; `k3Why`: those
    that reject.
  `madeB pol KL lay`: the library's own maker of the public data returns on the three public files.
  `lotTestsFit Z n made`: the tests on the lot, once; `lotFits`: all accept.
  `reqFitsB X r`: a test on the instance's public data: the covered positions and the checked tokens
    have a place for each position.
  `fitHalves bsOf made L` (`keeps`): a lot's honest side with the halves left out at whose site a
    test rejects; no half at all where a test on the lot rejects.
  `theLotFit`, `theLotSpecFit`: the two lots of LotFilled.lean, so filtered.
  `k3FitLines`: the tests at all sites as lines, for a print.

The one padding value that was found to stand on a coin (in a search by patterns over this kind's
own files; the frame's own part and the library's terms were not searched). The function `inY` of a
stage's summand (Honest/K3/JobsFast.lean, at five places) reads the mask entries of the stage's end
values by `getD`. No public shape reaches its padding value, so no test is wanted: the masked
sumcheck's part hands a list made over the coins' own type, whose length is the number of end values
of the stage's own shape, and `inY` reads no entry at or beyond that number. Both are theorems,
without a hypothesis: `endCoins_length` and `inY_reads_tail` (Honest/K3/MasksReadFast.lean
[not in this library]). (At a course, and for the specification's summands: stated where the
theorems on a coin are, not here.)

Which shape each test rejects.
  A challenge that is read by its number has not been heard: the rounds in front are the chain's own
    count; `rowReadsAt`; the matrix's round, by `readsInFront`.
  The round "RNG" is heard but samples fewer entries than the link's test reads: `rngTrits` against
    `tritsDue`.
  A round samples fewer elements than a point takes: the plan's entries (`entriesFit`, the
    verifier's own test; and the library's `fitsVia` at the place's parameters, which includes it
    and the strict reader's test on each entry); these two read the place's parameters: that the
    member in the chain's own list declares just these entries: `declFits`.
  A part of no level, fewer than two planes, an order that is no permutation: `Face.ok`.
  The plan's number of rows is not the sum of the matrices' rows; tables of another size, a padding
    row that is not 0; a piece of a key vector that asks a column or a row beyond the array of
    digits: `mzFitsB`, `colsFitB`, `tablesFitB`, `tailFitsB`, `piecesFitB`.
  A key or a bit asks a matrix beyond the link's list, by a fixed number or by a feature's; a
    borrowed mark beyond its owner's list; a mark below 256: `listFitsB`, `featuresFitB`,
    `ownerTests`.
  A link without a plan; a shape that is not the plan's own: `hasPlan`, `publicTests`, `shapeTests`.
  Fewer than 5 row bits of the planes, or more than the shape's tables have and 5: the library's
    `planesOk`.
  The table of places cannot be read; an address without a site; fewer halves than sites:
    `lotTestsFit`.
  Any other shape at which a key or bit term of the library itself pads (a tensor's name that the
    layout lacks, a call beyond the list of calls, ...): the wide test `madeB`: the public part is
    made of files on which the library's own maker returns. It rejects such a shape only as far as
    the letter `made` is given truly (see below).
  The instance's arrays of covered positions or of checked tokens are shorter than the head has
    positions: `reqFitsB`.
Called by name, not written anew: `hasPlan`, `listFitsB`, `featuresFitB`, `mzFitsB`, `colsFitB`,
`tablesFitB`, `tailFitsB`, `piecesFitB`, `tritsDue` (Honest/K3/WitFits.lean), `publicTests`
(LotPublic.lean), `shapeTests` (LotFilled.lean), `ownerTests` (LotOwners.lean), `lookMisses`
(Lot.lean). Four of the eight tests of `seatTests` are tests of the `siteTests` of Lot.lean in their
code: the first and the seventh under the same labels, the second and the third under other labels.

The letters bsOf and made. A lot's honest side is handed the public part, not the chain's list of
sub-protocols and not the three files. Both are letters here: whoever seats the lot gives the
description's own list, and `madeB` at the files. That the public part is made of these very files
is no test with code: it would ask an equality test on the public data's structure, which there is
not. In a theorem it is a hypothesis; in a program that seats the lot it is the program's own text.
So the tests that read the list (the rounds in front, the round "RNG" and its entries, what each
stage reads, the member's own declaration and its own test on the plan) reject a shape only as far
as the letter bsOf is given truly: as the list of the chain in which the halves are seated; and the
test on the files only as far as the letter made is.

Imported. Honest/SeatTests.lean.

Users. Honest/K3/Law/SeatFitsLaw.lean shows what an acceptance of `k3Fits` gives (`fits_gives`) and
that the filtered lot gives a half only where the tests accept (`fit_only`). Honest/K3/LotInst.lean
filters its two lots by `fitHalves`. Honest/K3/SeatFitsAtZ7.lean [not in this library],
Honest/K3/SeatFitsGuards.lean [not in this library], Honest/K3/ToyAskFits.lean
[not in this library], Honest/K3/WitHeadPlayNF.lean [not in this library],
Honest/K3/WitPlaysFits.lean [not in this library] and Honest/K3/WitReq.lean import this file too.

Limits. `stageReads` is a table written by hand beside `ptsOf` (Honest/K3/Heard.lean): that the
points which a stage's summand reads are made of no other round is tested by evaluation at two faces
(Honest/K3/SeatFitsGuards.lean [not in this library]), not proved; that a summand reads these points
alone is what the theorems on summands assume. `rowReads` guards that table: at the table as it
stands it should accept at every face, since a stage in front ends where the next begins (not proved
here; it accepts at the faces of SeatFitsGuards.lean [not in this library]); what `rowReadsAt` then
asks of the public part is the first test of `seatTests` (shown in: Honest/K3/Law/SeatFitsLaw.lean,
`rowReadsAt_eq`). `rowReadsAt` counts in the first chain (`readsInFront` at base 0): a key file's
lookups stand in another chain and are not served by it as it is typed. As `readsInFront`, the tests
compare no number with what a part means by it. `planesOk` is asked at the site's own shape and
number of row bits: that these are the layout's is, for the shape, the first of `publicTests`; for
the number of row bits it is `lmFits`. The test "the matrix's round has been heard when the row
begins" follows from two others (the rounds in front are the chain's own count; the matrix's round
stands in front): no shape rejects it alone, and no test by evaluation shows it rejecting alone. The
test on the entries of the round "RNG" compares one number with the declaration, `tritsDue`: a
product. It does not tell the factors apart: a plan with other factors and the same product passes.
By reading, not shown here: the matrix's reader pads just where the sampled list is shorter than
that product; so where the test accepts no padding is met, whichever the factors. No test here
compares the rows and columns that a link's list declares for a matrix with the layout's own: a cell
beyond a matrix's declared shape is the reader's matter (Honest/K3/WitFits.lean, Limits). No public
file is at hand in what this file imports. (The library has the three public files of the full size
as a term: `VerifierAndGoals.storedPublicFiles`, Ladder/Stored.lean.) Tested by evaluation, each at synthetic data of its
own (SeatFitsGuards.lean [not in this library], Honest/K3/WitFitsGuards.lean [not in this library]):
`seatTestsAt`, `planTestsAt`, `rngTrits`, `declFits`, `lmFits`, `planFits`, `rowReads`,
`rowReadsAt`, `planesOk`, `fitsVia`, `reqFitsB`, and the rejection by `madeB`. Tested by evaluation
at a synthetic public part, written as a literal (Honest/K3/SeatFitsAtZ7.lean
[not in this library]): `publicTests`, `shapeTests`, `ownerTests`, `lotTestsFit`, the wrappers
`seatTests` and `planTests`, `k3Tests`, `k3Fits` and `k3Why` as a whole, `theLotFit` and
`theLotSpecFit` (through these `fitHalves` and `keeps`): all accept at its ten sites; its negative
tests alter the public part, the list or a site in one place. In no test by evaluation: an
acceptance by `madeB`. At a description's own public part, by a print (`k3FitLines` and the run
file's own lines): `k3Tests` (through it the five lists and the two wrappers), `k3Fits`,
`lotTestsFit`, `madeB`; `reqFitsB` at a synthetic request; and, in a section of their own,
`lotFits`, `k3Why`, `keeps`, `theLotFit` and `theLotSpecFit` (through these `fitHalves`), each both
ways.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.SeatTests
import Johnson.Desc.ProofFile.Honest.K3.LotFilled
import Johnson.Desc.ProofFile.Honest.K3.LotOwners
import Johnson.Desc.ProofFile.Honest.K3.LotPublic
import Johnson.Desc.ProofFile.Honest.K3.WitFits
import Johnson.Desc.First.Look.Via.Via

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open VerifiableInference.Desc (Block)

variable {S Cl V W X W₀ Rc Xi Tr : Type}

/-! ## 1 Which rounds of the row a stage reads -/

/-- The rounds of the shift, where there is one, and of alpha. -/
def readsTwo (f : LFace) : List (Nat × Nat) :=
  (if f.shifted then [(firstRound f .shift, 1)] else []) ++ [(firstRound f .alpha, 1)]

/-- The rounds of which the point in front of the table side's level number l is made. -/
def readsTab (f : LFace) : Nat → List (Nat × Nat)
  | 0 => [(firstRound f .join, 1)]
  | l + 1 => [(firstRound f (.tab l) + 1, f.mu + l), (firstRound f (.tabLine l), 1)]

/-- **The stretches of the row's rounds whose challenges the summand of stage s reads.** None at a
stage that sends nothing. -/
def stageReads (f : LFace) : Stage → List (Nat × Nat)
  | .tie _ => readsTwo f
  | .split _ => readsTwo f
  | .key _ 0 => readsTwo f
  | .key i (m + 1) =>
    readsTwo f ++ [(firstRound f (.key i m) + 1, m), (firstRound f (.keyLine i m), 1)]
  | .tab l => readsTwo f ++ readsTab f l
  | .leaves => readsTwo f ++ readsTab f f.d
  | .bits => readsTwo f ++ [(firstRound f .zero, 1)]
  | _ => []

/-- Every stretch that a stage reads ends in front of the stage's own first round. Here by' is the
table of stretches. -/
def rowReadsBy (by' : LFace → Stage → List (Nat × Nat)) (f : LFace) : Bool :=
  (stages f).all fun s => (by' f s).all fun x => decide (x.1 + x.2 ≤ firstRound f s)

def rowReads (f : LFace) : Bool := rowReadsBy stageReads f

/-- **The same at the seat**: the challenges have been heard when the stage's part begins. Here bs
is the chain's own list of sub-protocols. -/
def rowReadsAt (bs : List (Block S Cl)) (a : At) : Bool :=
  (stages a.face).all fun s => (stageReads a.face s).all fun x =>
    readsInFront bs a.place (a.base + x.1) x.2 (inRow := firstRound a.face s)

/-! ## 2 The tests at a site -/

/-- **How many matrix entries the round declares that samples the matrix of the site's link**, read
off the chain's own list: the link's one member whose one round is named "RNG" and stands at the
number that the site names. Nothing at a site that names no such round, and where there is not just
one such member. -/
def rngTrits (bs : List (Block S Cl)) (s : Site) : Option Nat :=
  s.rng.bind fun r =>
    match bs.filter fun c => c.place.link == some s.link && roundsInFront bs c.place == some r &&
        c.rounds.map (·.entry.name) == ["RNG"] with
    | [c] => (c.rounds.head?).map (·.entry.trits)
    | _ => none

/-- The tests on the seat: the numbers of rounds, the face, the plan's entries. Here due says how
many matrix entries the link's test reads, and es are the plan's entries of the lookup's rounds. -/
def seatTestsAt (due : Nat) (es : List Fmt.Entry) (bs : List (Block S Cl)) (s : Site) :
    List (String × Bool) :=
  [("the rounds in front are the chain's own count",
      roundsInFront bs s.at_.place == some s.at_.base),
   ("the matrix's round stands in front and is the link's one round RNG that samples entries",
      s.rng.all fun r =>
        decide (r < s.at_.base) &&
          (bs.filter fun c => c.place.link == some s.link &&
            roundsInFront bs c.place == some r &&
            c.rounds.map (fun d => (d.entry.name, d.entry.trits != 0)) == [("RNG", true)]).length
            == 1),
   ("at the digits alone a round is named that samples the matrix", s.rng.isSome == s.digits),
   ("at the digits: the round RNG samples just as many entries as the link's test reads",
      !s.digits || rngTrits bs s == some due),
   ("each stage reads challenges that have been heard when its part begins", rowReadsAt bs s.at_),
   ("the matrix's round has been heard when the row begins",
      s.rng.all fun r => readsInFront bs s.at_.place r 1),
   ("the face passes the hearing's test on its numbers", s.at_.face.ok),
   ("the plan's entries are those that the hearing goes by",
      VerifiableInference.Desc.K3.entriesFit s.at_.face es)]

/-- The same at a public part: due by the link's plan; the entries by the place's parameters. -/
def seatTests (Z : Pub) (bs : List (Block S Cl)) (s : Site) : List (String × Bool) :=
  seatTestsAt (tritsDue Z.p.X s.link) (s.p.entries.getD []) bs s

/-- The tests on a link's plan, from Honest/K3/WitFits.lean. Here digits says that the lookup is the
one on the digits. -/
def planTestsAt (X : OnBytes.Model.Verify.Public) (link : Nat) (digits : Bool) :
    List (String × Bool) :=
  [("the link has a plan", hasPlan X link),
   ("the link's list of matrices is the layout's; each borrowed mark lies in its owner's list",
      listFitsB X link),
   ("the features in use lie inside their families' matrices", featuresFitB X link),
   ("at the digits: the plan's number of rows is the sum of the matrices' rows",
      !digits || mzFitsB (tlOf X link)),
   ("at the digits: the columns fit", !digits || colsFitB (tlOf X link)),
   ("at the digits: two tables, of 2 ^ 10 and 2 ^ 8 rows, the padding row 0",
      !digits || tablesFitB (tlOf X link)),
   ("at the digits: the key vectors' pieces fit the array of digits (the library's DgP.tailTest)",
      !digits || tailFitsB (tlOf X link)),
   ("at the digits: the shape is made of the plan's pieces", !digits || piecesFitB (tlOf X link))]

/-- The same at a site. -/
def planTests (Z : Pub) (s : Site) : List (String × Bool) := planTestsAt Z.p.X s.link s.digits

/-- **The member at the site's place declares just these entries**, round for round, work bits and
all. Here es are the plan's entries of the lookup's rounds, and bs is the chain's own list. -/
def declFits (es : List Fmt.Entry) (bs : List (Block S Cl)) (s : Site) : Bool :=
  (bs.find? fun b => b.place == s.at_.place).map (·.rounds.map (·.entry)) == some es

/-- **The member at the site's place passes its own test on the plan**: the library's own test, as
the chain's own list bears it. Here bs is that list. -/
def planFits (bs : List (Block S Cl)) (s : Site) : Bool :=
  (bs.find? fun b => b.place == s.at_.place).any (·.planOk)

/-- **The site's number of row bits of the planes is the layout's**: at the digits 5; at the calls
the layers', that attention group's, or the head's own number: the four cases of the library's
`lookAt` (Johnson/Desc/First/Look/LookAt.lean). -/
def lmFits (X : OnBytes.Model.Verify.Public) (s : Site) : Bool :=
  if s.digits then s.p.lm == 5
  else
    match s.caller with
    | .layers => s.p.lm == X.y.h.lmb
    | .attention => (X.A[s.group]?).map (·.S.cf.lmb) == some s.p.lm
    | .head => s.p.lm == X.hS.lmbH

/-- **The tests at a site**, each with its name. -/
def k3Tests (Z : Pub) (bs : List (Block S Cl)) (s : Site) : List (String × Bool) :=
  seatTests Z bs s ++ planTests Z s ++ publicTests Z.p.X s ++ shapeTests s ++
    [("the planes' number of row bits fits the shape",
      VerifiableInference.Desc.First.Look.planesOk s.shape s.p.lm),
     ("the place's parameters pass the library's own test on the plan's entries",
      VerifiableInference.Desc.K3.Law.fitsVia s.p),
     ("the member at the site's place declares just the plan's entries",
      declFits (s.p.entries.getD []) bs s),
     ("the planes' number of row bits is the layout's, by the site's sort", lmFits Z.p.X s),
     ("the member at the site's place passes its own test on the plan", planFits bs s)] ++
    (borrowedAt Z.p.X s.link).flatMap fun x => ownerTests Z.p.X s.link x.1

/-- **"Fits" at a site.** -/
def k3Fits (Z : Pub) (bs : List (Block S Cl)) (s : Site) : Bool := (k3Tests Z bs s).all (·.2)

/-- The names of the tests that reject. -/
def k3Why (Z : Pub) (bs : List (Block S Cl)) (s : Site) : List String := failing (k3Tests Z bs s)

/-! ## 3 The tests on the lot -/

/-- **The library's own maker of the program's public data returns on the three public files.** -/
def madeB (pol KL lay : ByteArray) : Bool :=
  match OnBytes.Model.Verify.publicOf pol KL (some lay) with
  | .ok _ => true
  | .error _ => false

/-- The tests on the lot, once. Here n says how many halves the lot's honest side gives, and made is
`madeB` at the three files of which the public part is made. -/
def lotTestsFit (Z : Pub) (n : Nat) (made : Bool) : List (String × Bool) :=
  [("the table of places can be read", (spotsOf Z.cuts).isSome),
   ("a site for every address of the lot's list", (lookMisses Z).isEmpty),
   ("as many halves as sites", n == (lookSites Z).length),
   ("the library's own maker returns on the files of which the public part is made", made)]

def lotFits (Z : Pub) (n : Nat) (made : Bool) : Bool := (lotTestsFit Z n made).all (·.2)

/-! ## 3b A test on the instance's public data -/

/-- **The covered positions and the checked tokens have a place for each of the head's positions.**
Here r gives, of the instance, the covered positions and the token that is checked at each. It is no
test at the lot's seat: it is asked by whoever gives the instance. -/
def reqFitsB (X : OnBytes.Model.Verify.Public) (r : OnBytes.Model.Head.Covered × Array Nat) :
    Bool :=
  r.1.hOn.size == X.hS.T && r.1.hOnC.size == X.hS.T && r.2.size == X.hS.T

/-! ## 4 The lot that gives a half only where the tests accept -/

/-- A half is kept: a site stands at its place, and at every site that stands there all tests
accept. -/
def keeps (Z : Pub) (bs : List (Block S Cl)) (h : Placed V W X) : Bool :=
  ((lookSites Z).any fun s => s.at_.place == h.place) &&
    (lookSites Z).all fun s => s.at_.place != h.place || k3Fits Z bs s

/-- **A lot's honest side, filtered.** Here bsOf gives, of the public part, the first chain's list
of sub-protocols, and made gives, of the public part, `madeB` at the files of which it is made.
Where `lotFits` rejects the lot has no half at all: an empty side, without a word; and where it
accepts, a half at which a test rejects is left out likewise. So a sentence on every half of this
lot says nothing on a site without `lotFits … = true`, and `k3Fits` at that site, by name. -/
def fitHalves (bsOf : Pub → List (Block S Cl)) (made : Pub → Bool) (L : HLot V W X) : HLot V W X :=
  { name := L.name
    halves := fun Z G =>
      if lotFits Z (L.halves Z G).length (made Z) then (L.halves Z G).filter (keeps Z (bsOf Z))
      else [] }

/-- **The lot's honest side, a half only where "fits" accepts.** In the place of `theLot`, never
beside it. -/
def theLotFit (bsOf : Pub → List (Block S Cl)) (made : Pub → Bool) (cells : Tr → Cells)
    (weights : W₀ → Weights) (req : Xi → OnBytes.Model.Head.Covered × Array Nat) :
    HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  fitHalves bsOf made (theLot cells weights req)

/-- The same at the specification's summands: in the place of `theLotFit`, never beside it. -/
def theLotSpecFit (bsOf : Pub → List (Block S Cl)) (made : Pub → Bool) (cells : Tr → Cells)
    (weights : W₀ → Weights) (req : Xi → OnBytes.Model.Head.Covered × Array Nat) :
    HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  fitHalves bsOf made (theLotSpec cells weights req)

/-! ## 5 For a print -/

/-- **The tests at all sites as lines**: how many accept; each that rejects, under its site. -/
def k3FitLines (Z : Pub) (bs : List (Block S Cl)) (made : Bool) : List String :=
  let sites := lookSites Z
  let lot := lotTestsFit Z sites.length made
  let all := sites.flatMap fun s => (k3Tests Z bs s).map fun t =>
    (s!"link {s.link}, " ++ (if s.digits then "digits" else "calls") ++ ": " ++ t.1, t.2)
  [s!"FITS, THE LOT: accepted {lot.length - (failing lot).length} of {lot.length}"] ++
    (failing lot).map ("  REJECTED: " ++ ·) ++
  [s!"FITS, THE SITES: {sites.length} sites; accepted at all tests: " ++
      s!"{(sites.filter (k3Fits Z bs)).length}; tests accepted " ++
      s!"{all.length - (failing all).length} of {all.length}"] ++
    (failing all).map ("  REJECTED: " ++ ·)

end ProofFile.Honest.K3
