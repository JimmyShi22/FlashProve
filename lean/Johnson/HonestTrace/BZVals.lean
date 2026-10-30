-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/BZVals.lean

The array BZ of a segment's smallness test by its own row and column, as a function of the cells and
of what was heard, with the two tests beside it. No place of an oracle message's table is named
here: how the array lies in a message is laidData's (Johnson/Desc/ProofFile/Honest/LaidData.lean).
Definitions with code. No theorem.

BZ holds the bits of the multiplicities of the lookup on the digits: 32 rows, 2^11 columns, over the
base field (docs/format/11-1-machinery.md, "Where a bit of a multiplicity is in BZ"). That page's
table under "The arrays of a segment's smallness test" lists it at moment 2, after the array of
digits ZZ, and lists no other array of the lookup on the digits.

Main definitions:
* "BzAt": what BZ's entries read of public data at one segment: the number of the round "RNG" among
  the first chain's rounds; how many entries that round is declared to sample; the plan's state tl
  of the smallness test; the list mats (for each matrix of the test's list: its owner's segment, its
  name there, its first column there).
* "BzAt.entry b C heard": BZ by its own row and column: the field bz of digitsOf b.tl b.mats C t
  (Johnson/HonestTrace/DigitsAtTrace.lean), t being the entries that the round number b.rng of heard
  has sampled. That field is bzOf (Johnson/HonestTrace/CountsDigits.lean) of zzOf
  (Johnson/Desc/ProofFile/Honest/K8/Digits.lean).
* "BzAt.ready b heard": THE TEST ON WHAT WAS HEARD.
* "BzAt.why b front rows columns", "BzAt.fits": THE TEST ON PUBLIC DATA, with the first reason for
  which it rejects.
* "rngIn", "rngAt", "bzAtOf": a segment's BzAt off a description's public part Z and the segments'
  plans G. mats is a parameter: no definition here makes it.

Where a value stands in, and which test rejects there. BzAt.entry is a total function. It yields a
value that means nothing: where the round has not been heard, or has sampled another number of
entries than the list's columns times tau, or an entry other than -1, 0, 1 (BzAt.ready rejects);
where that round is not the last in front of the sending, or is declared to sample another number;
where mats is shorter or longer than the plan's list; where tl.mz is not the number of all rows of
cells; where the shape of the lookup has not two calls with tables of 2^10 and 2^8 rows that hold 0,
1, 2, … and the padding row 0; where a call has 2^32 places or more; where the library's test
DgP.tailTest on the pieces rejects; where the layout's array has not 32 rows and tl.bzColumns
columns (BzAt.fits rejects each). What no test covers is under Limits. A law on these values is to
take BzAt.fits and BzAt.ready as premises.

Limits. WHAT NO TEST HERE COVERS, because it hangs on the cells: a combination that leaves its
window (from -2^17 to 2^17 - 1). There zzOf's two digits do not give the combination back, and BZ
counts these digits. The honest part of the smallness test's round stops there (smallHid,
Johnson/Desc/ProofFile/Honest/K8/Part.lean). Nor is a reader of cells held to anything: at a name
that it does not know it yields what it yields; of mats the test reads the length alone. rngIn takes
the first round of the segment's place of the kind K8, and yields nothing unless that round's
declared name is "RNG". Where two places of the kind K8 bear one segment's number, or two steps one
name, it takes the first; BzAt.fits then rejects unless that round is the last in front of the
sending. rngAt and bzAtOf want a description's public part: Johnson/HonestTrace/BZRowsAtSmall.lean
evaluates them at one; Johnson/HonestTrace/BZRowsToy.lean runs rngIn at a synthetic table of steps.
Cost: every entry makes the counts anew (for each place of a call's key vector a search through the
call's table): a sender that lays 2^16 entries wants a table of counts; none is typed here.

Not claimed: that a prover's program sends these entries; that a verifier accepts them; completeness
of the protocol; anything on what the entries reveal.
-/
import Johnson.HonestTrace.DigitsAtTrace
import Johnson.Desc.ProofFile.Places
import Johnson.Desc.ProofFile.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open ProofFile (Pub Ground Spot spotsOf)
open ProofFile.Honest (Cells)
open ProofFile.Honest.K8 (parOfTail)
open VerifiableInference.Desc.First.K8.Honest (allRows)
open OnBytes.Model (HTailF2)

/-- **What BZ's entries read of public data at one segment.** -/
structure BzAt where
  /-- the number, among the first chain's rounds, of the round that samples the smallness test's
  matrix -/
  rng : Nat
  /-- how many entries that round is declared to sample -/
  declared : Nat
  /-- the plan's state of the segment's smallness test -/
  tl : HTailF2
  /-- for each matrix of the test's list: its owner's segment, its name there, its first column
  there. A parameter, which nothing here ties to matsOf (Johnson/HonestTrace/DigitsAtTrace.lean):
  "the entries are the trace's only at mats := matsOf X k (cellsAtOf_matsOf)" -/
  mats : List (Nat × String × Nat)

/-- How many entries the digits read of the round: for each column of each matrix of the list, tau.
-/
def BzAt.wanted (b : BzAt) : Nat := (parOfTail b.tl).ks.sum * b.tl.tau

/-- The entries that the round has sampled, off the challenges heard; nothing where that round is
not among them. -/
def BzAt.sampled (b : BzAt) (heard : List Fmt.Drawn) : Option (List Int) :=
  (heard[b.rng]?).map (·.trits)

/-- **The test on what was heard.** It accepts if the round that samples the matrix is among the
challenges heard, has sampled as many entries as the digits read, and each of them is -1, 0 or 1. -/
def BzAt.ready (b : BzAt) (heard : List Fmt.Drawn) : Bool :=
  (b.sampled heard).any fun t =>
    t.length == b.wanted && t.all fun x => x == -1 || x == 0 || x == 1

/-- **The test on public data**: the first reason for which it rejects; nothing if it accepts.
front: how many rounds of the first chain stand in front of the sending. rows, columns: those of the
layout's array. -/
def BzAt.why (b : BzAt) (front rows columns : Nat) : Option String :=
  if b.rng + 1 != front then some "the round that samples the matrix is not the last in front"
  else if b.declared != b.wanted then some "the round is declared to sample another number"
  else if b.mats.length != b.tl.mats.size then some "mats is not as long as the plan's list"
  else if b.tl.mz != allRows (parOfTail b.tl) then some "mz is not the number of all rows of cells"
  else if !(FoNums.ok b.tl.f9 && OnBytes.DgP.tailTest b.tl) then
    some "the lookup's shape or its pieces fail the library's tests"
  else if !(b.tl.f9.calls.size == 2 && 2 ^ b.tl.f9.cK == 2) then some "not two calls"
  else if !(FoNums.kOf b.tl.f9 0 == 10 && FoNums.kOf b.tl.f9 1 == 8 && b.tl.f9.kT == 10) then
    some "the tables have not 2^10 and 2^8 rows"
  else if !(FoNums.t0Of b.tl.f9 0 == 0 && FoNums.t0Of b.tl.f9 1 == 0) then
    some "a padding row is not 0"
  else if !((List.range 2).all fun c =>
      (List.range (2 ^ FoNums.kOf b.tl.f9 c)).all fun t => FoNums.tauN b.tl.f9 c t == t) then
    some "a table does not hold 0, 1, 2, …"
  else if !((List.range 2).all fun c => decide (FoNums.nOf b.tl.f9 c < 32)) then
    some "a call has too many places for 32 planes"
  else if !(rows == 32 && columns == b.tl.bzColumns) then
    some "the layout's array has not BZ's rows and columns"
  else none

/-- It accepts. -/
def BzAt.fits (b : BzAt) (front rows columns : Nat) : Bool := (b.why front rows columns).isNone

/-- **BZ by its own row and column**: the field bz of digitsOf at the cells and the sampled entries;
at the empty list of entries where the round has not been heard: BzAt.ready rejects there. As at
zzOf (Johnson/Desc/ProofFile/Honest/K8/Digits.lean): "This is the array before encoding: which part
sends it, with which coins, is not said here. At a name in mats that is no label the cells are what
the reader yields there." -/
def BzAt.entry (b : BzAt) (C : Cells) (heard : List Fmt.Drawn) : Nat → Nat → Cb.Gl.F :=
  (digitsOf b.tl b.mats C ((b.sampled heard).getD [])).bz

/-- The number, among the first chain's rounds, of the first round of a segment's place of the kind
K8, with the number of entries that it is declared to sample; nothing unless that round's declared
name is "RNG". before: how many rounds stand in front of the step of a name. D: the first chain's
declared rounds. sps: the first chain's places. -/
def rngIn (before : String → Option Nat) (D : List Fmt.DeclaredRound) (sps : List Spot) (seg : Nat) :
    Option (Nat × Nat) := do
  let sp ← sps.find? fun sp => sp.place.link == some seg && sp.place.kind == .K8
  let c ← sp.cuts.head?
  let n ← before c.look
  let d ← D[n]?
  if d.entry.name == "RNG" then some (n, d.entry.trits) else none

/-- The same off a description's public part. -/
def rngAt (Z : Pub) (sps : List Spot) (seg : Nat) : Option (Nat × Nat) :=
  rngIn Z.roundsBefore? Z.D.1 sps seg

/-- A segment's public data, off the description's public part and the segments' plans. mats: a
parameter, which nothing here ties to matsOf (Johnson/HonestTrace/DigitsAtTrace.lean): "the entries
are the trace's only at mats := matsOf X k (cellsAtOf_matsOf)". -/
def bzAtOf (Z : Pub) (G : Ground) (mats : Nat → List (Nat × String × Nat)) (seg : Nat) :
    Option BzAt := do
  let sps ← spotsOf Z.cuts
  let n ← rngAt Z sps seg
  let Y ← G.built[seg]?
  pure ⟨n.1, n.2, Y.tl, mats seg⟩

end OnBytes.HonestTrace
