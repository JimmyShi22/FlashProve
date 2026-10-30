-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/Ranges.lean: from what the key's proof of the ranges looks up, and two lines of the
parameter file, to every number of that proof.

The two lines. One gives the lengths and the rule for the distance of the group of the oracle
message that holds the multiplicities (a group: oracle messages that are tested together). The other
is one free number, called the dial here: a part of a lookup reads 2^partLog rows of the matrix, so
that every part asks about the same memory of a prover. From the two lines follow the parts of the
keys, the planes of the multiplicities, the shape of the oracle message, the codes and stages of its
proximity test, and the proof's share of the rounds of the key's first chain. No number is given
twice.

Main definitions: cutEntries, partsOf, planesOfParts, RangesLines, rangesLines, RangesSized,
rangesSized, sizedFits, lookupSizes, rangesPlan.
C++ counterpart: wf_cut, wf_parts_of, wf_planes_of, wf_lines, wf_sized and wf_plan in
blocks/frame/wf_frame.h.

Not claimed here: no theorem is stated. Where the C++ routines refuse with a reason in words, the
functions of this file return nothing.
-/
import OnBytes.Plan.Units
import OnBytes.Params.DeriveLin
import OnBytes.Iop.Wf

namespace OnBytes.Plan

open OnBytes.Params

/-! ## The parts of a lookup -/

/-- Puts one run of entries into parts of `most` entries. The state: the parts so far, the last one
first, each with its runs the last one first; and the room that the last part has left. A run that
crosses the border of a part is cut there. The first argument bounds the number of pieces. If it
ran out, the rest of the run would be left out, in no part. A run of p entries has at most
1 + (p - 1 + most - 1) / most pieces: the first takes at least one entry, and each later one starts
a fresh part and takes most entries, or all that are left. -/
def cutRun (most : Nat) : Nat → WfRun → List (List WfRun) × Nat → List (List WfRun) × Nat
  | 0, _, st => st
  | fuel + 1, r, st =>
    if r.places == 0 then st
    else
      let cut := if st.2 == 0 then [] :: st.1 else st.1
      let room := if st.2 == 0 then most else st.2
      let take := min room r.places
      let piece : WfRun := ⟨most - room, r.firstRow, take, r.stride⟩
      cutRun most fuel { r with firstRow := r.firstRow + take, places := r.places - take }
        ((piece :: cut.headD []) :: cut.drop 1, room - take)

/-- Cuts a list of entries into parts of 2^logPlaces places. A part holds
2^(logPlaces - logRowsApart) consecutive entries; the last part may be partly covered.
Row number q of entry number i of a part is at the place q 2^(logPlaces - logRowsApart) + i. So the
row's number within its entry is in the top bits of the place, and a part holds all rows of the same
entries. The bound that cutRun is given, places / most + 2, is at least the number of a run's
pieces, so nothing is left out. -/
def cutEntries (entries : List WfRun) (logPlaces logRowsApart : Nat) : List WfPart :=
  let most := 2 ^ (logPlaces - logRowsApart)
  let cut := (entries.foldl (fun st r => cutRun most (r.places / most + 2) r st) ([], 0)).1
  cut.reverse.map fun one =>
    ⟨logPlaces, (List.range (2 ^ logRowsApart)).flatMap fun q =>
      one.reverse.map fun r =>
        ⟨q * most + r.firstPlace, r.firstRow + q * r.stride, r.places,
          if logRowsApart != 0 then 0 else r.stride⟩⟩

/-- How many parts cutEntries makes. -/
def partsOf (entries : List WfRun) (logPlaces logRowsApart : Nat) : Nat :=
  let most := 2 ^ (logPlaces - logRowsApart)
  (entries.foldl (fun n r => n + r.places) 0 + most - 1) / most

/-- The most parts of one lookup, as in the C++ (WF_MOST_PARTS, blocks/frame/wf_frame.h). Each part
is a product tree of its own in the plan and in the key, and nothing later stops a large number. The
dial is in a public file, from which a verifier plans before it knows whose file it is. So a dial
that gives more parts is refused, and the parts are counted (partsOf) before anything is cut, so
that the refusal costs nothing. The number has no other ground than that a planning call stays
within seconds and megabytes; the measurements are in the C++ comment there. -/
def mostParts : Nat := 256

/-- The least number from planes on, at most 63, with keys < 2^planes. The first argument bounds the
steps. -/
def growPlanes (keys : Nat) : Nat → Nat → Nat
  | 0, planes => planes
  | fuel + 1, planes =>
    if planes < 63 && 2 ^ planes ≤ keys then growPlanes keys fuel (planes + 1) else planes

/-- The planes of a lookup follow from its parts: the least number with which a multiplicity can
count all its keys, those of padding too (a part of 2^logPlaces places has 2^(logPlaces + kCol)
keys), and which exceeds every part's number of bits. No caller chooses it. -/
def planesOfParts (parts : List WfPart) (kCol : Nat) : Nat :=
  growPlanes ((parts.map fun p => 2 ^ min (p.logPlaces + kCol) 62).sum) 63
    (parts.foldl (fun x p => max x (p.logPlaces + kCol + 1)) 2)

/-- The lookups with their parts and planes, and the line of their oracle message's group. -/
structure RangesLines where
  /-- the matrix has 2^kCol columns -/
  kCol : Nat
  /-- the rows of the matrix -/
  matrixRows : Nat
  /-- the lookups -/
  lookups : List WfLookup
  /-- the group of the oracle message with the multiplicities -/
  group : GroupLine
  /-- whether the fresh masks of the proximity test's folds ride with earlier messages -/
  masksRide : Bool := true
  /-- the oracle message's number in its chain: it comes after the index-mask message -/
  messageId : Nat := 1

/-- One lookup with its parts and planes. Nothing if the dial is too small or too large for it,
or if planes are given. -/
def lookupOfShape (kCol partLog : Nat) (s : ShapeLookup) : Option WfLookup :=
  let digits := clog2 (max s.lookup.digitWeight.length 1)
  if digits ≤ partLog && s.logRowsApart ≤ partLog - digits && partLog < 63 &&
      partsOf s.entries (partLog - digits) s.logRowsApart ≤ mostParts &&
      s.lookup.mu == 0 && s.lookup.live == 0 then
    let parts := cutEntries s.entries (partLog - digits) s.logRowsApart
    let planes := planesOfParts parts kCol
    let mu := max 1 (clog2 planes)
    some { s.lookup with parts := parts, mu := mu, live := if planes == 2 ^ mu then 0 else planes }
  else none

/-- All members of a list of options, if none is missing. -/
def allSome {α : Type} (l : List (Option α)) : Option (List α) :=
  loop l []
where
  /-- done: the members so far, the last one first. -/
  loop : List (Option α) → List α → Option (List α)
    | [], done => some done.reverse
    | some x :: t, done => loop t (x :: done)
    | none :: _, _ => none

/-- The lookups with their parts and planes, from the shape, the group's line and the dial. Nothing
if a part would read more rows than the matrix has, rounded up to a power of two, or if
lookupOfShape refuses a lookup. A part that long reads nothing more and costs more: prover and
verifier write one element for each place of a part. -/
def rangesLines (shape : Shape) (group : GroupLine) (partLog : Nat) : Option RangesLines :=
  if clog2 (max shape.matrixRows 1) < partLog then none
  else (allSome (shape.lookups.map (lookupOfShape shape.kCol partLog))).map fun l =>
    { kCol := shape.kCol, matrixRows := shape.matrixRows, lookups := l, group := group }

/-! ## The sizes -/

/-- What follows from the lines for the proof of the ranges. -/
structure RangesSized where
  /-- the lines -/
  lines : RangesLines
  /-- the size of the matrix, as the lines have it. It sizes the planes, the mask rows and the plan.
  The blocks of a chain take the size from the shape of the test on the table instead (Wf.matrixOf).
  Nothing compares the two: keySized (OnBytes/Plan/KeyOneTime.lean) makes both from the same two
  numbers, and keyOk asks Wf.admitted of these lookups under the other one. That test refuses parts
  that reach beyond the other matrix's rows or leave one out. Of the number of columns no such test
  is made: it enters only the counts of keys and of masks -/
  matrix : Wf.Matrix
  /-- the item "ranges" -/
  x : WfPublic
  /-- the group of the oracle message and the stages of the test on it -/
  test : TestSizes
  /-- the pending rows, that is, the linear claims on the matrix that are left for the test on the
  table: one for each part -/
  pending : Nat

/-- Sizes the proof of the ranges. codes: the list of the codes of the key's chains, to which the
proof's codes are added. Nothing if no admissible numbers follow. -/
def rangesSized (s : Setting) (L : RangesLines) (codes : Codes) :
    Option (RangesSized × Codes) := do
  let m : Wf.Matrix := ⟨L.kCol, L.matrixRows⟩
  if L.lookups.isEmpty then none
  if !(L.lookups.all fun l =>
      decide (1 ≤ l.mu) && decide (l.mu ≤ 6) && decide (l.live ≤ 2 ^ l.mu) &&
      decide (1 ≤ l.d) && decide (l.d ≤ 40) && !l.parts.isEmpty) then none
  let ell := 2 ^ L.group.logL
  let ellZk := 2 ^ L.group.maskLogL
  let blocks := Wf.layout L.lookups ell
  if !(blocks.all fun b => decide (2 ^ b.bits ≤ ell)) then none
  let last ← blocks.getLast?
  if ellZk ≤ s.samples then none
  let x0 : WfPublic :=
    { lookups := L.lookups
      message := ⟨{ mainRows := last.row + 1, mainDeg := 1, answers := s.samples }, 0⟩
      messageId := L.messageId
      stages := []
      choice := ⟨L.masksRide⟩ }
  let maskRows := Send.maskRowsFor (Wf.ownMasks x0 m) ellZk s.samples
  if maskRows == 0 then none
  let o : OracleShape := { x0.message.shape with maskRows := maskRows }
  let kh := linGroupBits [o]
  let group : GroupSize := { shapeOf L.group kh.1 false with h := kh.2 }
  let load : GroupLoad :=
    { cubeBits := stageCubeBits group, messages := 1, batchedRows := Wf.rowsBatched x0 m }
  let test ← solveTest s .once L.group load id group
  let (stages, codes') := ioppStages test.stages codes
  let first ← stages.head?
  let x : WfPublic :=
    { x0 with
      message := ⟨{ o with code := first.code, maskCode := first.maskCode }, 0⟩
      stages := stages }
  if !Wf.admitted codes' x m then none
  pure (⟨L, m, x, test, (L.lookups.map (·.parts.length)).sum⟩, codes')

/-! ## The rounds -/

/-- True if the stages of a proximity test name the codes and numbers of rows for which it was
sized. The list of codes is handed in by the caller: this asks whether it is the list that the
sizing filled. -/
def sizedFits (codes : Codes) (stages : List IoppStage) (solved : List StageSize) : Bool :=
  let same := fun (run : Option Code) (priced : CodeSize) =>
    run == some ⟨priced.logN, priced.ell, priced.r⟩
  stages.length == solved.length && (zipT stages solved).all fun p =>
    p.1.k == p.2.g.k && p.1.h == p.2.g.h && same codes.base[p.1.code]? p.2.g.main &&
    same codes.mask[p.1.maskCode]? p.2.g.mask

/-- The sizes of the lookups, as their rounds are planned. -/
def lookupSizes (x : WfPublic) (m : Wf.Matrix) : List LookupSize :=
  (Wf.lookupsOf x m).map fun p => { d := p.d, mu := p.mu, live := p.live, parts := p.parts }

/-- The share of the proof of the ranges in the rounds of the key's first chain, after the sending
of the index-mask message: the multiplicities, the lookups, the proximity test and, if several rows
are left on the table, the joining of these rows. -/
def rangesPlan (codes : Codes) (z : RangesSized) : Planning Unit := do
  let x := z.x
  planSend [⟨cubeBitsOf codes x.message.shape, [z.test.first]⟩]
    (← must (treesOf codes (Wf.messageOf x)))
  forEach (lookupSizes x z.matrix) planLookup
  needs (sizedFits codes x.stages z.test.stages)
  planIopp z.test.stages (Wf.rowsBatched x z.matrix) (if x.choice.masksRide then 0 else 1)
    x.choice.masksRide
  if 1 < z.pending then planBatt z.pending z.matrix.kCol

end OnBytes.Plan
