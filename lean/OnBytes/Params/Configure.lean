-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Configure.lean: from the parsed public files to the parameter bytes of all seven
chains.

Everything public about an instance follows from its public files. The C++ programs have one
routine that goes from the files' bytes to the digest that every chain hashes at its start and to
what is derived from the files: all sizes, the plans of the chains, the shapes
(blocks/frame/configure.h, with sized() in blocks/frame/files.h). This file renders that routine
from the parsed lines on. What the routine cannot read off the files itself comes from the caller,
as a record `Shapes`: the sub-proofs' shapes and rounds, the layout, the links' identifiers, what
the key's proof of the ranges looks up, and a request's range checks.

The seven chains are hash chains: three of a key file (one-time, shared, second), one of an entry
file (the link's) and three of a proof file (first, shared, second). lean/GLOSSARY.md says what
these files, a chain and a round are; OnBytes/Params/Chains.lean says what each chain holds. The
result holds their parameter bytes. They follow from the lines of the parameter file, the caller's
shapes and the digest of the public files, and from nothing else.

Every round must hold at the target t that the parameter file names, with the round's w bits of
proof of work counted: the planner's bound on the round's error is at most 2 ^ (w - t)
(`roundHolds`, OnBytes/Params/Planner.lean). `needsWork` says if a round misses the target unless
its work counts. `configure` does not read it: what follows from it is the caller's to decide.
Whether the target is enough is a separate question: `bits` is what the caller asks of every round,
and a file whose target is below it is refused. A caller that passes 0 asks nothing here and has to
compare the file's target with the bits of its call elsewhere.

Main definitions: `Shapes`, `Sized`, `sized`, `Configured`, `configure`, `configurationDigest`.
What is not claimed: no theorem is stated here.
What is not done here, though blk::configure() does it:
 - The lines, the shapes and the digest are three arguments. That all three come from the same
   files is the caller's duty. In C++ one routine parses and hashes the same bytes.
 - That the layout fits the shapes and the codes (req_layout_fault) is not asked. It is asked for a
   model's proof alone (`linksFit`, OnBytes/Model/StagesLinks.lean), not for the files of the test
   protocols.
 - That every round has a name of the format (names_of_the_format) is not asked: the planner gives
   rounds the format's names alone, and `Given.read` tests them where the bytes are read.
 - The C++ plan also lists the trees and their openings, and refuses two ways of opening a tree that
   is marked for one list of positions (plan_open). Neither is rendered: see the head of
   OnBytes/Params/Planner.lean.
-/
import OnBytes.Hash.H
import OnBytes.Iop.Lin
import OnBytes.Iop.Link
import OnBytes.Iop.Req
import OnBytes.Params.Gate
import OnBytes.Plan.RangesGate

namespace OnBytes.Params

/-- The digest of the public files, the parameter file first. -/
def configurationDigest (files : List ByteArray) : ByteArray :=
  Fmt.configDigestW (m := Id) formatHashFastForm files

/-- What a caller's own code reads off the public files. -/
structure Shapes where
  sub : Subproofs
  layout : ReqLayout
  /-- one number for each link -/
  identifiers : List Nat
  /-- what the key's proof of the ranges looks up -/
  ranges : Plan.Shape
  /-- the range checks of one request. They are tested (`missedInTheChecks`) and enter no chain's
  parameter bytes -/
  rangeChecks : List RangeCheck

/-- What the plans of the three files (a proof, a key, an entry) are made from. -/
structure Sized where
  /-- the lines as they were given, for a caller -/
  lines : Lines
  set : Setting
  proof : ProofSized
  key : Plan.KeySized
  link : LinkSized
  entryCodes : Codes

/-- Sizes all three files: a proof, a key, an entry. After each sizing comes the test that the
finished shapes fit themselves and their codes (lin_fault, iopp_fault, req_fault, link_fault). -/
def sized (l : Lines) (x : Shapes) : Except String Sized := do
  let s := settingOf l
  -- the caller gives the matrix's number of rows twice (in C++ once: Subproofs::ranges)
  if x.sub.matrixRows != x.ranges.matrixRows then throw notAdmitted
  let proof ← orRefuse (proofSized l x.sub)
  let tests := fun (codes : Codes) (S : LinShape) =>
    linOk codes S && [S.testU, S.testOmega, S.testOwn].all fun t =>
      t.isEmpty || ioppOk codes t s.samples
  if !tests proof.codes proof.batch.shape || !reqOk proof.codes proof.request then
    throw notAdmitted
  let key ← orRefuse (Plan.keySized l x.ranges)
  if !tests key.codes key.once.shape then throw notAdmitted
  let (link, entryCodes) ← orRefuse (linkSized s l proof.batch.table {})
  if !linkOk entryCodes link.shape s.samples then throw notAdmitted
  -- A proof may list its drawn positions, in `listed` bytes each (0: it lists none). A position of
  -- the table and of the longest code of a proof's chains must then fit these bytes. Eight bytes
  -- hold every position, so only fewer are tested (verifier/src/vf_segments.inc).
  let longest := (proof.codes.base ++ proof.codes.mask).foldl (fun m c => max m c.logN) l.tableLogN
  if l.listed != 0 && l.listed < 8 && 8 * l.listed < longest then throw notAdmitted
  pure ⟨l, s, proof, key, link, entryCodes⟩

/-- What the chains of an instance hash at their start (the parameter bytes) and what their readers
follow round by round (the plans). -/
structure Configured where
  sized : Sized
  /-- the digest of the public files, for a caller; each chain's parameter bytes hold it too -/
  configuration : ByteArray
  /-- the plans of a proof's three chains -/
  proof : List Planned
  /-- the plans of a key's three chains -/
  key : List Planned
  /-- the plan of an entry's chain -/
  entry : Planned
  /-- the parameter bytes of the key's one-time chain; the next six fields hold the other chains' -/
  keyOneTime : ByteArray
  keyShared : ByteArray
  keySecond : ByteArray
  entryLink : ByteArray
  first : ByteArray
  shared : ByteArray
  second : ByteArray

/-- True if in a file's chains a round misses the target unless its proof of work counts. -/
def needsWork (plans : List Planned) : Bool := plans.any (·.needsWork)

/-- Makes the plans and the parameter bytes of all chains. The caller owes that the first three
arguments come from the same files. `bits`: what the caller asks of every round. Every refusal has
one of the C++ verifier's names for public files; on files with two faults the two programs can name
different ones. Not asked: that the layout fits (`reqLayoutOk`). -/
def configure (l : Lines) (x : Shapes) (cfg : ByteArray) (bits : Nat := 128) :
    Except String Configured := do
  let z ← sized l x
  let s := z.set
  let proof ← proofPlans z.proof x.sub
  let oneTime ← Plan.oneTimePlan z.key
  let keyShared ← sharedPlan s z.key.codes z.key.once
  let keySecond ← secondPlan s z.key.once
  let entry ← finishHeld s .once (linkPlan z.link)
  match proof with
  | [first, shared, second] =>
    let parts := sumT (z.key.ranges.x.lookups.map (·.parts.length))
    -- the conditions of OnBytes/Params/Gate.lean on random entries, mask room and range checks: on
    -- a request's links, on the key's proof of the ranges, on the tests on the table, on the checks
    if ← missedInTheLinks l z.proof x.sub first then throw notAdmitted
    if Plan.missedInTheRanges z.key then throw notAdmitted
    if missedOnTheTable l ⟨z.proof.batch, z.proof.codes, shared, second, x.sub.pendingRows, 0⟩
        ⟨z.key.once, z.key.codes, keyShared, keySecond, if parts != 0 then parts else 1, parts⟩
        z.link z.entryCodes entry then throw notAdmitted
    if missedInTheChecks l x.rangeChecks z.key.once.shape.fold.columns z.link.shape.columnsFirst
        z.proof.batch.batches then throw notAdmitted
    -- the public values of a key's one-time chain fit each other (key_fault)
    if !Plan.keyOk z.key then throw notAdmitted
    -- four of the six conditions of the reader of a proof's first chain (`First.read`,
    -- OnBytes/Params/Chains.lean): one identifier for each link, one notice at the start, a pending
    -- row, one plain scalar in the last link alone. Not asked here: one entry of the layout for
    -- each link, and a plan without an entry for a table's own sample
    let links := z.proof.request.link.length
    if x.identifiers.length != links || z.proof.request.atStart.length != 1 ||
        x.sub.pendingRows == 0 ||
        z.proof.request.link.map (·.plain) != List.replicate (links - 1) 0 ++ [1] then
      throw notAdmitted
    -- asked last: the C++ verifier asks it after all the refusals of blk::configure()
    if l.sec < bits then throw "security-bits"
    let lin := fun (codes : Codes) (S : LinShape) =>
      [("codes", spellCodes codes), ("the test on the table", spellLin S)]
    pure
      { sized := z, configuration := cfg, proof := proof,
        key := [oneTime, keyShared, keySecond], entry := entry,
        keyOneTime := Fmt.paramsBytes oneTime.plan cfg (Plan.oneTimeItems z.key),
        keyShared := Fmt.paramsBytes keyShared.plan cfg (lin z.key.codes z.key.once.shape),
        keySecond := Fmt.paramsBytes keySecond.plan cfg [],
        entryLink := Fmt.paramsBytes entry.plan cfg
          [("codes", spellCodes z.entryCodes), ("the link", spellLink z.link.shape)],
        first := Fmt.paramsBytes first.plan cfg
          (lin z.proof.codes z.proof.batch.shape ++
           [("request's shape", spellReq z.proof.request), ("layout", spellLayout x.layout),
            ("links' identifiers", spellWords x.identifiers),
            ("pending rows", spellWord x.sub.pendingRows),
            ("binding tree", spellBinding ⟨clog2 l.slots, s.saltBytes⟩)]),
        shared := Fmt.paramsBytes shared.plan cfg (lin z.proof.codes z.proof.batch.shape),
        second := Fmt.paramsBytes second.plan cfg [] }
  | _ => throw notAdmitted

end OnBytes.Params
