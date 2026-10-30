-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/Send.lean: the block SEND on the verifier's side.
C++ counterpart: blocks/iop/send.h.

The prover sends oracle messages. The verifier answers with the seeds of an out-of-domain sample: s
seeds, where s is the number of answers in the oracle messages' shapes (the largest, if they differ;
0 marks a message that is not sampled). The prover begins its next message with the answers, as many
for each sampled oracle message as its shape says. Answer i is the value, under seed i, of a random
linear form on the whole message that the oracle message encodes. The equation "form of the message
= answer" is kept as an open row, the sample row, and every proximity test on the oracle message
takes it in.
All oracle messages of one prover's message share the seeds: a seed's point has as many coordinates
as the largest cube, and each message uses the first coordinates, as many as its own cube has. The
draws come as point, factor,
point, factor; the answers come by oracle message, then by number of the answer.

Why. Beyond half the minimum distance a committed word can be close to several code words, and a
prover could rely on one of them in one place and on another elsewhere. The seed is drawn after the
word is fixed, and the protocol's argument is that, for all but a small fraction of the seeds, two
different messages near one word give different answers. So the answer is intended to fix which of
these messages the prover is held to.

The form. The entries of a message are placed on one cube. The main table (row bits low, rows beyond
the real ones zero) has A_m index bits, the mask table A_z. With one table only, the cube has that
many bits and entry j has the weight eq(j, z). With both, the cube has max(A_m, A_z) + 1 bits: the
top bit is 0 for the main table and 1 for the mask table, and each table sits in the low bits. For
each answer one element of the extension field in the message is set apart as the pad of that
answer: it has the weight 0 under every z, the factor beta in its own answer and 0 in the others.
The pads are the last s places of the last mask row; without mask rows, the last s places of the
last main row (3 s places there if the main rows are over the base field, read through the basis 1,
X, X^2).
 - Every entry that is no pad has its weight under z, whether or not a claim reads it: an entry
   without a weight could differ between two messages that no seed tells apart.
 - The factor beta is not 0: with 0, two messages that differ in a pad only would not be told apart.
 - No row that Blk.addRow takes reads a pad: it tests that the coefficient there is 0.

SEND tests no equation. It requires that no seed's factor is 0. Rounds: "SEND seed" and, unless the
caller closes the answers' round itself, "SEND answer".

Main definitions: SampleCube, Send.cube, PadPlace, Send.pad, Send.freeMaskEntries, SampleSeed,
Send.form, Send.verify, sendVerify.

Not claimed here: soundness or hiding. No theorem is stated here.
-/
import OnBytes.Iop.Ground
import OnBytes.Chain.Lists

namespace OnBytes

/-- How the entries of one oracle message are placed on its cube. -/
structure SampleCube where
  hasMain : Bool := false
  hasMask : Bool := false
  mainRowBits : Nat := 0
  /-- all index bits of the main table -/
  mainBits : Nat := 0
  maskRowBits : Nat := 0
  /-- all index bits of the mask table -/
  maskBits : Nat := 0
  /-- the coordinates of the point that the message reads -/
  bits : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- One entry of the pad: it belongs to one answer, with the coefficient beta times basis. -/
structure PadPlace where
  part : Part
  index : Nat
  answer : Nat
  basis : E
  deriving Inhabited

/-- The seed of an out-of-domain sample: a point and a factor. The factor must not be 0. The
structure does not enforce it: Send.verify and foldeqRequire test it. -/
structure SampleSeed where
  z : List E
  beta : E
  deriving Inhabited

namespace Send

/-- The cube of an oracle message. -/
def cube (codes : Codes) (s : OracleShape) : SampleCube :=
  let hasMain := decide (0 < s.mainRows)
  let hasMask := decide (0 < s.maskRows)
  let mainRowBits := if hasMain then ceilLog2 s.mainRows else 0
  let mainBits := if hasMain then mainRowBits + (codes.base.getD s.code default).logEll else 0
  let maskRowBits := if hasMask then ceilLog2 s.maskRows else 0
  let maskBits := if hasMask then maskRowBits + (codes.mask.getD s.maskCode default).logEll else 0
  { hasMain := hasMain, hasMask := hasMask, mainRowBits := mainRowBits, mainBits := mainBits,
    maskRowBits := maskRowBits, maskBits := maskBits,
    bits := if hasMain && hasMask then max mainBits maskBits + 1 else mainBits + maskBits }

/-- The places of the pad, by increasing index. Nothing if the row is too short for the pad. -/
def pad (codes : Codes) (s : OracleShape) : Option (List PadPlace) :=
  let c := cube codes s
  let part : Part := if c.hasMask then .mask else .main
  let rows := if c.hasMask then s.maskRows else s.mainRows
  let rowBits := if c.hasMask then c.maskRowBits else c.mainRowBits
  let len :=
    if c.hasMask then (codes.mask.getD s.maskCode default).ell
    else (codes.base.getD s.code default).ell
  let each := if c.hasMask || s.mainDeg == 3 then 1 else 3
  if len < each * s.answers then none
  else
    some ((List.range s.answers).flatMap fun i =>
      (List.range each).map fun t =>
        let place := len - each * s.answers + each * i + t
        { part := part, index := (rows - 1) + place * 2 ^ rowBits, answer := i,
          basis := thetaE t })

/-- How many entries the ledger of a sampled message's mask rows gives out: all below the first
place of the pad, which is at the end of the last row. In an index the row's number is low, so every
row gives its places before the pad's, and every row except the last gives one place more. -/
def freeMaskEntries (maskRows ellZk answers : Nat) : Nat :=
  if maskRows == 0 || ellZk < answers then 0
  else maskRows * (ellZk - answers) + (maskRows - 1)

/-- The least number of mask rows, up to 4096, whose free entries (freeMaskEntries) are at least
entries; 0 if no such number has. -/
def maskRowsFor (entries ellZk answers : Nat) : Nat :=
  match (List.range 4096).find? fun i => entries ≤ freeMaskEntries (i + 1) ellZk answers with
  | some i => i + 1
  | none => 0

/-- The factor in front of the equality vector for one of the two tables: it fixes the cube's bits
above the table. -/
def front (z : List E) (c : SampleCube) (tableBits : Nat) (mask : Bool) : E :=
  if !(c.hasMain && c.hasMask) then oneE
  else
    let top := z.getD (c.bits - 1) zeroE
    ((z.take (c.bits - 1)).drop tableBits).foldl (fun f x => mulE f (subE oneE x))
      (if mask then top else subE oneE top)

/-- The left side of the sample row of o for one answer. Its coefficient is eq(., z) on every entry
that is no pad, beta times basis on the pad of this answer, and 0 on the pads of the other answers.
Not tested here (send.h, Send::form, tests both): that the seed's point has at least the cube's
coordinates, and that beta is not 0. Send.verify, its only caller in the program, ensures both. -/
def form (codes : Codes) (s : OracleShape) (o : Nat) (seed : SampleSeed) (answer : Nat) :
    Option Row := do
  let c := cube codes s
  let places ← pad codes s
  let onMain := Tensor.eq (seed.z.take c.mainBits) (front seed.z c c.mainBits false)
  let onMask := Tensor.eq (seed.z.take c.maskBits) (front seed.z c c.maskBits true)
  let row0 : Row := places.foldl (fun (r : Row) p =>
    let underZ := (if p.part == .main then onMain else onMask).entry p.index
    r.addUnit o p.part p.index
      (subE (if p.answer == answer then mulE seed.beta p.basis else zeroE) underZ))
    { kind := .sample }
  let row1 := if c.hasMain then row0.add o .main onMain else row0
  pure (if c.hasMask then row1.add o .mask onMask else row1)

/-- Cuts the elements that a round of seeds has drawn into n seeds, each of bits coordinates and a
factor. Nothing unless there are exactly n (bits + 1) elements. -/
def seedsOf (bits : Nat) : Nat → List E → Option (List SampleSeed)
  | 0, [] => some []
  | 0, _ :: _ => none
  | n + 1, l =>
    match l.drop bits with
    | [] => none
    | beta :: rest => (seedsOf bits n rest).map fun t => ⟨l.take bits, beta⟩ :: t

/-- The answers of o's sample have been received: from now on rows, groups and masks may name o. The
mask entries below the first place of the pad are free. With several answers and several mask rows,
a few entries beside the pad stay unused; they have their weight under z like all others. -/
def admit (o : Nat) (rows : Array Row) : Blk Unit := do
  let S ← Blk.statement
  let x ← Blk.oracle o
  let s := x.shape
  let places ← Blk.get (pad S.codes s)
  Blk.must (!x.sampled && rows.size == s.answers && decide (1 ≤ s.answers))
  let free := freeMaskEntries s.maskRows (S.codes.mask.getD s.maskCode default).ell s.answers
  Blk.onOracle o fun x => { x with
    sampled := true, sampleRows := rows, pad := places.map fun p => (p.part, p.index),
    ledger :=
      if 0 < s.maskRows then
        some { next := 0, left := free, rows := max s.maskRows 1, logRows := ceilLog2 s.maskRows }
      else none }

/-- Draws the seeds and receives the answers for those of the oracle messages ids, all of the
prover's open message, that have answers. Fails if none has answers, if one has been sampled before,
if they do not come in the order of sending, if a row is too short for its pad, or if the round does
not draw one point and one factor for each answer. On a view it also fails if a factor is 0.
ownRound: SEND closes the round of the answers itself; otherwise the caller answers them with a
verifier's message of its own. -/
def verify (ids : Array Nat) (ownRound : Bool := true) : Blk Unit := do
  let S ← Blk.statement
  let todo := ids.toList.filter fun o => ((S.oracles[o]?).map (·.shape.answers)).getD 0 != 0
  Blk.must (!todo.isEmpty && Fmt.increasing todo)
  Blk.must (todo.all fun o => ((S.oracles[o]?).map (!·.sampled)).getD false)
  let shapes ← Blk.get (todo.mapM fun o => (S.oracles[o]?).map (·.shape))
  let bits := shapes.foldl (fun b s => max b (cube S.codes s).bits) 0
  let answers := shapes.foldl (fun a s => max a s.answers) 0
  let drawn ← Blk.close "SEND seed" .seeds answers
  let seeds ← Blk.get (seedsOf bits answers (drawn.elems.map E.ofTriple))
  Blk.test (seeds.all fun s => !isZeroE s.beta)
  for (o, s) in zipT todo shapes do
    let mut rows : Array Row := #[]
    for i in List.range s.answers do
      let seed ← Blk.get seeds[i]?
      let row ← Blk.get (form S.codes s o seed i)
      let y ← Blk.recvAnswer
      rows := rows.push { row with target := y }
    admit o rows
  if ownRound then Blk.closeEmpty "SEND answer"

end Send

/-- SEND for a verifier: receives the roots of all oracle messages of the present prover's message,
draws the seed and receives the answers. Returns the messages' numbers, in the order given. -/
def sendVerify (notices : Array OracleNotice) (ownRound : Bool := true) : Blk (Array Nat) := do
  let ids ← Blk.receiveOracles notices
  Send.verify ids ownRound
  pure ids

end OnBytes
