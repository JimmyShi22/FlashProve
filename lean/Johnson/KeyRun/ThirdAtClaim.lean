-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/KeyRun/ThirdAtClaim.lean: a check of a key file's third chain as a plain function, with
code: `decWith`, from public values of the plan, a claim, and the file's three views to yes or no.

Words. A key file holds three hash chains, here first, second and third (OnBytes/Params/Chains.lean:
one-time, shared, second). A view (`Fmt.View`) is what a reader has taken out of one chain: for each
round what the prover sent and what was drawn, and the columns that were opened in the hash trees.
The plan is what the library derives from the three public parameter files. "The program" is the
Lean port of the C++ verifier. Its blocks (type `Blk`, OnBytes/Iop/Ground.lean) are the stateful
routines in which it decides; a context is a block's state; a dry run of a block lists its rounds
and reads no file. W, Omega, claim (`LinClaim`), index-mask message, the rows (Eval) and (Dot):
OnBytes/Iop/Lin.lean. Oracle message, group, member, kept member, sample row, mask entry, ledger:
OnBytes/Iop/Ground.lean. Stage, masks that ride: OnBytes/Iop/Prox.lean. Sealing round:
OnBytes/Proof/Tail.lean.

What is checked. The third chain is a proximity test on one group of three oracle messages: the
index-mask message, W and Omega. `decWith` runs no block: there is no value of the type `Blk`, no
context and no dry run beneath it. It goes in these steps:
  1. `into3` reads off the first two views what the third chain needs of them (`Into3`). The rounds
     are found by the names that the plans give them.
  2. `bat3` builds a statement from the public shapes: the oracle messages of three prover's
     messages, and one group of three members. It makes each member's sample rows (`sendRows`), the
     rows (Eval) and (Dot), the layout, and the one row into which the first round's drawn element
     batches them all.
  3. `sideOf` holds the third view's opened columns against the list of those that the test looks
     for (`wanted`) and lays the three members' columns into the first stage's column (`layFirst`).
  4. `Side.yes` is `Fmt.M1.iopp` (Fmt/M1Dec.lean: the proximity test of the library's first toy
     protocol), at that toy's six functions (`Fmt.M1.blocksA`, Fmt/M1CsFast.lean), on the batched
     row, on the third view's rounds behind the first, all of which it must use up, and on these
     columns.
Every function of the program that is called here has a plain type: none is a block. They are
`Send.cube`, `Send.seedsOf`, `Send.form` (OnBytes/Iop/Send.lean); `linMessageW`, `linMessageOmega`,
`linLayW`, `linLayOmega`, `linEvalRow`, `linDotRow`, `LinShape.ownSplitNeeded`
(OnBytes/Iop/Lin.lean); `Statement.layout` (OnBytes/Iop/Ground.lean); `Bat.combine`
(OnBytes/Iop/Bat.lean); `Form.writeOut` (OnBytes/Iop/Tensor.lean); and small helpers on field
elements. Of Fmt/: `iopp`, `ofView`, `sentOf`, `listOf`. `sendRows` is written after the text of the
block `Send.verify`; `bat3`, `layFirst`, `wanted` and `sideOf` stand in the place of blocks and are
written anew.

What it is not.
  - No theorem is stated. No equation ties `decWith` to a protocol of which this library states
    soundness, or to the program's decision. Nothing on soundness.
  - It checks the third chain alone, and THE CLAIM IS AN ARGUMENT: what the first chain leaves is
    not made here (Johnson/KeyRun/Third.lean puts it in).
  - `iopp` was written for a toy protocol, and is called here without that toy's test on sizes,
    `stagesOK`. Its file's head says of the C++ programs: "That this is what the programs decide is
    not proved".
  - A view holds no root, nonce, salt or path: proof of work, hashes and openings under a root are
    the reader's matter. So is that the words of a field's element lie below the prime: the
    program's readers refuse other words (the head of OnBytes/Maker/OkView.lean); nothing here does.
    So is from which tree a column comes: the three members' trees and the second stage's all stand
    under the key 0; `sideOf` tells them apart by their order, and holds position and width. So is
    that a drawn position lies below its range: `wanted` takes it modulo the tree's length.
  - Known differences from the program's run of this chain, by reading; the list may not be whole.
    (1) The test is another text: the program runs `ioppVerify` (OnBytes/Iop/Prox.lean).
    (2) FEW TESTS ON THE PLAN ALONE ARE MADE HERE: the names "SEND seed" and "LIN point" in the
        first two chains, the name and the count of rows at "BAT", one round of positions for each
        stage, the first stage's k and h, main rows over the extension field, that the messages have
        shapes, answers and room for their pads, and that W and Omega have one code (where they
        differ the program goes on with a split; here it is a no). Built in: one answer to a sample,
        masks ride, the first fold's mask comes ahead in W's leaf, no stage's code is longer than
        2^32. Where a shape names a code that the plan does not have, the code (0, 0, 0) is taken
        without a word (`getD .. default` in `depthOf`, `stOf`, `wanted`); array and index are the
        plan's, so no view can bring that about. `thirdPublicOk` (Johnson/KeyRun/Third.lean) asks
        more of the plan; its head says what.
    (3) The tests that `Blk.addRow` makes on the rows (Eval) and (Dot) are not made: on the places
        that a row names, and that its coefficient is 0 at every entry that masks an answer. Nor is
        the test that the batched row's tables have the group's lengths (`foldRowOk`,
        OnBytes/Iop/Fold.lean): `gRow` writes the row out at the layout's lengths and cuts it.
    (4) There is no ledger: that each mask entry is spent once is not tested. Nor is the program's
        test at a chain's end asked, that every group has been tested (`Blk.requireAllTested`).
    (5) Of the third view it asks just the wanted columns and that all rounds are used up. Of a
        round it asks only what it reads: other items or positions in the round "BAT" pass, and
        matrix entries or a digest in any round; `sentOf` passes over an item that is no element,
        and takes an answer for an element. Of the first two views it asks nothing beyond the rounds
        that it reads, and it takes the round after each "SEND seed" as the answers' round, whatever
        its name.
    (6) Which round "SEND seed" is whose is taken from its place among the plan's rounds of that
        name: the first and the last of the first chain's, the second of the second chain's.
    (7) That a draw is not 0 is tested of the factors of the three members' seeds, and of no draw of
        the third chain. The program tests the factor at every "SEND seed" (`Send.verify`).


-/
import Fmt.M1CsFast
import OnBytes.Iop.Lin
import OnBytes.Iop.Bat
import OnBytes.Params.Chains

set_option autoImplicit false

namespace Johnson.KeyRun.Third

open OnBytes OnBytes.Params

/-- The plan's public values that the check reads. -/
structure Pub3 where
  codes : Codes
  S : LinShape
  /-- the index-mask message -/
  idx : OracleNotice
  /-- the rounds of the first chain's plan -/
  e₁ : List Fmt.Entry
  /-- those of the second chain's -/
  e₂ : List Fmt.Entry
  /-- those of the third chain's -/
  e₃ : List Fmt.Entry

def pubOf (k : KeyChains) : Pub3 :=
  ⟨k.shared.codes, k.shared.lin, k.oneTime.indexMasks, k.oneTime.given.rounds,
    k.shared.given.rounds, k.second.given.rounds⟩

/-- The numbers of the plan's rounds of one name. -/
def named (es : List Fmt.Entry) (name : String) : List Nat :=
  (es.zipIdx.filter fun e => e.1.name == name).map (·.2)

/-- The elements that round i of a view has drawn; none if there is no such round. -/
def drawnAt (v : Fmt.View) (i : Nat) : List E :=
  ((v.rounds[i]?).map fun r => r.drawn.elems.map E.ofTriple).getD []

/-- The elements that the prover sent in round i of a view; none if there is no such round. -/
def sentAt (v : Fmt.View) (i : Nat) : List E :=
  ((v.rounds[i]?).map fun r => (Fmt.M1.sentOf r.vals).map E.ofTriple).getD []

/-- The sample rows of one prover's message. msg: its oracle messages with their numbers. drawn:
what its round of seeds has drawn. ys: the answers, in order. Nothing if the numbers do not fit or a
seed's factor is 0. -/
def sendRows (codes : Codes) (msg : List (Nat × OracleShape)) (drawn ys : List E) :
    Option (List (Nat × Array Row)) := do
  let todo := msg.filter fun m => m.2.answers != 0
  guard (!todo.isEmpty)
  let bits := todo.foldl (fun b m => max b (Send.cube codes m.2).bits) 0
  let answers := todo.foldl (fun a m => max a m.2.answers) 0
  let seeds ← Send.seedsOf bits answers drawn
  guard (seeds.all fun s => !isZeroE s.beta)
  guard (ys.length == (todo.map (·.2.answers)).sum)
  let r ← todo.foldlM (fun (acc : List (Nat × Array Row) × List E) m => do
    let rows ← (List.range m.2.answers).mapM fun i => do
      let seed ← seeds[i]?
      let row ← Send.form codes m.2 m.1 seed i
      let y ← acc.2[i]?
      pure { row with target := y }
    pure (acc.1 ++ [(m.1, rows.toArray)], acc.2.drop m.2.answers)) ([], ys)
  pure r.1

/-- What `bat3` builds for the test. -/
structure Built where
  st : Statement
  input : RunInput
  /-- the element that the batching round has drawn; the check does not read this field -/
  x : E
  /-- the batched row -/
  row : GroupRow
  /-- W's number among the oracle messages; not read either -/
  w : Nat
  /-- Omega's; not read either -/
  omega : Nat
  /-- the number of the fresh mask that is sent ahead in W's message, if one is -/
  rider : Option Nat

/-- The shape of the group's member number m. -/
def Built.shapeAt (b : Built) (m : Nat) : OracleShape :=
  ((b.st.oracles[b.input.layout.members.getD m noId]?).map (·.shape)).getD default

/-- The oracle messages of a prover's message, numbered from `first` on. -/
def numbered (first : Nat) (a : Array OracleNotice) : List (Nat × OracleShape) :=
  a.toList.zipIdx.map fun n => (first + n.2, n.1.shape)

/-- **What the third chain takes of the two chains before it.** -/
structure Into3 where
  /-- what the first chain leaves: the claim on W -/
  claim : LinClaim
  /-- the shared point: what the second chain's first round has drawn -/
  psi : List E
  /-- the seeds drawn for the index-mask message -/
  seedI : List E
  /-- the answers sent for it -/
  ansI : List E
  /-- the same for W's message -/
  seedW : List E
  ansW : List E
  /-- the same for Omega's message -/
  seedO : List E
  ansO : List E

/-- These values, but for the claim, read off the first two views at rounds that the plans name. -/
def into3 (P : Pub3) (claim : LinClaim) (v₁ v₂ : Fmt.View) : Except String Into3 := do
  let s₁ := named P.e₁ "SEND seed"
  let s₂ := named P.e₂ "SEND seed"
  let some iI := s₁.head? | throw "chain 1's plan has no round SEND seed"
  let some iW := s₁.getLast? | throw "chain 1's plan has no round SEND seed"
  let some iO := s₂[1]? | throw "chain 2's plan has no second round SEND seed"
  if (P.e₂.head?.map (·.name)) != some "LIN point" then
    throw "chain 2's first round is not LIN point"
  pure ⟨claim, drawnAt v₂ 0, drawnAt v₁ iI, sentAt v₁ (iI + 1), drawnAt v₁ iW, sentAt v₁ (iW + 1),
    drawnAt v₂ iO, sentAt v₂ (iO + 1)⟩

/-- **The batching round's step**: the row that reaches the test, from the public values, what has
been taken of the first two chains and the element x that the round has drawn. It refuses numbers
that do not fit, a seed's factor 0, and a mask term of the claim on another oracle message than
number 0. It tests no other value. -/
def bat3 (P : Pub3) (I : Into3) (x : E) : Except String Built := do
  let S := P.S
  let claim := I.claim
  if S.ownSplitNeeded then throw "W and Omega differ in code: this check has no split"
  let some mW := linMessageW S | throw "W's message has no shape"
  let mO := linMessageOmega S
  let nI := numbered 0 #[P.idx]
  let nW := numbered 1 mW
  let nO := numbered (1 + mW.size) mO
  let w := 1
  let omega := 1 + mW.size
  let some rI := sendRows P.codes nI I.seedI I.ansI
    | throw "the index-mask message's sample rows cannot be made"
  let some rW := sendRows P.codes nW I.seedW I.ansW | throw "W's sample rows cannot be made"
  let some rO := sendRows P.codes nO I.seedO I.ansO | throw "Omega's sample rows cannot be made"
  let rows := rI ++ rW ++ rO
  let oracles : Array Oracle := ((nI ++ nW ++ nO).map fun n =>
    ({ shape := n.2, sampled := n.2.answers != 0,
       sampleRows := ((rows.find? fun r => r.1 == n.1).map (·.2)).getD #[] } : Oracle)).toArray
  let members : Array Nat := #[0, w, omega]
  let st : Statement :=
    { codes := P.codes, oracles := oracles,
      groups := #[{ code := S.w.code, maskCode := S.ownMaskCode, members := members,
                    kept := #[false, false, false] }] }
  if !(claim.masks.all fun m => m.oracle == 0) then
    throw "a mask term of the claim names another message than number 0"
  let some eval := linEvalRow S claim w (linLayW P.codes S) | throw "the row (Eval) cannot be made"
  let some dot := linDotRow S claim.g I.psi omega (linLayOmega P.codes S) w (linLayW P.codes S)
    | throw "the row (Dot) cannot be made"
  let some L := st.layout 0 | throw "the group has no layout"
  let samples := members.foldl (fun a o => a ++ ((st.oracles[o]?).map (·.sampleRows)).getD #[]) #[]
  let input : RunInput := ⟨L, #[eval, dot] ++ samples⟩
  if (P.e₃.head?.map (·.rows)) != some input.rows.size then
    throw s!"the plan's round BAT does not count {input.rows.size} rows"
  let some row := Bat.combine st 0 input x | throw "the rows cannot be batched"
  if !row.kept.isEmpty then throw "the batched row has a kept member"
  pure ⟨st, input, x, row, w, omega, if S.masksAhead then some mW.size else none⟩

/-- `into3`, then `bat3` at what the third view's first round has drawn. -/
def build (P : Pub3) (claim : LinClaim) (v₁ v₂ v₃ : Fmt.View) : Except String Built := do
  let I ← into3 P claim v₁ v₂
  if (P.e₃.head?.map (·.name)) != some "BAT" then throw "chain 3's first round is not BAT"
  let [x] := drawnAt v₃ 0 | throw "chain 3's first round does not draw one element"
  bat3 P I x

/-- The batched row as plain arrays. -/
def gRow (b : Built) : Fmt.M1.GRow :=
  let L := b.input.layout
  ⟨(b.row.c.writeOut (L.k + L.logEll)).map fun x => x.triple,
    (Array.range (2 ^ (L.h + L.logEllZk))).map fun i => (b.row.d.getD i zeroE).triple,
    b.row.target.triple⟩

/-- An opened column as a view holds it: key, position, words. -/
abbrev Ent : Type := Nat × Nat × List UInt64

/-- The words of the column at the position x among r. -/
def colIn (r : List Ent) (x : Nat) : Option (List UInt64) :=
  (r.find? fun o => o.2.1 == x).map (·.2.2)

/-- The words of an oracle message's symbols in a leaf. -/
def wordsOf (s : OracleShape) : Nat := s.mainRows * s.mainDeg + 3 * s.maskRows

/-- The logarithm of the length of a member's tree. -/
def depthOf (codes : Codes) (s : OracleShape) : Nat :=
  if s.mainRows != 0 then (codes.base.getD s.code default).logN
  else (codes.mask.getD s.maskCode default).logN

/-- **The first stage's column at the position x**, from the three members' columns: the group's
main rows 0 to mE - 1 (0 for a row that no member sent), its 2^h mask rows, and the 2^h fresh rows,
which lie behind W's own symbols in W's leaf. runs: the members' columns, in the members' order. -/
def layFirst (b : Built) (mE : Nat) (runs : List (List Ent)) (x : Nat) : Option (List UInt64) := do
  let L := b.input.layout
  let sh := b.shapeAt
  let cols ← (List.range L.members.size).mapM fun m =>
    colIn (runs.getD m []) (x % 2 ^ depthOf b.st.codes (sh m))
  let pick (firsts : Array (Option Nat)) (rows off : Nat → Nat) (r : Nat) : List UInt64 :=
    match (List.range L.members.size).find? fun m =>
      match firsts.getD m none with
      | some f => f ≤ r && r < f + rows m
      | none => false with
    | some m => (((cols.getD m []).drop (off m + 3 * (r - (firsts.getD m none).getD 0))).take 3)
    | none => [0, 0, 0]
  let main := (List.range mE).flatMap (pick L.mainFirst (fun m => (sh m).mainRows) fun _ => 0)
  let mask := (List.range (2 ^ L.h)).flatMap
    (pick L.maskFirst (fun m => (sh m).maskRows) fun m => (sh m).mainRows * (sh m).mainDeg)
  let fresh := ((cols.getD 1 []).drop (wordsOf (sh 1))).take (3 * 2 ^ L.h)
  pure (main ++ mask ++ fresh)

/-- What `iopp` takes. -/
structure Side where
  V : Fmt.M1.View
  st : List Fmt.M1.Stage
  G : Fmt.M1.GRow
  /-- the main rows that were sent at the first stage -/
  mE : Nat

/-- A stage of the plan's test, with t positions to draw, as `iopp` takes it. -/
def stOf (c : Codes) (s : IoppStage) (t : Nat) : Fmt.M1.Stage :=
  let b := c.base.getD s.code default
  let z := c.mask.getD s.maskCode default
  ⟨⟨b.logN, b.ell, b.r⟩, ⟨z.logN, z.ell, z.r⟩, s.k, s.h, t⟩

/-- The words of a column of a later stage's tree: 2^k main symbols, 2^h carried and 2^h fresh mask
symbols; at the last stage two main and two mask symbols. -/
def laterWidth (s : IoppStage) (last : Bool) : Nat :=
  if last then 12 else 3 * 2 ^ s.k + 6 * 2 ^ s.h

/-- Cuts a list into pieces of the given lengths. Nothing unless they use it up. -/
def cutBy {α : Type} : List Nat → List α → Option (List (List α))
  | [], [] => some []
  | [], _ :: _ => none
  | n :: ns, l => if l.length < n then none else (cutBy ns (l.drop n)).map fun t => l.take n :: t

/-- **The columns that the test looks for**, in the order in which a view is to show them, as (key,
position, words). lists: the positions drawn, stage by stage. At the first stage's draw: each
member's tree, in the members' order, under the key 0, at the format's list (`Fmt.listOf`) of the
drawn positions modulo the tree's length. At each later stage's draw: that stage's own tree, under
its number among the chain's own trees. -/
def wanted (P : Pub3) (b : Built) (lists : List (List Nat)) : List (List (Nat × Nat × Nat)) :=
  let L := b.input.layout
  let n := L.members.size
  let sh := b.shapeAt
  let width (m : Nat) : Nat :=
    wordsOf (sh m) + (if m == 1 && b.rider.isSome then 3 * 2 ^ L.h else 0)
  let later := P.S.testOwn.drop 1
  ((List.range n).map fun m =>
    (Fmt.listOf ((lists.getD 0 []).map (· % 2 ^ depthOf b.st.codes (sh m)))).map
      fun x => (0, x, width m)) ++
  (later.zipIdx.map fun s =>
    (Fmt.listOf ((lists.getD (s.2 + 1) []).map
      (· % 2 ^ (P.codes.base.getD s.1.code default).logN))).map fun x =>
        (s.2, x, laterWidth s.1 (s.2 + 1 == later.length)))

/-- What `iopp` takes, from what was built and the third view. It refuses unless the view
shows just the columns of `wanted`, in that order and at those widths. -/
def sideOf (P : Pub3) (b : Built) (v₃ : Fmt.View) : Except String Side := do
  let L := b.input.layout
  let n := L.members.size
  let sh := b.shapeAt
  if !((List.range n).all fun m => (sh m).mainRows == 0 || (sh m).mainDeg == 3) then
    throw "a member's main rows are over the base field"
  let mE := (List.range n).foldl (fun a m =>
    match L.mainFirst.getD m none with
    | some f => max a (f + (sh m).mainRows)
    | none => a) 0
  let later := P.S.testOwn.length - 1
  let ts := (P.e₃.filter fun e => e.poss != 0).map (·.poss)
  if ts.length != P.S.testOwn.length then
    throw "the plan's rounds that draw positions are not one for each stage"
  if (P.S.testOwn.head?.map fun s => (s.k, s.h)) != some (L.k, L.h) then
    throw "the first stage's k, h are not the layout's"
  let lists := (P.e₃.zipIdx.filter fun e => e.1.poss != 0).map fun e =>
    ((v₃.rounds[e.2]?).map (·.drawn.poss)).getD []
  let want := wanted P b lists
  if v₃.opened.map (fun o => (o.1, o.2.1, o.2.2.length)) != want.flatten then
    throw "the view's opened columns are not just those that the test looks for, in their order"
  let some runs := cutBy (want.map (·.length)) v₃.opened | throw "the opened columns cannot be cut"
  let first ← (Fmt.listOf (lists.getD 0 [])).mapM fun x =>
    match layFirst b mE runs x with
    | some w => pure ((0 : Nat), x, w)
    | none => throw "a member's column is missing at a drawn position"
  let rest := (List.range later).flatMap fun j =>
    (runs.getD (n + j) []).map fun o => (j + 1, o.2.1, o.2.2)
  pure ⟨⟨(Fmt.M1.ofView v₃).rounds.drop 1, first ++ rest⟩,
    (P.S.testOwn.zip ts).map fun p => stOf P.codes p.1 p.2, gRow b, mE⟩

/-- `iopp` on what `sideOf` has laid. -/
def Side.yes (s : Side) : Bool :=
  Fmt.M1.iopp Fmt.M1.blocksA .two s.V s.st 0 0 s.mE s.G s.V.rounds

/-- **A check of the third chain, at a claim.** -/
def decWith (P : Pub3) (claim : LinClaim) (v₁ v₂ v₃ : Fmt.View) : Bool :=
  match build P claim v₁ v₂ v₃ with
  | .error _ => false
  | .ok b =>
    match sideOf P b v₃ with
    | .error _ => false
    | .ok s => s.yes

end Johnson.KeyRun.Third
