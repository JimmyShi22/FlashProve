-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/RoundsOfPlan.lean: the declared rounds of a key file's and of a proof file's three chains,
computed from the three public files. No block of the verifier program is run for it, neither dry
nor on a view.

A part of D: definitions alone; nothing proved of it; D as a whole has not run on a real file. (D:
the description of the protocol: the rounds' data as functions of the plan, and a decision on a
file's three views. No file has it whole. This file has the rounds' data.) Every definition can be
evaluated.

A declared round (`Fmt.DeclaredRound`, Decl/Declared.lean) is its entry of the plan, the stored tables
that it opens and the other trees that it opens. Its kind and the cut of its message follow from the
entry (`Fmt.kindOf`, `Fmt.Entry.cut`). `Params.declared` (OnBytes/Params/DeclaredOf.lean) and the
makers of a file's data (`dryKey`, `dryProof`, OnBytes/Maker/Files.lean) take the openings from a
dry run of the verifier program's blocks. Here
they are computed from the plans and from the lists of what is sent. The chains are named as in the
declared structure: first (number 0), shared (number 1), second (number 2).

What is called. `Model.Verify.planned`, the routine by which the program makes the seven chains'
parameter bytes from the public files; it calls the format's hash for the files' digest and, in
`publicOf`, the second hash function (Limits, "The hash").
`sendsOf` (Johnson/G/Sends.lean). Functions of public shapes that the program's blocks also call:
`layTrees` (OnBytes/Iop/Ground.lean), `foldMaskNotice` (OnBytes/Iop/Fold.lean), `ioppFoldShape`
(OnBytes/Iop/Prox.lean), `IndexShape.tree` (OnBytes/Iop/Foldeq.lean).

Where each field comes from.
  entry: the plan's rounds (`Fmt.Plan.rounds`: the entry RECORD is no round).
  The trees that a chain sends (`treesSent`): `sendsOf` lists the oracle messages of each "SEND
    seed"; `layTrees` (R7.12) says which of them share a tree. A tree's depth is its `logN`. A
    column holds its main and its mask symbols. One more tree: the planner gives the first fold of
    Omega's test a root of its own (`linPlanShared`, OnBytes/Params/DeriveLin.lean), for the mask
    that this fold sends itself (`ownMasks`). `treesSent` refuses unless each round gets as many
    trees as its entry has roots.
  What a sending is (`sendTag`): read off the label that `sendsOf` gives it. At a label that
    `sendTag` does not know, `declOf` refuses.
  opens: only rounds that draw positions open trees. The lists of trees below are put at these
    rounds in order (`fill`). In the two examples the rounds have the names given here.
      A proof's first chain (`frameOpens`). The chain has a group for each link and then the group
        of the last test; `sendsOf` labels that last group's sending as one link more. "LOC" number
        k, from 0: the trees that link k has sent, but for the tree of what rides at the start
        (`atStart`). The first "CS": the trees of the last test's group. Each later "CS" or "BASE":
        the tree of the next code switch of the last test.
      A key's first chain (`onceOpens`). The first "CS": the multiplicities' trees. Each later "CS"
        or "BASE": the tree of the next code switch of the ranges' test.
      A shared chain (`sharedOpens`). "LOC": the stored table, and no tree. The first "CS" of the
        folded row's test: the folded row's trees and, with a split, the split's tree; without a
        split, Omega's trees. With a split, the first "CS" of Omega's test: all trees of Omega's
        sending and the fold's own mask. Each later "CS" or "BASE": the next code switch's tree.
      A second chain (`secondOpens`). The first "CS": the trees that are taken over: the first
        chain's input and W, the shared chain's Omega. The input is a key's index-mask message; in
        a proof it is what rides at the start. Each later "CS" or "BASE": the tree of the next code
        switch of the own test. The chain's own trees are numbered from the first chain's number of
        trees plus 1 (R13.7): the 1 is the one tree that is taken over from the shared chain. That
        `secondOpens` finds just one tree of Omega there is not tested.
  stored: one table, at the shared chain's first round of positions: the tree and the salt of the
    table's shape; the statement's item 0 (as `readTail` asks for it, OnBytes/Proof/Tail.lean); from
    the draw 0 on (OnBytes/Iop/Foldeq.lean); as many draws as the fold has columns.
`fill` also refuses if a round of positions would open nothing, and `fileOf` if a tree that a chain
sends would be opened nowhere in the file.

Main names.
  `SendTag`, `sendTag`: what a sending is.
  `Sent`, `treesSent`: the trees that a chain sends.
  `fill`, `fileOf`, `declKOf`, `declPOf`, `declOf`: the declared rounds.
  `writtenOf`, `roundsOf`: the same as written rounds (`Params.Rounds`), by `Fmt.DeclaredRound.round`. A
    tree that is taken over gets the stand-ins `Three.tagRoot`, `Three.tagRun` for its root and its
    chain's run value, as the written dry lists have them (Johnson/G/DryProofLit.lean).
  `depthOf`: the stored table's depth.
  `Made`, `madeOf`: what the planner and `sendsOf` make of the three files. `declKOf`, `declPOf`,
    `roundsAt`, `dataKAt`, `dataPAt` start from it, so that it need be made once only.
  `dataKOf`, `dataPOf`: the data of the two files' rounds (`WholeD`), after the makers' own tests
    (`dataAt`, OnBytes/Maker/Files.lean): where a test fails they are the data of three empty lists.

Evidence: the head of Johnson/G/RoundsOfPlanGuard.lean.

Limits. No theorem is stated.
  Which trees the first round of positions of a test opens, and that the later ones follow the code
    switches in order, was read off the written dry lists (Johnson/G/DryKeyLit.lean,
    DryProofLit.lean: two files at two examples). The guard file holds the functions against these
    same lists. So at the two examples it shows only that the rule is typed as it was read. What
    else the functions were held against, and what never varied there, is told in the guard file's
    head.
  The clause for a shared chain without a split follows the planner's text: the folded row's group
    is then the folded row and Omega (OnBytes/Params/DeriveLin.lean). Both examples have a split, so
    no test that a build runs reaches that clause.
  `ownMasks` gives every "FOLD epsilon" with a root the mask of the first stage of Omega's test, and
    `sharedOpens` has it opened at that test. The planner gives no other fold a root
    (`masksAhead := true`, OnBytes/Params/DeriveLin.lean). If it did, that tree's shape and round
    would be wrong here, and nothing here would notice. The planner also lets all later masks ride
    (`choice := ⟨true⟩`) and never splits W from Omega (`testOwnOmega := []`). Without riding masks
    `treesSent` would refuse; for such a split `secondOpens` has no clause.
  `fill` puts the lists at the rounds of positions in order. It compares their number, not the
    rounds' names. `declPOf` counts the entries named "LOC", and `frameOpens` puts as many lists and
    one more in front of the lists of the last test's code switches. If a plan had a round of
    positions of another name among the links, and one code switch more under the last test's label,
    the number would fit and the order be wrong.
  A tree is known by the leaf class of its first oracle message. If a link's own message had the
    class of what rides at the start, its tree would be struck from its "LOC". At link 0, moment 0,
    it would be taken for the input, and no test here need fail; at every other place `fileOf` would
    refuse (a tree opened nowhere). The planner gives what rides at the start a class above every
    link's (OnBytes/Params/DeriveReq.lean).
  `fileOf` asks that each tree is opened somewhere in the file, not that it is opened as often as
    the program opens it. That the split's tree is opened twice is known only because
    `sharedOpens` says so.
  The stored table's number of draws (the fold's columns) is held against nothing here, nor against
    the positions that the entry draws.
  The plans are those that the program's readers read back from the parameter bytes. The shapes and
    the codes are the planner's own (`made.sized`). Nothing here compares the two.
  The hash. No declared round, written round or `WholeD` here holds a digest. A declared round holds
    an entry, shapes and numbers; a tree that is taken over is named (`TreeSource.taken`); the
    stand-ins in `writtenOf` are constants. `Made` does hold digests: its field `p` is the whole
    value of `planned`, with the digest of the three files (`cfg`; in each chain's parameter bytes;
    in each `given.cfg`) and three digests of the second hash function (`X.digests`). Of `p` the
    functions here read `chains.made.sized` and six plans (`given.plan`), and nothing else. Two
    hashes are called on the road, both as concrete functions. The format's hash: `planned` computes
    the digest of the three files (`configuration`) and writes it into the parameter bytes, from
    which the plans are read back; `madeOf` calls `planned`, and `sendsOf` calls it once more. The
    second hash function: `publicOf` (OnBytes/Model/VerifyPublic.lean), the first step of `planned`,
    hashes the public tables and refuses if a digest is not the one in the parameter file's lines
    (`tableHeld`, OnBytes/Model/Config.lean); it also forms `hPar` and the digests of the lists of
    calls. The second hash function stands there as a constant, not as an argument. So whether a
    function here returns a value can hang on an answer of the second hash function. That the values
    depend on neither hash is not proved. For the format's hash OnBytes/Tie/ChainsAtCfg.lean has the
    text of `planned` with the digest as an argument (`plannedAt`) and the law that sizes and plans
    are the same at every digest of 32 bytes (`plannedAt_at`, under its hypotheses); `plannedAt`
    calls `publicOf` as it stands. `sendsOf` has no form that starts from a value of the planner.
  The stand-ins. A stand-in is no root and no run value: `tagRoot n` has n + 1 bytes and `tagRun c`
    one, and the readers' test `Fmt.Round.ok` (Fmt/Rules8.lean) asks 32 of each. So no file can be
    read under a second chain's list as `writtenOf` returns it. `Three.Whole.of` reads a stand-in
    back as a chain and a number (`Three.named`); `tagRoot n` is the same for both earlier chains,
    and `tagRun` alone tells them apart. Whoever reads a file takes the declared rounds (`declKOf`,
    `declPOf`) and calls `Fmt.DeclaredRound.round` with the roots and run values with which the file's
    first two chains were read.
  A label of `sendsOf` that is changed into another label that `sendTag` knows is noticed only where
    a count, or one of the two tests on what is opened, then fails (three such cases: the guard
    file). A change of a stage's number, or of a moment's number behind group 0, is never noticed:
    the rule does not read these numbers.
  No request is read. The proof file's written lists, and the proof file's chains in
    `Params.declared`, come from dry runs at one made-up request each. That a dry run gives the same
    rounds at every request is not proved.
  The verifier program lies below this file by two roads. Johnson/G/Sends.lean imports, through
    Johnson/G/Calls.lean, OnBytes/Model/Verify.lean, and with it the blocks, the three stages and
    the checks of the three files. OnBytes/Maker/Files.lean, imported for `dataAt`, brings `dryKey`
    and `dryProof`; OnBytes/Three/Data.lean, imported for the stand-ins, `dry3`. Nothing here calls
    a block, a dry run or a check of a file.
  The entry file's chain is not made.
  `sendsOf` is by its own head a reading of the verifier's text, with no theorem.


-/
import Johnson.G.Sends
import Fmt.Parsed
import OnBytes.Three.Data
import OnBytes.Maker.Files

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G.OfPlan

open OnBytes OnBytes.Params OnBytes.Maker
open OnBytes.Three (tagRoot tagRun)

/-- The proximity tests of a key file's and of a proof file's chains. -/
inductive TestTag where
  | ranges
  | folded
  | omega
  | own
  | last
  deriving DecidableEq, Repr

/-- What a sending is. -/
inductive SendTag where
  /-- the oracle messages of one moment of group number l: a link's, or the last test's group's.
  The rule reads the moment at group 0 alone -/
  | link (l moment : Nat)
  /-- the code switch of stage number i of a test. The rule does not read i -/
  | stage (t : TestTag) (i : Nat)
  | indexMask
  | multiplicities
  | foldedRow
  | omega
  | w
  /-- the mask that a fold sends itself; `sendsOf` does not list it -/
  | ownMask
  deriving DecidableEq, Repr

/-- The test of a name, as `sendsOf` spells it. -/
def testTag : String → Option TestTag
  | "the ranges' test" => some .ranges
  | "the folded row's test" => some .folded
  | "Omega's test" => some .omega
  | "the own test" => some .own
  | "the last group's test" => some .last
  | _ => none

/-- What a sending is, by the label that `sendsOf` gives it. Nothing at any other label. -/
def sendTag (label : String) : Option SendTag :=
  match label with
  | "the index-mask message" => some .indexMask
  | "the multiplicities" => some .multiplicities
  | "the folded row" => some .foldedRow
  | "Omega" => some .omega
  | "W" => some .w
  | _ =>
    match label.splitOn ", the code switch of stage " with
    | [t, i] => do pure (.stage (← testTag t) (← i.toNat?))
    | _ =>
      match label.splitOn ", moment " with
      | [a, m] =>
        if a.startsWith "link " then do pure (.link (← (a.drop 5).toNat?) (← m.toNat?)) else none
      | _ => none

/-- A refusal's words: where, what, and what it means. -/
def refusal (at_ what : String) : String :=
  s!"{at_}: {what}. The rule of Johnson/G/RoundsOfPlan.lean does not fit these public files; " ++
    "the files need not be at fault."

/-- A tree that a chain sends. -/
structure Sent where
  /-- the number, from 0, of the round that sends it -/
  round : Nat
  /-- its depth -/
  a : Nat
  /-- the words of a column -/
  W : Nat
  /-- the leaf class of its first oracle message -/
  cls : Nat
  /-- what its sending is -/
  tag : SendTag

/-- The trees of one sending. at_: the file and the chain, for a refusal's words. off: how many of
the plan's entries are no rounds; they are taken to stand in front (if they do not, `treesSent`
finds a tree at a wrong round and refuses, unless that round's entry has as many roots). -/
def sentAt (at_ : String) (codes : Codes) (off : Nat) (x : Sending) :
    Except String (List Sent) := do
  let tag ← match sendTag x.label with
    | some t => pure t
    | none =>
      throw (refusal at_ s!"a sending has the label \"{x.label}\", which `sendTag` does not know")
  let L ← match layTrees codes x.sent.toArray with
    | some L => pure L
    | none => throw (refusal at_ s!"the oracle messages of \"{x.label}\" cannot be placed in trees")
  pure <| L.shapes.toList.zipIdx.map fun (t, i) =>
    let j := (List.range x.sent.length).find? fun j => L.tree.getD j 0 == i
    ⟨x.entry - 1 - off, t.logN, t.mainWidth + t.maskWidth,
      ((j.bind fun j => x.sent[j]?).map (·.leafClass)).getD 0, tag⟩

/-- All trees of a chain in the order of sending, each with its number. at_: the file and the chain,
for a refusal's words. c: the chain's codes and sendings. P: its plan. extra: the trees that go in a
round that is no "SEND seed". Refused unless each round gets as many trees as its entry has roots.
-/
def treesSent (at_ : String) (c : ChainSends) (P : Fmt.Plan) (extra : List Sent) :
    Except String (List (Sent × Nat)) := do
  let es := P.rounds
  let l ← c.sends.mapM (sentAt at_ c.codes (P.entries.length - es.length))
  let ts := (l.flatten ++ extra).mergeSort fun a b => a.round ≤ b.round
  let made := ts.foldl (fun (n : Array Nat) t => n.modify t.round (· + 1))
    (Array.replicate es.length 0)
  match es.zipIdx.find? fun e => made.getD e.2 0 != e.1.roots with
  | some e => throw <| refusal at_ <| s!"round {e.2} (\"{e.1.name}\"): the plan's entry has " ++
      s!"{e.1.roots} root(s), but {made.getD e.2 0} tree(s) were found for it"
  | none =>
    unless ts.all fun t => t.round < es.length do
      throw (refusal at_ "a tree was found for a round after the plan's last round")
    pure ts.zipIdx

/-- A tree as a declared round names it: its shape, and whose it is. -/
abbrev Told : Type := Fmt.Shape × Fmt.TreeSource

/-- One of the chain's own trees. first: the number of the chain's first tree. -/
def ownAt (first : Nat) (t : Sent × Nat) : Told := (⟨t.1.a, t.1.W, false, first + t.2⟩, .own t.2)

/-- A tree that is taken over from the chain number c. -/
def takenAt (c : Nat) (t : Sent × Nat) : Told := (⟨t.1.a, t.1.W, false, t.2⟩, .taken c t.2)

/-- For each tree of a code switch of the test t, in order: that tree alone. (A code switch of two
trees would give two lists, and `fill` would refuse by their number.) -/
def switchOpens (first : Nat) (t : TestTag) (ts : List (Sent × Nat)) : List (List Told) :=
  (ts.filter fun x => match x.1.tag with
    | .stage t' _ => t' == t
    | _ => false).map fun x => [ownAt first x]

/-- The declared rounds of a chain: the lists are put at the rounds that draw positions, in order;
every other round opens nothing. Refused unless the lists are as many as these rounds, and each
holds a tree or a stored table. -/
def fill (at_ : String) (es : List Fmt.Entry) (plan : List (List Told × List Fmt.Stored)) :
    Except String (List Fmt.DeclaredRound) := do
  let n := (es.filter fun e => Fmt.kindOf e.name == some .positions).length
  unless n == plan.length do
    throw <| refusal at_
      s!"{n} round(s) draw positions, but lists of trees were found for {plan.length}"
  if let some x := plan.zipIdx.find? fun x => x.1.1.isEmpty && x.1.2.isEmpty then
    throw (refusal at_ s!"the round of positions number {x.2}, from 0, would open nothing")
  pure (es.foldl (fun (s : Array Fmt.DeclaredRound × List (List Told × List Fmt.Stored)) e =>
    match Fmt.kindOf e.name == some .positions, s.2 with
    | true, x :: rest => (s.1.push ⟨e, x.2, x.1⟩, rest)
    | _, _ => (s.1.push ⟨e, [], []⟩, s.2)) (#[], plan)).1.toList

/-- Lists of trees, with no stored table. -/
def noStored (l : List (List Told)) : List (List Told × List Fmt.Stored) := l.map (·, [])

/-- What the rounds of positions of a proof's first chain open, in order. riders: the leaf classes
of what rides at the start. locs: the number of the chain's rounds "LOC". -/
def frameOpens (riders : List Nat) (ts : List (Sent × Nat)) (locs : Nat) : List (List Told) :=
  ((List.range (locs + 1)).map fun l =>
    (ts.filter fun t => !riders.contains t.1.cls && match t.1.tag with
      | .link l' _ => l' == l
      | _ => false).map (ownAt 0)) ++
  switchOpens 0 .last ts

/-- What the rounds of positions of a key's first chain open, in order. -/
def onceOpens (ts : List (Sent × Nat)) : List (List Told) :=
  (ts.filter fun t => t.1.tag == .multiplicities).map (ownAt 0) :: switchOpens 0 .ranges ts

/-- What the rounds of positions of a shared chain open, in order, with the stored table. -/
def sharedOpens (S : LinShape) (ts : List (Sent × Nat)) : List (List Told × List Fmt.Stored) :=
  ([], [⟨S.fold.index.tree, S.fold.index.saltBytes, 0, 0, S.fold.columns⟩]) ::
  noStored (
    (ts.filter fun t => t.1.tag == .foldedRow ||
      (t.1.tag == .omega && (!S.sharedSplitNeeded || t.1.cls == S.sharedSplitLeafClass))).map
        (ownAt 0) ::
    switchOpens 0 .folded ts ++
    (if S.sharedSplitNeeded then
      (ts.filter fun t => t.1.tag == .omega || t.1.tag == .ownMask).map (ownAt 0) ::
        switchOpens 0 .omega ts
     else []))

/-- What the rounds of positions of a second chain open, in order. input: which of the first chain's
trees holds the input. t0, t1: the trees of the first and of the shared chain. -/
def secondOpens (S : LinShape) (input : Sent → Bool) (t0 t1 ts : List (Sent × Nat)) :
    List (List Told) :=
  ((t0.filter fun t => input t.1).map (takenAt 0) ++
    (t0.filter fun t => t.1.tag == .w).map (takenAt 0) ++
    (t1.filter fun t => t.1.tag == .omega && t.1.cls == S.omegaLeafClass).map (takenAt 1)) ::
  switchOpens (t0.length + 1) .own ts

/-- The masks that folds of a shared chain send themselves: at each "FOLD epsilon" with a root, the
mask of the first stage of Omega's test. -/
def ownMasks (codes : Codes) (S : LinShape) (es : List Fmt.Entry) : List Sent :=
  let cls :=
    (S.testOmega.head?.map fun st => (foldMaskNotice (ioppFoldShape st {})).leafClass).getD 0
  match S.testOmega.head?.bind fun st =>
      layTrees codes #[foldMaskNotice (ioppFoldShape st {})] with
  | none => []
  | some L =>
    (es.zipIdx.filter fun e => e.1.name == "FOLD epsilon" && 0 < e.1.roots).flatMap
      fun e => L.shapes.toList.map fun t => ⟨e.2, t.logN, t.mainWidth + t.maskWidth, cls, .ownMask⟩

/-- Three chains' declared rounds: first, shared, second. -/
abbrev Decl3 : Type := List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound

/-- The trees that a file's rounds open, each as the chain that sent it and its number there. -/
def toldIn (D : Decl3) : List (Nat × Nat) :=
  [D.1, D.2.1, D.2.2].zipIdx.flatMap fun c => (c.1.flatMap (·.opens)).map fun o =>
    match o.2 with
    | .own n => (c.2, n)
    | .taken k p => (k, p)

/-- One file's three chains. file: its name, for a refusal's words. first: what the first chain's
rounds of positions open, from its trees and its plan's rounds. input: which of the first chain's
trees holds the input. Refused also if a tree that a chain sends is opened nowhere in the file. -/
def fileOf (file : String) (S : LinShape) (P0 P1 P2 : Fmt.Plan) (c0 c1 c2 : ChainSends)
    (first : List (Sent × Nat) → List Fmt.Entry → List (List Told)) (input : Sent → Bool) :
    Except String Decl3 := do
  let t0 ← treesSent s!"{file}, first chain" c0 P0 []
  let t1 ← treesSent s!"{file}, shared chain" c1 P1 (ownMasks c1.codes S P1.rounds)
  let t2 ← treesSent s!"{file}, second chain" c2 P2 []
  let D : Decl3 :=
    (← fill s!"{file}, first chain" P0.rounds (noStored (first t0 P0.rounds)),
      ← fill s!"{file}, shared chain" P1.rounds (sharedOpens S t1),
      ← fill s!"{file}, second chain" P2.rounds (noStored (secondOpens S input t0 t1 t2)))
  let told := toldIn D
  match ([t0, t1, t2].zipIdx.flatMap fun c => c.1.map fun t => (c.2, t.2)).find?
      fun x => !told.contains x with
  | some x => throw <| refusal file <| s!"tree {x.2}, from 0, of the " ++
      s!"{["first", "shared", "second"].getD x.1 ""} chain would be opened nowhere in the file"
  | none => pure D

/-- What the planner and `sendsOf` make of the three public files. -/
structure Made where
  p : OnBytes.Model.Verify.Planned
  key : ChainSends × ChainSends × ChainSends
  proof : ChainSends × ChainSends × ChainSends

/-- From policy.txt, layout.txt and KL.bin. -/
def madeOf (pol lay KL : ByteArray) : Except String Made := do
  let p ← OnBytes.Model.Verify.planned pol KL (some lay)
  match ← sendsOf pol lay KL with
  | [k0, k1, k2, _, p0, p1, p2] => pure ⟨p, (k0, k1, k2), (p0, p1, p2)⟩
  | _ => throw "the list of sendings has not seven chains (key 0 1 2, entry, proof 0 1 2)"

/-- The declared rounds of the key file's three chains. -/
def declKOf (m : Made) : Except String Decl3 :=
  fileOf "key file" m.p.chains.made.sized.key.once.shape m.p.chains.key.oneTime.given.plan
    m.p.chains.key.shared.given.plan m.p.chains.key.second.given.plan m.key.1 m.key.2.1 m.key.2.2
    (fun ts _ => onceOpens ts) (fun t => t.tag == .indexMask)

/-- The declared rounds of the proof file's three chains. -/
def declPOf (m : Made) : Except String Decl3 :=
  let riders := m.p.chains.made.sized.proof.request.atStart.map (·.leafClass)
  fileOf "proof file" m.p.chains.made.sized.proof.batch.shape m.p.chains.proof.first.given.plan
    m.p.chains.proof.shared.given.plan m.p.chains.proof.second.given.plan m.proof.1 m.proof.2.1
    m.proof.2.2
    (fun ts es => frameOpens riders ts (es.filter fun e => e.name == "LOC").length)
    (fun t => t.tag == .link 0 0 && riders.contains t.cls)

/-- **The declared rounds of the key file's and of the proof file's three chains**, from policy.txt,
layout.txt and KL.bin. -/
def declOf (pol lay KL : ByteArray) : Except String (Decl3 × Decl3) := do
  let m ← madeOf pol lay KL
  pure (← declKOf m, ← declPOf m)

/-- The number of roots that declared rounds send. -/
def rootsOf (l : List Fmt.DeclaredRound) : Nat := (l.map (·.entry.roots)).sum

/-- One file's declared rounds as written rounds. A tree that is taken over gets fixed tags.
file: the file's name, for a refusal's words. -/
def writtenOf (file : String) (D : Decl3) : Except String (Rounds × Rounds × Rounds) := do
  let earlier : List (List ByteArray × ByteArray) :=
    [((List.range (rootsOf D.1)).map tagRoot, tagRun 1),
     ((List.range (rootsOf D.2.1)).map tagRoot, tagRun 2)]
  let one (chain : String) (e : List (List ByteArray × ByteArray)) (l : List Fmt.DeclaredRound) :
      Except String Rounds :=
    l.mapM fun r => match r.round e with
      | some x => pure (x, r.stored)
      | none => throw <| refusal s!"{file}, {chain} chain" <| s!"the round \"{r.entry.name}\" " ++
          (if (Fmt.kindOf r.entry.name).isNone then "has a name that the format does not know"
           else "takes over a tree that the earlier chain does not send")
  pure (← one "first" [] D.1, ← one "shared" [] D.2.1, ← one "second" earlier D.2.2)

/-- The written rounds of the key file's and of the proof file's three chains, from what the planner
and `sendsOf` have made. -/
def roundsAt (m : Made) :
    Except String ((Rounds × Rounds × Rounds) × (Rounds × Rounds × Rounds)) := do
  pure (← writtenOf "key file" (← declKOf m), ← writtenOf "proof file" (← declPOf m))

/-- **The written rounds of the key file's and of the proof file's three chains**, from the three
public files. -/
def roundsOf (pol lay KL : ByteArray) :
    Except String ((Rounds × Rounds × Rounds) × (Rounds × Rounds × Rounds)) := do
  roundsAt (← madeOf pol lay KL)

/-- The depth of the stored table. Refused if the two files' shapes do not agree on it. -/
def depthOf (m : Made) : Except String Nat := do
  let a := m.p.chains.made.sized.key.once.shape.fold.index.code.logN
  unless a == m.p.chains.made.sized.proof.batch.shape.fold.index.code.logN do
    throw (refusal "both files" "their shapes give the stored table two depths")
  pure a

/-- The data of the key file's rounds, from what the planner and `sendsOf` have made. Where the
makers' tests (`okAt`) say no this does not refuse: it returns the data of three empty lists
(`dataAt`). -/
def dataKAt (m : Made) : Except String WholeD := do
  let a ← depthOf m
  pure (WholeD.of a (dataAt a (some (← writtenOf "key file" (← declKOf m)))))

/-- The data of the proof file's rounds, from what the planner and `sendsOf` have made. Where the
makers' tests (`okAt`) say no this does not refuse: it returns the data of three empty lists
(`dataAt`). -/
def dataPAt (m : Made) : Except String WholeD := do
  let a ← depthOf m
  pure (WholeD.of a (dataAt a (some (← writtenOf "proof file" (← declPOf m)))))

/-- **The data of the key file's rounds**, from the three public files. Where the makers' tests
(`okAt`) say no this does not refuse: it returns the data of three empty lists (`dataAt`). -/
def dataKOf (pol lay KL : ByteArray) : Except String WholeD := do dataKAt (← madeOf pol lay KL)

/-- **The data of the proof file's rounds**, from the three public files. Where the makers' tests
(`okAt`) say no this does not refuse: it returns the data of three empty lists (`dataAt`). -/
def dataPOf (pol lay KL : ByteArray) : Except String WholeD := do dataPAt (← madeOf pol lay KL)

end Johnson.G.OfPlan
