-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBook.lean: the book of coins of the key file's protocol, as a function of the sizes from
which the key file's rounds are computed (`Plan.KeySized`, OnBytes/Plan/KeyOneTime.lean). A book
(`ProverCoinCounts`) is a structure of the frame (Johnson/Desc/ProofFile/Honest/Frame.lean: the types in which
an honest prover is written). It is the public table that says how many coins (random field
elements) each part of the prover has of its own, which blocks of these coins other parts are given
too, and how each sub-protocol's rounds are cut into parts. Public data only: no prover, no coin's
value, no witness. Executable definitions, general in the sizes, and one small theorem.
E2E/KeyBookAtWritten.lean evaluates them at the written sizes of the full size. The frame's tests on
a book (`ProverCoinCounts.clauses`) are run in E2E/KeyBookTests.lean, except
the one on mask words, whose answer is supplied there as true.

Terms. A place (`Place`) is the label of a sub-protocol; an address (`Addr`) is a place and the
number of a part there. A count (`Due`) is a number of coins in each of the two fields. An entry
(`Ahead`) is a block of the coins of one part, its owner (the field `owner`), that one other part,
its spender (the field `spender`), is given too. An entry is marked as spent (`once` is true: meant
for coins that mask a value which is sent) or as carried (`once` is false: meant for coins on which
the part computes). A notice (`OracleNotice`) is an oracle message as it is announced: its shape and
its class of leaves. A sending (`Sending`) is the list of the oracle messages of one prover's
message, each with its counts of coins. A fill (`Fill`) says how a message's mask table is made of
coins. A face (`K3.Face`, Johnson/Desc/First/Look/K3LookupGeneral.lean) holds a lookup's public numbers.

  `keyBook K carried`: a definition: the key file's book, from a `KeyPub` K: for each of the three
    chains the owners with their counts; the entries `K.spent` and, where the flag carried is true
    (the default), `K.carried` after them; the cuts `K.cuts`
  `KeyPub`, `KeyPub.of z a`: a structure: what the book is made of (the lookups' faces, the number
    of variables of the matrix's columns, the four proximity tests' stages, six sendings, the counts
    of the four tests' parts after the first fold); and its value at the sizes z and at a answers to
    an OOD sample, or nothing at sizes that are not served (see the limits)
  `unroll_look`: the theorem: at every number i, face f and numbers a, b: the coins that the entries
    of lookup number i name, one by one (`unroll`), are what two counters that start at a and b give
    along the library's table `K3.fromKeys f` (`deal`)
  `Fill`, `MsgCoins`, `MsgCoins.due`, `msgCoins`, `fillOf`: the three forms of step (4) below; one
    message's counts, step by step; these by field; the counts of the message that a notice
    announces; the fill of a message that is not a code switch's own
  `Sending`, `sendingOf`, `startAt`, `Sending.due`, `tableAt`: a sending; a sending from its
    notices; the count of its first k messages; its whole count; the number of the first coin of a
    message's mask table
  `carriedAt`, `switchSendings`, `restDue`, `firstK`, `testCut`: of a proximity test: what a fold
    leaves for the next stage's mask table; the sendings of its code switches; the count of its part
    after the first fold; the rounds of its first fold; its cut into two parts
  `countsMaskRun`, `spend`, `carry`: an owner's name; an entry that is spent; an entry that is
    carried
  `seatOfLookup`, `takenOwn`, `takenKey`, `lookups`: a lookup's place and its two owners; how many coins
    a list of spans (`Span`, E2E/KeyBookFace.lean) takes of each owner; all lookups' entries
  `KeyPub.spent`, `KeyPub.carried`, `KeyPub.cuts`: the book's entries of the two sorts; its cuts
  `TestGroup`, `KeyPub.groups`, `TestGroup.entries`: a test's group (its member messages and its
    first fold's fresh table); the four groups; the carried entries of one group
  `Member`, `ownersOf`, `membersOf`: the table of places: for each sub-protocol its rounds, its cut,
    its parts' own coins, and whose coins its parts spend and carry
  `sentAt`: which oracle messages are sent at which place, sending by sending

By what. `unroll_look` is `unroll_book` (E2E/KeyBookFace.lean) at `seatOfLookup i`; its hypothesis, that
the two owners are two addresses, holds by `decide`. Definitions of other files: `Seat`, `Span`,
`spansOf`, `bookEntries`, `unroll`, `deal` (E2E/KeyBookFace.lean); the places (E2E/KeyPlaces.lean);
`mainDue`, `maskDue`, `RowsDue.tails` (E2E/RowCode.lean); `sentOfTest` (E2E/TreeRows.lean);
`runName`, `carriedName`, `indexMaskRun`, `foldMaskRun`, `splitMaskRun`
(Johnson/Desc/ProofFile/Honest/ForKinds.lean); and the library's functions on shapes:
`Wf.messageOf`, `Wf.lookupsOf` (OnBytes/Iop/Wf.lean), `Wf.matrixOf` (OnBytes/Key/Ranges.lean),
`linMessageW`, `linMessageOmega` (OnBytes/Iop/Lin.lean), `linMessageU`
(OnBytes/Params/DeriveLin.lean), `foldMaskNotice` (OnBytes/Iop/Fold.lean), `ioppFoldShape`
(OnBytes/Iop/Prox.lean), `faceOfLkp` (Johnson/Desc/First/Look/K3Key.lean).

Why the counts are written separately from every prover's definition. The docstring of `ProverCoinCounts` says
that a book is a check only if it is computed from the public files independently of the definitions
of the prover's sides: otherwise a part's count is compared with itself. So this file calls no count
from the definition of a part that sends. It counts by the rows' codes (`RowCode.mainDue`,
`maskDue`: E2E/RowCode.lean). One count is shared with a spender, in E2E/KeyBookFace.lean: the first
block of a masked sumcheck with the call k has `ownRun k` coins, and `ownRun k`
(Johnson/Desc/ProofFile/Honest/Sum.lean) is also the count in the type of the frame's part for that
sumcheck. It is a thin wrapper of the verifier's own `ownSlots` (Johnson/Desc/Part/MaskedSum4.lean).
Sum.lean is among the files that this file imports, through E2E/KeyBookFace.lean.

The order of an owner's coins. It is meant to be the order in which the parts that send, in the
frame's folder, count; how it is applied at the key file is this file's own choice. A part that has
a sending has one value of coins: so many of the base field, so many of the extension field, each
field's coins numbered from 0 through all oracle messages of the sending, in the order of sending.
The definitions fix the counts, and where a message's coins and its mask table begin (`startAt`,
`tableAt`); in this file the order of steps (1) to (3), and the order inside a step, are stated in
this comment only. In a message:
  (1) the main rows' encoding randomness, row 0 first, in the rows' own field
  (2) for a masking word (main rows, no sample): its main row's message
  (3) the pad of the OOD sample, if the message has no mask row: for each answer one element where
    the main rows are over the extension field, three where they are over the base field
  (4) the mask table
  (5) the mask rows' encoding randomness
Step (4) has three forms (`Fill`):
  `all`: every entry is a coin, entry c of row i of m rows at number c m + i: the index-mask
    message, the multiplicities' mask rows, W's mask row, the split's mask message, a masking word's
    mask row
  `fresh k`: a fold's fresh table: the 2 k + 1 coefficients of the fold's hiding polynomial; every
    other entry of the table is computed from these or is 0. k: the rounds of the fold that spends
    it
  `room c`: the oracle message that a code switch sends: all entries but the c that take what the
    fold leaves (two mask rows' messages, the main row's and two mask rows' encoding randomness:
    `switchParts`, OnBytes/Iop/Cs.lean)

Who owns, who spends.
  Owners: the five sendings (the index-mask message; the multiplicities; W; the folded row; Omega
    with the split's mask message); of each proximity test the part after its first fold (its
    switches' messages, the later folds' fresh tables, the masking word); and the first part of
    Omega's test, whose fold sends its own fresh table.
  Spenders: every masked sumcheck of the lookups (E2E/KeyBookFace.lean) spends coins of the
    multiplicities' mask rows, except that the end values of the last key level of each part of the
    keys take coins of the index-mask message. The sumcheck of the batching of the rows on the table
    spends coins of the index-mask message, after the lookups'. The first fold of the ranges' test,
    of the folded row's test and of the own test spends the fresh table that was sent along with the
    multiplicities, the folded row and W. The split spends the first entry of its mask message.
  Carried (given to a part that computes on them, not added to a value that is sent): each member
    message of a test's group, whole, to both parts of the test, in the order of sending; and, last,
    the first fold's fresh table, whole, to the second part only (`TestGroup`, `KeyPub.groups`).
    These entries rest on a reading: see the limits.

Limits.
- The encoding randomness of rows over the base field is counted in the base field: as the programs
  have it, and as the library's own condition on what may be sent asks (`Sendable`,
  Johnson/RunOne/KeyMember.lean). The library's code of a shape (`portCode`, Johnson/Pack/Port.lean)
  has it over the extension field by type.
- The book is a reading, not a theorem. Nothing here says that a prover samples just these coins, in
  this order; the counts rest on the code numbers in the sizes' shapes.
- The carried entries rest on a reading. Which messages are a group's members is a reading of which
  trees the test's first code switch opens. The definition of a part has to state what it carries
  independently of this list: otherwise name, count and order are compared with themselves.
- The count of `room` (`carriedAt`) is this file's reading of `switchParts` at a test's own switch:
  two mask rows, no kept row, no old pad. Two mask rows: the library's test on a switch asks for
  them (`switchTargetCheck`, OnBytes/Iop/Cs.lean). No kept row at the key file's four tests: the
  target of a test's own switch names no kept message (`switchTargetStage`), and every call that
  joins a message to one of the four groups in the description's text says "not kept"
  (`joinP … false`: Johnson/Desc/K13/Text.lean, K14/Text.lean, Third/K14BatchLinearConstraintsSecondPart.lean, Key/One.lean).
  That is by reading; no theorem says it. Subtraction is cut off at 0: a table too small for what it
  has to take counts 0.
- The book can be longer than what the programs' prover samples; by this reading it is not shorter.
  Every entry of a mask table that is not computed from something else is counted as a coin, also
  where no later message of a key file takes a mask from it. There are five such ranges: the
  index-mask message and the multiplicities' mask rows after what the lookups and the batching take;
  W's mask row, except the pad's entry; the split's mask message after its first entry; the free
  entries of every code switch's message (`room`). No line of the format's pages is known to fix
  these entries, and that the programs'
  prover samples them so is not checked.
- `fillOf` takes every message without a main row and without a sample for a fold's fresh table. An
  index-mask message or a split's message without a sample would so count 2 k + 1; the library's
  verifier rejects both (`memberRowsFit`, `splitMessageOk`: OnBytes/Iop/Lin.lean).
- `testCut` is for tests of at least two stages. At a test of one stage the frame's cut by the
  rounds' names (`cutOfNames`, Johnson/Desc/ProofFile/Honest/BookOf.lean) is the batching round
  only, then the base case; `testCut` gives another cut.
- The batching's entry is in the book at every size. The library's verifier takes no entry for it
  where the lookups have one part in all (`Wf.indexMaskEntries`, OnBytes/Iop/Wf.lean).
- Not served: sizes at which masks are not sent along with the sendings; at which the first folds'
  fresh tables are not sent ahead; without a split between the folded row's group and Omega's; with
  a split at W's own group (there W's sending has one more message, and there is a fifth test).
  `KeyPub.of` returns nothing there (`of_flags`, E2E/KeyBookSourced.lean).
- Two sorts of sizes that the library's verifier rejects (`ioppOk`, OnBytes/Iop/Prox.lean) are not
  excluded here. A ranges' test without a stage: the multiplicities' message is sent with no fresh
  table, the first fold's block begins at the end of the sending's coins, and the carried fresh
  table has no coin. No answer to a sample (a = 0): a code switch's message counts as a masking
  word, so the book is longer.
- That free entry number j of a mask table is coin number j of step (4) holds where the pad's
  entries are the table's last numbers: at one answer to a sample. It is not tested here for more.
- The owners' names are strings: the definition of a part has to call the same functions for them.
- No honest prover is defined.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyBookFace
import E2E.KeyPlaces
import E2E.RowCode
import E2E.TreeRows

set_option autoImplicit false

namespace AtPublicFiles.KeyBook
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K3 (Face faceOfLkp)
open AtPublicFiles.RowCode (RowsDue mainDue maskDue)
open ProofFile.Honest (Addr Ahead Due ProverCoinCounts runName carriedName indexMaskRun foldMaskRun splitMaskRun)

/-! ## 1 The counts -/

/-- How a message's mask table is made of coins. -/
inductive Fill where
  /-- every entry is a coin -/
  | all
  /-- a fold's fresh table: the 2 k + 1 coefficients of the hiding polynomial of a fold of k rounds
  -/
  | fresh (k : Nat)
  /-- the oracle message that a code switch sends: every entry but c of them is a coin -/
  | room (c : Nat)
  deriving DecidableEq, Repr

/-- One message's counts of coins, by the steps of the order in this file's head. -/
structure MsgCoins where
  /-- steps (1) to (3) where the main rows are over the base field (`mainDeg` is not 3); else 0 -/
  mainF : Nat
  /-- steps (1) to (3) where the main rows are over the extension field (`mainDeg` is 3); else 0 -/
  mainE : Nat
  /-- step (4) -/
  table : Nat
  /-- step (5) -/
  maskTails : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A message's count, by field: `mainF` in the base field, the three others in the extension field.
-/
def MsgCoins.due (m : MsgCoins) : Due := ⟨m.mainF, m.mainE + m.table + m.maskTails⟩

/-- The counts of the oracle message that the notice n announces, at a fill. Nothing where the
message has main rows, or mask rows, whose code's number is not in the list `codes`. -/
def msgCoins (codes : Codes) (n : OracleNotice) (fill : Fill) : Option MsgCoins :=
  match mainDue codes n, maskDue codes n with
  | some a, some b =>
    let s := n.shape
    let word := if s.mainRows != 0 && s.answers == 0 then (a.map fun d => d.rows * d.code.ell).sum
      else 0
    let pad := if s.maskRows == 0 then (if s.mainDeg == 3 then 1 else 3) * s.answers else 0
    let main := (a.map RowsDue.tails).sum + word + pad
    let whole := (b.map fun d => d.rows * d.code.ell).sum
    some
      { mainF := if s.mainDeg == 3 then 0 else main
        mainE := if s.mainDeg == 3 then main else 0
        table := match fill with
          | .all => whole
          | .fresh k => 2 * k + 1
          | .room c => whole - c
        maskTails := (b.map RowsDue.tails).sum }
  | _, _ => none

/-- A message without a main row and without a sample is taken for a fold's fresh table (`fresh k`);
every other message gets `all`. k: the rounds of the fold that spends the table. -/
def fillOf (k : Nat) (n : OracleNotice) : Fill :=
  if n.shape.mainRows == 0 && n.shape.answers == 0 then .fresh k else .all

/-- The oracle messages of one sending, each with its counts of coins. -/
abbrev Sending : Type := List MsgCoins

/-- The count of the first k messages: in each field, the number of the first coin of message number
k. -/
def startAt (l : Sending) (k : Nat) : Due := (l.take k).foldl (fun a m => a.plus m.due) ⟨0, 0⟩

/-- A sending's whole count. -/
def Sending.due (l : Sending) : Due := startAt l l.length

/-- The number, among the sending's coins of the extension field, of the first coin of the mask
table of message number k. -/
def tableAt (l : Sending) (k : Nat) : Nat := (startAt l k).e + (l.getD k default).mainE

/-- A sending outside a proximity test, from its notices. k: the rounds of the fold that spends the
fresh table that is sent along in it, if there is one. Nothing where `msgCoins` returns nothing. -/
def sendingOf (codes : Codes) (k : Nat) (l : List OracleNotice) : Option Sending :=
  l.mapM fun n => msgCoins codes n (fillOf k n)

/-! ## 2 A proximity test -/

/-- What the fold at a stage leaves for the mask table of the next stage's message: two mask rows'
messages, the main row's encoding randomness and two mask rows'. A code that the list lacks counts
as the code with all three numbers 0. -/
def carriedAt (codes : Codes) (s : IoppStage) : Nat :=
  let C := codes.base.getD s.code default
  let Z := codes.mask.getD s.maskCode default
  2 * Z.ell + C.r + 2 * Z.r

/-- The sendings of a test's code switches: the next stage's message (`room`), and what is sent
along with it: the next fold's fresh table or, at the last stage, the masking word. a: the answers
to a sample. The notices are `sentOfTest a true st` (E2E/TreeRows.lean), at which masks are sent
along. -/
def switchSendings (codes : Codes) (a : Nat) (st : List IoppStage) : Option (List Sending) :=
  (AtPublicFiles.TreeReads.sentOfTest a true st).zipIdx.mapM fun x =>
    x.1.zipIdx.mapM fun n =>
      msgCoins codes n.1
        (if n.2 == 0 then .room (carriedAt codes (st.getD x.2 default))
         else fillOf (st.getD (x.2 + 1) default).k n.1)

/-- The count of the part of a test that comes after its first fold: those of `switchSendings`,
added up. -/
def restDue (codes : Codes) (a : Nat) (st : List IoppStage) : Option Due :=
  (switchSendings codes a st).map fun l => l.foldl (fun d s => d.plus s.due) ⟨0, 0⟩

/-- A test's cut into two parts: the batching round with the first fold; all the rest. For tests of
at least two stages (see the limits in this file's head). -/
def testCut (st : List IoppStage) : List Nat :=
  let k := (st.headD default).k
  [2 + k, 1 + (st.dropLast.map fun s => s.k + 3).sum + 2 - (2 + k)]

/-! ## 3 Entries -/

/-- The name, as an owner, of the mask rows of the message with the multiplicities. -/
def countsMaskRun : String := "the multiplicities' mask rows"

/-- An entry that is spent: n coins of the extension field, from number a on, of the part at o, for
the part at dest. Its name is `runName owner dest use`. -/
def spend (owner : String) (use : String) (o : Addr) (a n : Nat) (dest : Addr) : Ahead :=
  ⟨runName owner dest use, o, ⟨0, a⟩, ⟨0, n⟩, dest, true⟩

/-- An entry that is carried: all coins of message number k of the sending l of the part at o, for
the part at dest. -/
def carry (o : Addr) (l : Sending) (k : Nat) (dest : Addr) : Ahead :=
  ⟨carriedName o k dest, o, startAt l k, (l.getD k default).due, dest, false⟩

/-- The `Seat` (E2E/KeyBookFace.lean) of lookup number i: its place, and the two owners whose coins
its parts spend: the part that sends the multiplicities and the part that sends the index-mask
message, each with its name as an owner. -/
def seatOfLookup (i : Nat) : Seat :=
  { place := lookPlace i, ownName := countsMaskRun, own := ⟨msgPlace, 0⟩
    keyName := indexMaskRun, key := ⟨idxPlace, 0⟩ }

/-- How many coins a list of spans takes of the first owner. -/
def takenOwn (ps : List Span) : Nat := ((ps.flatMap Span.homes).filter (!·)).length
/-- How many it takes of the second owner. -/
def takenKey (ps : List Span) : Nat := ((ps.flatMap Span.homes).filter (·)).length

/-- The lookups' entries, one lookup after the other, and the two owners' next unused coins. The
arguments after the faces: the first lookup's number; the two owners' first unused coins. -/
def lookups : List Face → Nat → Nat → Nat → List Ahead × Nat × Nat
  | [], _, a, b => ([], a, b)
  | f :: fs, i, a, b =>
    let r := lookups fs (i + 1) (a + takenOwn (spansOf f)) (b + takenKey (spansOf f))
    (bookEntries (seatOfLookup i) f a b ++ r.1, r.2)

/-- **The coins of a lookup's entries, one by one, are what two counters give along the library's
table.** It is `unroll_book` (E2E/KeyBookFace.lean) at `seatOfLookup i`, whose two owners are two
addresses. -/
theorem unroll_look (i : Nat) (f : Face) (a b : Nat) :
    unroll (seatOfLookup i) (bookEntries (seatOfLookup i) f a b) =
      deal (VerifiableInference.Desc.K3.fromKeys f) a b :=
  unroll_book (seatOfLookup i)
    (show (⟨msgPlace, 0⟩ : Addr) ≠ ⟨idxPlace, 0⟩ by decide) f a b

/-! ## 4 The book -/

/-- What the key file's book is made of. -/
structure KeyPub where
  /-- the lookups' faces -/
  faces : List Face
  /-- the number of the matrix's column variables, over which the batching's sumcheck runs -/
  kCol : Nat
  /-- this field and the next three: the stages of the four tests: on the ranges' group, on the
  folded row's, on Omega's and on the own group -/
  rng : List IoppStage
  folded : List IoppStage
  omega : List IoppStage
  own : List IoppStage
  /-- this field and the next four: the five sendings outside the tests: the index-mask message; the
  multiplicities; W; the folded row; Omega with the split's mask message -/
  sIdx : Sending
  sMsg : Sending
  sW : Sending
  sFolded : Sending
  sOmega : Sending
  /-- the fresh table that the first fold of Omega's test sends itself -/
  sOwnMask : Sending
  /-- this field and the next three: the counts of the four tests' parts after the first fold -/
  rRng : Due
  rFolded : Due
  rOmega : Due
  rOwn : Due

/-- The rounds of a test's first fold: the first stage's `k`; 0 at a test without a stage. -/
def firstK (st : List IoppStage) : Nat := (st.headD default).k

/-- A `KeyPub` from the sizes. a: the answers to a sample. Nothing where masks are not sent along
with the sendings; where the first folds' fresh tables are not sent ahead, with W and with the
folded row; where there is no split between the folded row's group and Omega's; where W's own group
has a split; where a message is not made; where Omega's test has no stage; or where a code is
missing. -/
def KeyPub.of (z : Plan.KeySized) (a : Nat) : Option KeyPub := do
  let S := z.once.shape
  let x := z.ranges.x
  guard (x.choice.masksRide && S.choice.masksRide && S.sharedSplitNeeded && S.masksAhead &&
    !S.ownSplitNeeded)
  let w ← linMessageW S
  let u ← linMessageU S
  let s0 ← S.testOmega.head?
  pure
    { faces := (Wf.lookupsOf x (Wf.matrixOf S)).map faceOfLkp
      kCol := (Wf.matrixOf S).kCol
      rng := x.stages, folded := S.testU, omega := S.testOmega, own := S.testOwn
      sIdx := ← sendingOf z.codes 0 [z.once.input]
      sMsg := ← sendingOf z.codes (firstK x.stages) (Wf.messageOf x).toList
      sW := ← sendingOf z.codes (firstK S.testOwn) w.toList
      sFolded := ← sendingOf z.codes (firstK S.testU) u.toList
      sOmega := ← sendingOf z.codes 0 (linMessageOmega S).toList
      sOwnMask := ← sendingOf z.codes s0.k [foldMaskNotice (ioppFoldShape s0 {})]
      rRng := ← restDue z.codes a x.stages
      rFolded := ← restDue z.codes a S.testU
      rOmega := ← restDue z.codes a S.testOmega
      rOwn := ← restDue z.codes a S.testOwn }

/-- The entries that are spent: the lookups'; then those of the first fold of the ranges' test, of
the batching's sumcheck, of the split, and of the first folds of the folded row's test and the own
test. -/
def KeyPub.spent (K : KeyPub) : List Ahead :=
  let L := lookups K.faces 0 (tableAt K.sMsg 0) (tableAt K.sIdx 0)
  L.1 ++
    [spend foldMaskRun "fold" ⟨msgPlace, 0⟩ (tableAt K.sMsg 1) (2 * firstK K.rng + 1) ⟨rngPlace, 0⟩,
      spend indexMaskRun "sum" ⟨idxPlace, 0⟩ L.2.2 (1 + 2 * K.kCol) ⟨battPlace, 1⟩,
      spend splitMaskRun "split" ⟨omegaPlace, 0⟩ (tableAt K.sOmega 1) 1 ⟨splitPlace, 0⟩,
      spend foldMaskRun "fold" ⟨foldedPlace, 0⟩ (tableAt K.sFolded 1) (2 * firstK K.folded + 1)
        ⟨foldedTestPlace, 0⟩,
      spend foldMaskRun "fold" ⟨wPlace, 0⟩ (tableAt K.sW 1) (2 * firstK K.own + 1)
        ⟨ownTestPlace, 0⟩]

/-- A proximity test's group, as the book has it: the test's place; the member messages, in the
order in which they are sent; and the first fold's fresh table. Each message is given by the part
that sends it, that part's sending and the message's number in it. -/
structure TestGroup where
  place : Place
  members : List (Addr × Sending × Nat)
  fresh : Addr × Sending × Nat

/-- The four tests' groups. -/
def KeyPub.groups (K : KeyPub) : List TestGroup :=
  [⟨rngPlace, [(⟨msgPlace, 0⟩, K.sMsg, 0)], (⟨msgPlace, 0⟩, K.sMsg, 1)⟩,
    ⟨foldedTestPlace, [(⟨foldedPlace, 0⟩, K.sFolded, 0), (⟨omegaPlace, 0⟩, K.sOmega, 1)],
      (⟨foldedPlace, 0⟩, K.sFolded, 1)⟩,
    ⟨omegaTestPlace, [(⟨omegaPlace, 0⟩, K.sOmega, 0), (⟨omegaPlace, 0⟩, K.sOmega, 1)],
      (⟨omegaTestPlace, 0⟩, K.sOwnMask, 0)⟩,
    ⟨ownTestPlace,
      [(⟨idxPlace, 0⟩, K.sIdx, 0), (⟨wPlace, 0⟩, K.sW, 0), (⟨omegaPlace, 0⟩, K.sOmega, 0)],
      (⟨wPlace, 0⟩, K.sW, 1)⟩]

/-- The entries of one group, in the order in which a part has to state them: to the first part the
members; to the second part the members and then, last, the fresh table. -/
def TestGroup.entries (G : TestGroup) : List Ahead :=
  G.members.map (fun m => carry m.1 m.2.1 m.2.2 ⟨G.place, 0⟩) ++
    G.members.map (fun m => carry m.1 m.2.1 m.2.2 ⟨G.place, 1⟩) ++
    [carry G.fresh.1 G.fresh.2.1 G.fresh.2.2 ⟨G.place, 1⟩]

/-- The entries that are carried; they rest on a reading (see the limits in this file's head). -/
def KeyPub.carried (K : KeyPub) : List Ahead := K.groups.flatMap TestGroup.entries

/-- The cut of every sub-protocol that has a round. -/
def KeyPub.cuts (K : KeyPub) : List (Place × List Nat) :=
  [(idxPlace, [2]), (msgPlace, [2])] ++
    K.faces.zipIdx.map (fun x => (lookPlace x.2, (spansOf x.1).map Span.rounds)) ++
    [(rngPlace, testCut K.rng), (battPlace, [1, 1 + K.kCol]), (wPlace, [2]), (sealPlace, [1]),
      (pointPlace, [1]), (foldedPlace, [2]), (locPlace, [1]), (omegaPlace, [2]), (zetaPlace, [1]),
      (splitPlace, [1]), (foldedTestPlace, testCut K.folded), (omegaTestPlace, testCut K.omega),
      (sharedSealPlace, [1]), (ownTestPlace, testCut K.own)]

/-- The key file's book of coins. carried: whether the carried entries, which rest on a reading, are
in it. -/
def keyBook (K : KeyPub) (carried : Bool := true) : ProverCoinCounts :=
  { first := [(⟨idxPlace, 0⟩, K.sIdx.due), (⟨msgPlace, 0⟩, K.sMsg.due), (⟨rngPlace, 1⟩, K.rRng),
      (⟨wPlace, 0⟩, K.sW.due)]
    shared := [(⟨foldedPlace, 0⟩, K.sFolded.due), (⟨omegaPlace, 0⟩, K.sOmega.due),
      (⟨foldedTestPlace, 1⟩, K.rFolded), (⟨omegaTestPlace, 0⟩, K.sOwnMask.due),
      (⟨omegaTestPlace, 1⟩, K.rOmega)]
    second := [(⟨ownTestPlace, 1⟩, K.rOwn)]
    ahead := K.spent ++ (if carried then K.carried else [])
    cuts := K.cuts }

/-! ## 5 The table of places -/

/-- A row of the table of places: what a book and the rows say of one sub-protocol. -/
structure Member where
  place : Place
  rounds : Nat
  /-- its parts' numbers of rounds; the empty list where the book has no cut for the place -/
  cut : List Nat
  /-- its parts' own coins: the part's number, the count -/
  takes : List (Nat × Due)
  /-- whose coins its parts spend: the owner; how many entries of the book; how many coins of the
  extension field -/
  spends : List (Addr × Nat × Nat)
  /-- whose coins its parts carry: the owner; how many entries -/
  carries : List (Addr × Nat)
  deriving Repr

/-- The owners of a list of entries, each once, in the order of their first entry. -/
def ownersOf (es : List Ahead) : List Addr := (es.map (·.owner)).eraseDups

/-- The table of places, from the rows (place, number of rounds) and a book. -/
def membersOf (rows : List (Place × Nat)) (B : ProverCoinCounts) : List Member :=
  rows.map fun r =>
    let here := B.ahead.filter fun e => e.spender.place == r.1
    let sp := here.filter (·.once)
    let ca := here.filter (!·.once)
    { place := r.1, rounds := r.2, cut := (B.cuts.lookup r.1).getD []
      takes := ((B.first ++ B.shared ++ B.second).filter fun x => x.1.place == r.1).map fun x =>
        (x.1.part, x.2)
      spends := (ownersOf sp).map fun o =>
        let l := sp.filter (·.owner == o)
        (o, l.length, (l.map (·.count.e)).sum)
      carries := (ownersOf ca).map fun o => (o, (ca.filter (·.owner == o)).length) }

/-! ## 6 What is sent -/

/-- The places that send oracle messages, in the order of play: each with its sendings, and each
sending with its oracle messages' notices. Nothing where a message is not made. It is put together
from the library's functions on shapes, as `sentKey` (E2E/TreeRows.lean) is; a test in
E2E/KeyBookAtWritten.lean compares the two at the written sizes. It does not have the guard of
`KeyPub.of`: at sizes that are not served it may still return a list. -/
def sentAt (z : Plan.KeySized) (a : Nat) : Option (List (Place × List (List OracleNotice))) := do
  let S := z.once.shape
  let w ← linMessageW S
  let u ← linMessageU S
  let s0 ← S.testOmega.head?
  pure
    [(idxPlace, [[z.once.input]]), (msgPlace, [(Wf.messageOf z.ranges.x).toList]),
      (rngPlace, AtPublicFiles.TreeReads.sentOfTest a true z.ranges.x.stages), (wPlace, [w.toList]),
      (foldedPlace, [u.toList]), (omegaPlace, [(linMessageOmega S).toList]),
      (foldedTestPlace, AtPublicFiles.TreeReads.sentOfTest a true S.testU),
      (omegaTestPlace, [foldMaskNotice (ioppFoldShape s0 {})] ::
        AtPublicFiles.TreeReads.sentOfTest a true S.testOmega),
      (ownTestPlace, AtPublicFiles.TreeReads.sentOfTest a true S.testOwn)]

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.unroll_look
#print axioms AtPublicFiles.KeyBook.Fill
#print axioms AtPublicFiles.KeyBook.MsgCoins
#print axioms AtPublicFiles.KeyBook.MsgCoins.due
#print axioms AtPublicFiles.KeyBook.msgCoins
#print axioms AtPublicFiles.KeyBook.fillOf
#print axioms AtPublicFiles.KeyBook.Sending
#print axioms AtPublicFiles.KeyBook.startAt
#print axioms AtPublicFiles.KeyBook.Sending.due
#print axioms AtPublicFiles.KeyBook.tableAt
#print axioms AtPublicFiles.KeyBook.sendingOf
#print axioms AtPublicFiles.KeyBook.carriedAt
#print axioms AtPublicFiles.KeyBook.switchSendings
#print axioms AtPublicFiles.KeyBook.restDue
#print axioms AtPublicFiles.KeyBook.testCut
#print axioms AtPublicFiles.KeyBook.countsMaskRun
#print axioms AtPublicFiles.KeyBook.spend
#print axioms AtPublicFiles.KeyBook.carry
#print axioms AtPublicFiles.KeyBook.seatOfLookup
#print axioms AtPublicFiles.KeyBook.takenOwn
#print axioms AtPublicFiles.KeyBook.takenKey
#print axioms AtPublicFiles.KeyBook.lookups
#print axioms AtPublicFiles.KeyBook.KeyPub
#print axioms AtPublicFiles.KeyBook.firstK
#print axioms AtPublicFiles.KeyBook.KeyPub.of
#print axioms AtPublicFiles.KeyBook.KeyPub.spent
#print axioms AtPublicFiles.KeyBook.TestGroup
#print axioms AtPublicFiles.KeyBook.KeyPub.groups
#print axioms AtPublicFiles.KeyBook.TestGroup.entries
#print axioms AtPublicFiles.KeyBook.KeyPub.carried
#print axioms AtPublicFiles.KeyBook.KeyPub.cuts
#print axioms AtPublicFiles.KeyBook.keyBook
#print axioms AtPublicFiles.KeyBook.Member
#print axioms AtPublicFiles.KeyBook.ownersOf
#print axioms AtPublicFiles.KeyBook.membersOf
#print axioms AtPublicFiles.KeyBook.sentAt
