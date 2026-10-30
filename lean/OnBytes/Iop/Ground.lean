-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/Ground.lean: what the blocks of the protocol share on the verifier's side.
 1. The statement: public data only.
 2. The book of trees: which oracle messages of one prover's message share a tree.
 3. The type Blk, in which a block is written once and read twice: by a dry run, for the strict
    reader's description, and by a run on a view, which makes the tests.
Each has a section below, which also explains the words: chain, session, plan, strict reader, view
and dry run at "The channel and the type of a block", oracle message and group at "The statement".

C++ counterparts: blocks/iop/relation.h (the statement, rows, groups, layouts), blocks/iop/context.h
(notices, lay_trees, the book of trees, receive_oracles, read_opened), blocks/iop/mask.h (the
ledger), blocks/code/code.h, cosets.h and short_position.h (the codes' arithmetic),
blocks/tree/positions.h (lists of positions), blocks/chain/rounds.h (the channel). Numbers such as
R7.13 name rules of the format page, docs/format/FORMAT.md.

Main definitions: Code, Codes, OracleShape, OracleNotice, Row, GroupRow, GroupLayout, Statement,
TreeBook, layTrees, Chan, Ctx, Failure, Blk, Blk.rounds, Blk.walk, Blk.runOn, Blk.decides,
Blk.receiveOracles, Blk.readOpened.

Rules that the types do not enforce (in full at the sections "The channel and the type of a block"
and "Calls on the statement"):
 - a block's course must not depend on a value that was received or drawn; whether a block makes all
   the tests that it should is a separate matter, which this construction does not settle;
 - only this file writes the channel or Ctx.failed; on Blk no block uses set, modify, <|> or catch;
 - only the sampling and Blk.sampledElsewhere mark a message as sampled; a batching takes all rows
   of a RunInput; a number from Blk.takeMask is used once. Nothing in this file tests these three.
Laws on Blk and on single calls: OnBytes/Iop/GroundLaws.lean, OnBytes/Iop/OpenLaws.lean.
What this file does not claim. Two small lemmas say how a missing value is lifted into a failure
(liftOption_none, liftOption_some). No other theorem is stated here.
-/
import OnBytes.Walk
import OnBytes.Field.Mle
import OnBytes.Iop.Tensor
import OnBytes.Chain.Draws

namespace OnBytes

/-! ## Codes and shapes -/

/-- The least a with n ≤ 2^a. -/
def ceilLog2 (n : Nat) : Nat := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- A code: words of length 2^logN, messages of ell entries, a random tail of r entries. -/
structure Code where
  logN : Nat
  ell : Nat
  r : Nat
  deriving DecidableEq, Repr, Inhabited

/-- True if n is a power of two. -/
def powerOfTwo (n : Nat) : Bool := n != 0 && 2 ^ ceilLog2 n == n

/-- ceilLog2 of the message length: the number of factors that the message's sum uses. It is the
length's logarithm where the length is a power of two, which every run tests of a statement's codes
(Blk.runNamed, Codes.lengthsOk). -/
def Code.logEll (c : Code) : Nat := ceilLog2 c.ell

/-- The codes of an instance: those of main rows and those of mask rows. -/
structure Codes where
  base : Array Code := #[]
  mask : Array Code := #[]
  deriving DecidableEq, Repr, Inhabited

/-- The condition on the codes of a statement: every message length is a power of two. -/
def Codes.lengthsOk (c : Codes) : Bool :=
  c.base.all (fun x => powerOfTwo x.ell) && c.mask.all fun x => powerOfTwo x.ell

/-- The number that means "no code", "no oracle message" or "no group". -/
def noId : Nat := 2 ^ 32 - 1

/-- The two tables of an oracle message: that of its main rows and that of its mask rows. (A part of
a tree is something else: an oracle message in that tree.) -/
inductive Part where
  | main
  | mask
  deriving DecidableEq, Repr, Inhabited

/-- What is public about one oracle message before it is sent. -/
structure OracleShape where
  /-- the code of its main rows, if it has any -/
  code : Nat := noId
  /-- its main rows; either number of rows may be 0, not both -/
  mainRows : Nat := 0
  /-- 1: main rows over the base field; 3: over the extension field -/
  mainDeg : Nat := 1
  /-- its mask rows, which are over the extension field -/
  maskRows : Nat := 0
  /-- the code of its mask rows -/
  maskCode : Nat := 0
  /-- the answers to its out-of-domain sample; 0: it is not sampled -/
  answers : Nat := 1
  deriving DecidableEq, Repr, Inhabited

/-- An oracle message as it is announced: its shape and its class of leaves. Oracle messages of one
prover's message with one class, and with main rows of one length, share leaves (layTrees). So an
opening must ask for all of them together (Blk.readOpened). -/
structure OracleNotice where
  shape : OracleShape
  leafClass : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- The conditions on the shape of an oracle message alone: it has rows, names a code for the rows
that it has, and its main rows are over one of the two fields. Whether the codes exist depends on
the list of codes and is not tested here. -/
def shapeFaultless (s : OracleShape) : Bool :=
  !(s.mainRows == 0 && s.maskRows == 0) && !(s.mainRows != 0 && s.code == noId) &&
    !(s.maskRows != 0 && s.maskCode == noId) &&
    !(s.mainRows != 0 && s.mainDeg != 1 && s.mainDeg != 3)

/-- The conditions of shapeFaultless, on the shape of an announced oracle message. -/
def noticeOk (n : OracleNotice) : Bool := shapeFaultless n.shape

/-- The rows of one of the two tables. -/
def OracleShape.rows (s : OracleShape) : Part → Nat
  | .main => s.mainRows
  | .mask => s.maskRows

/-! ## The codes' arithmetic

A code is a Reed-Solomon code on cosets. Position x has a point z. A row with the message m and the
tail t is the polynomial whose coefficients are the entries of t and, after them, those of m; its
symbol at x is the polynomial's value at z. -/

/-- An element of order 2^32 of the base field: 7^(5 (2^32 - 1)). -/
def rootOfOrder32 : F := 0xE2AF70635744FD26

/-- The greatest logarithm of a code's length: up to 2^28 cosets of 2^32 points. -/
def mostLogN : Nat := 60

/-- The dimension of a code: message and tail together. -/
def Code.dim (c : Code) : Nat := c.ell + c.r

/-- The number of factors z^(2^i) whose products give z^j for every coefficient j of a row. -/
def Code.logDim (c : Code) : Nat := ceilLog2 c.dim

/-- The number of factors that the tail's sum uses. -/
def Code.logR (c : Code) : Nat := ceilLog2 c.r

/-- True if the three numbers describe a code (code_ok in blocks/code/code.h). The dimension must
fit one coset: then no factor z^(2^i) of a position's point z, i below Code.logDim, depends on the
position's bits below i. No definition of this file calls Code.ok: those that follow take for
granted that it holds. It is tested of the codes of a proximity test's stages (ioppOk,
OnBytes/Iop/Prox.lean) and of a stored table's code (IndexShape.ok, OnBytes/Iop/Foldeq.lean), not of
every code in a statement's list. -/
def Code.ok (c : Code) : Bool :=
  decide (1 ≤ c.logN) && decide (c.logN ≤ mostLogN) && decide (1 ≤ c.ell) &&
    decide (c.ell ≤ 2 ^ c.logN) && decide (c.r ≤ 2 ^ c.logN) && decide (c.dim ≤ 2 ^ c.logN) &&
    decide (c.dim ≤ 2 ^ min c.logN 32)

/-- True if mask rows under zk can go with main rows under c: they are not longer. -/
def maskFits (c zk : Code) : Bool := decide (zk.logN ≤ c.logN)

/-- The position of a shorter word that goes with position x of a longer one. -/
def shortPosition (logShort x : Nat) : Nat := x % 2 ^ logShort

/-- The point of position x in a code of length 2^logN (gl64_point in blocks/code/cosets.h). With
s = min logN 32, H the subgroup of order 2^s and c = x / 2^s, the bits of x from s on pick the coset
7^(1 + c) H, and bit i below s multiplies by the root of unity of order 2^(i + 1). -/
def codePoint (logN x : Nat) : F :=
  let s := min logN 32
  ((List.range 32).foldl (fun (zr : F × F) j =>
    let i := 31 - j
    (if i < s && x.testBit i then mulF zr.1 zr.2 else zr.1, mulF zr.2 zr.2))
    (powF 7 (1 + x / 2 ^ s), rootOfOrder32)).1

/-- All that a symbol's formula needs at one position: symbol = messageScale * sum_j m[j] b_j +
tailScale * sum_j t[j] b_j, where b_j is the product of the factors f[i] over the bits i that are
set in j. -/
structure GeneratorRow where
  messageScale : F
  tailScale : F
  /-- logDim factors; the message's sum uses the first logEll, the tail's the first logR -/
  f : List F
  deriving Inhabited

/-- The generator row of a code at position x. -/
def generatorAt (c : Code) (x : Nat) : GeneratorRow :=
  let f := squaresOf c.logDim (codePoint c.logN x)
  { messageScale := productIndex f c.r, tailScale := 1, f := f }

/-- The coefficients of the ell message entries in the symbol at x. -/
def generatorMessage (c : Code) (x : Nat) : Array F :=
  let g := generatorAt c x
  (productTable (g.f.take c.logEll) c.ell).map (mulF · g.messageScale)

/-- The coefficients of the r tail entries in the symbol at x. -/
def generatorTail (c : Code) (x : Nat) : Array F :=
  let g := generatorAt c x
  (productTable (g.f.take c.logR) c.r).map (mulF · g.tailScale)

/-- Horner's rule on machine words: s z^n + a[n-1] z^(n-1) + .. + a[0], where s has the coordinates
c0, c1, c2 and z is in the base field. Entries that a lacks count as 0. -/
def hornerFrom (a : Array E) (z : F) : Nat → F → F → F → E
  | 0, c0, c1, c2 => E.mk3 c0 c1 c2
  | n + 1, c0, c1, c2 =>
    let x := a.getD n zeroE
    hornerFrom a z n (addF (mulF c0 z) x.c0) (addF (mulF c1 z) x.c1) (addF (mulF c2 z) x.c2)

/-- The symbol at position x of the row with this message and tail over the extension field. Entries
beyond ell or r are not read, and entries that are missing count as 0. -/
def symbolAt (c : Code) (x : Nat) (message tail : Array E) : E :=
  let z := codePoint c.logN x
  let m := hornerFrom message z c.ell 0 0 0
  hornerFrom tail z c.r m.c0 m.c1 m.c2

/-! ## Rows -/

/-- A structured coefficient vector on one table of one oracle message. The table is read as a
vector with 2^(ceilLog2 rows) rows; rows beyond the real ones are zero. So v has as many variables
as the table has index bits (Statement.tableBits): the row's bits are the low ones, the bits of the
place in the row come after them. -/
structure Term where
  oracle : Nat
  part : Part
  v : Tensor
  deriving Inhabited

/-- A coefficient on a single entry of a table. -/
structure Single where
  oracle : Nat
  part : Part
  index : Nat
  coeff : E
  deriving Inhabited

/-- Coefficients that are written out: a vector of its own over the extension field, or a stretch
of a vector over the base field that many values of the type Run share. (At one position all
generator rows have the same coefficients on the random tail, so they share one vector.) -/
inductive Coeffs where
  | own (c : Array E)
  | stretch (v : Array F) (start count : Nat)
  deriving Inhabited

/-- How many coefficients there are. -/
def Coeffs.size : Coeffs → Nat
  | .own c => c.size
  | .stretch _ _ count => count

/-- Coefficient number j; 0 beyond the end. -/
def Coeffs.get : Coeffs → Nat → E
  | .own c, j => c.getD j zeroE
  | .stretch v start count, j => if j < count then ofF (v.getD (start + j) 0) else zeroE

/-- True if a stretch is within its vector. -/
def Coeffs.ok : Coeffs → Bool
  | .own _ => true
  | .stretch v start count => decide (start + count ≤ v.size)

/-- Coefficients on the entries first, first + step, first + 2 step, and so on, of a table. With
step 1 the run follows the table read as a vector; with step 2^(row bits) it follows one row. -/
structure Run where
  oracle : Nat
  part : Part
  first : Nat
  step : Nat
  coeffs : Coeffs
  deriving Inhabited

/-- A whole coefficient vector on the main table of an oracle message. -/
structure MainForm where
  oracle : Nat
  c : Form
  deriving Inhabited

/-- The place of a row in the fixed order in which a batching takes rows. -/
inductive RowKind where
  | plain
  | sample
  | generator
  deriving DecidableEq, Repr, Inhabited

/-- A row: the sum of its terms, single entries, runs and forms, applied to the messages, equals
the target. The target is public. -/
structure Row where
  kind : RowKind := .plain
  terms : Array Term := #[]
  units : Array Single := #[]
  runs : Array Run := #[]
  forms : Array MainForm := #[]
  target : E := zeroE
  deriving Inhabited

/-- The coefficients of a group's row on the main table of one kept member (kept: see
GroupLayout). -/
structure KeptForm where
  oracle : Nat
  c : Form := {}
  deriving Inhabited

/-- One row on a whole group, as a proximity test takes it: c on the group's main table of 2^k
rows, a form on each kept member's own main table, d written out on the group's mask table of 2^h
rows. Whoever uses such a row has to take in all three pieces. -/
structure GroupRow where
  group : Nat := noId
  c : Form := {}
  /-- by increasing number of the oracle message -/
  kept : Array KeptForm := #[]
  d : Array E := #[]
  target : E := zeroE
  deriving Inhabited

/-- Where the rows of each member are among the rows of a group. A member with K rows takes an
aligned block of 2^(ceilLog2 K) rows. Blocks are placed from row 0 by decreasing size, ties in the
order of sending; the rows after them, up to 2^k (2^h for mask rows), are zero. h is the least
number that holds the mask rows' blocks, k the least that holds the main rows' blocks with h ≤ k and
1 ≤ k. A member may be kept: its main rows are read at the group's positions and tested with the
group, but they are not folded with the other rows, because a later part of the protocol reads them
again. A kept member's main rows have no place among the 2^k rows. -/
structure GroupLayout where
  k : Nat := 0
  h : Nat := 0
  logEll : Nat := 0
  logEllZk : Nat := 0
  /-- in the order of sending -/
  members : Array Nat := #[]
  kept : Array Bool := #[]
  /-- the first row of each member's block; nothing if it has no such rows -/
  mainFirst : Array (Option Nat) := #[]
  maskFirst : Array (Option Nat) := #[]
  deriving Inhabited

/-- The place of an oracle message among the members. -/
def GroupLayout.find (L : GroupLayout) (o : Nat) : Option Nat := L.members.idxOf? o

/-! ## The statement

The statement. It holds public data only: the codes, the oracle messages sent so far, the groups of
oracle messages that one proximity test reads together, and the open rows. A row says that a linear
form of the messages that some oracle messages encode has a public value.

Words. An oracle message is a set of main rows under one code and of mask rows under one mask code,
sent in one prover's message; it is sampled out of domain at most once and tested only as a whole. A
group is a set of whole oracle messages with one main code, which one proximity test reads at one
list of positions. -/

/-- The free mask entries of an oracle message (MaskLedger in blocks/iop/mask.h). Each is handed out
once, in the order of the entries; none after a proximity test on a group of the message has begun.
next: the number from which the next entry is searched for; left: how many are still free; rows,
logRows: the real mask rows and ceilLog2 of their number. An entry's row is the low logRows bits of
its number; a number that falls on a row beyond the real ones names no entry and is passed over.
Nothing here enforces how an entry is used: Blk.takeMask returns a plain number, so a number that
was taken in time can be used after the ledger is closed, or twice, and Row.addUnit and Row.addRun
can name a mask entry that was never handed out. -/
structure Ledger where
  next : Nat
  left : Nat
  rows : Nat
  logRows : Nat
  closed : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- An oracle message in the statement. -/
structure Oracle where
  shape : OracleShape
  sampled : Bool := false
  /-- one for each answer, from the moment the answers have been received -/
  sampleRows : Array Row := #[]
  /-- the entries that mask the answers; no other row reads them -/
  pad : List (Part × Nat) := []
  /-- the groups that it belongs to -/
  groups : List Nat := []
  ledger : Option Ledger := none
  /-- it is not sampled and has served as the mask of a fold or of a last step -/
  spentAsMask : Bool := false
  deriving Inhabited

/-- A group in the statement. inRun: its proximity test has begun (Blk.beginRun). In inRun, beginRun
and RunInput "run" means that test, not a value of the type Run and not a run of a block. -/
structure Group where
  code : Nat
  maskCode : Nat := 0
  /-- in the order of sending -/
  members : Array Nat := #[]
  kept : Array Bool := #[]
  /-- open rows, in the order of creation -/
  rows : Array Row := #[]
  inRun : Bool := false
  deriving Inhabited

/-- The statement that the blocks pass along. -/
structure Statement where
  codes : Codes := {}
  oracles : Array Oracle := #[]
  groups : Array Group := #[]
  deriving Inhabited

/-- What the beginning of a proximity test hands to a batching: the layout, and the rows in the
fixed order. -/
structure RunInput where
  layout : GroupLayout
  rows : Array Row
  deriving Inhabited

namespace Statement

/-- True if the oracle message has rows of this kind. -/
def has (S : Statement) (o : Nat) (part : Part) : Bool :=
  match S.oracles[o]? with
  | some x => decide (0 < x.shape.rows part)
  | none => false

/-- The number of bits that index a row of a table. -/
def rowBits (S : Statement) (o : Nat) (part : Part) : Nat :=
  match S.oracles[o]? with
  | some x => ceilLog2 (x.shape.rows part)
  | none => 0

/-- The number of bits that index a place in a row of a table; 0 for a table that is not there. -/
def placeBits (S : Statement) (o : Nat) (part : Part) : Nat :=
  match S.oracles[o]? with
  | some x =>
    if x.shape.rows part == 0 then 0
    else match part with
      | .main => (S.codes.base.getD x.shape.code default).logEll
      | .mask => (S.codes.mask.getD x.shape.maskCode default).logEll
  | none => 0

/-- The number of all index bits of a table: the row's bits, which are the low ones, then the bits
of the place in the row. -/
def tableBits (S : Statement) (o : Nat) (part : Part) : Nat :=
  S.rowBits o part + S.placeBits o part

end Statement

/-! ## Trees

The book of trees. It says which oracle messages of one prover's message share a tree, and where
each is in a leaf. -/

/-- The shape of a tree of oracle messages (R7.1). The leaf of position x holds the main rows'
symbols at x and, after them, the mask rows' symbols at x modulo the mask rows' length. -/
structure TreeShape where
  logN : Nat := 0
  logNzk : Nat := 0
  /-- for each oracle message in the tree (each part of the tree): the base-field elements of its
  main rows in a column -/
  mainSymbols : Array Nat := #[]
  /-- for each oracle message in the tree (each part of the tree): the base-field elements of its
  mask rows in a column -/
  maskSymbols : Array Nat := #[]
  deriving DecidableEq, Repr, Inhabited

/-- The base-field elements of all main rows in a column. -/
def TreeShape.mainWidth (t : TreeShape) : Nat := t.mainSymbols.foldl (· + ·) 0

/-- The base-field elements of all mask rows in a column. -/
def TreeShape.maskWidth (t : TreeShape) : Nat := t.maskSymbols.foldl (· + ·) 0

/-- How the oracle messages of one prover's message are placed in trees. -/
structure TreeLay where
  /-- for each oracle message: its tree within the prover's message -/
  tree : Array Nat := #[]
  /-- for each oracle message: its place among the parts of that tree -/
  part : Array Nat := #[]
  shapes : Array TreeShape := #[]
  deriving DecidableEq, Repr, Inhabited

/-- A tree in the book. -/
structure Tree where
  shape : TreeShape
  /-- the tree's number (R7.13), which the chain that sent it has given. It does not tell trees
  apart within a session: a chain that continues no other chain counts from 0, so two trees that one
  chain reads can have one number -/
  number : Nat := 0
  /-- where a reader takes the tree's root and start from (the start is the value from which its
  leaves are hashed). A tree of the present chain is named by its number in the chain's order of
  sending; a tree that is taken over from another chain comes with both values -/
  src : Fmt.Src := .own 0
  /-- the oracle messages in it -/
  parts : Array Nat := #[]
  /-- it holds an oracle message without a sample, so it is opened at one list only -/
  oneList : Bool := false
  /-- at how many lists it has been opened -/
  lists : Nat := 0
  deriving Inhabited

/-- The trees sent so far, and the place of each oracle message: its tree and its place among that
tree's parts. -/
structure TreeBook where
  trees : Array Tree := #[]
  place : Array (Nat × Nat) := #[]
  deriving Inhabited

/-- The symbols of one oracle message at one position: one element of the extension field for each
row, also for a row over the base field. -/
structure Column where
  main : Array E := #[]
  mask : Array E := #[]
  deriving Inhabited

/-- A list of positions that a round has drawn: the range, the draws as they came, and the list by
which trees are opened (each position once, increasing). -/
structure Positions where
  logN : Nat := 0
  draws : Array Nat := #[]
  all : Array Nat := #[]
  deriving DecidableEq, Repr, Inhabited

/-- Which entry of the list the position x is. -/
def Positions.indexOf (p : Positions) (x : Nat) : Option Nat := p.all.idxOf? x

/-- A list from draws below 2^logN. Not tested here: that they are below it, and that there is at
least one (from_draws in blocks/tree/positions.h tests both). The one caller, Blk.closePositions,
tests that the plan's entry has this range and at least one position. -/
def Positions.ofDraws (logN : Nat) (draws : List Nat) : Positions :=
  ⟨logN, draws.toArray, (listOfT draws).toArray⟩

/-! ## The channel and the type of a block

The type Blk, in which a block is written. A block receives the items of the prover's messages,
closes rounds, takes what the verifier drew, and reads opened columns.

Words. A chain is one hash chain that makes an interactive protocol non-interactive: a list of
rounds, each a prover's message and what the verifier draws after it. A session is all the chains
that one verdict reads. A chain's plan (Fmt.Plan) is public: it has an entry for each round, with
the round's name and its counts (bytes, roots, answers, draws, batched rows). The strict reader
reads a chain's bytes by a description of its rounds, computes the hashes, derives the draws and
checks each opening against its root. A view (Fmt.View) is what it hands to a decision: for each
round the items read, without the roots, and the draws; and the opened columns.

One text for a block, read twice. A chain needs a description for the strict reader (which items
each round holds, what it draws, which trees it opens) and a decision on what was read. Both follow
the same sequence of steps, which depends on public data alone. So a block is written once, in Blk,
and two functions read it.
 - Blk.rounds makes a dry run. Every value is zero, every test on a value is skipped, no row is
   built but SEND's sample rows (over zeros), and the run notes each round's kind, items and opened
   trees. The result follows from public parameters alone.
 - Blk.walk runs the block on the rounds of a view and makes all tests.
Neither reads bytes or calls the hash.

What a writer of a block must keep to. The course of a block (which items it receives, which rounds
it closes, which trees it opens) must not depend on a value that was received or drawn. If it did,
the dry run could give a description that differs from the course of the run on a view. Then the
strict reader refuses the file, or the run on the view fails, because it must use up every round,
item and opened column. Whether a block makes all the tests that it should is a separate matter,
which this construction does not settle: a branch on a value that skips a test would be a fault of
the block.

Three kinds of test. Blk.must is for public conditions and is tested in both readings. Blk.test
(fails at once) and Blk.check (noted; refuses at the run's end) are for conditions on values and do
nothing in the dry run. The dry run adds no row to a group and skips what is computed under
Blk.onView or a call like it, so a condition on such a row or value, public or not, is tested only
in the run on a view.

Why a run is refused. A failure carries the name that the failing call was given, or the word
"refused"; the channel's own failures are named "view-shape", "plan" and "codes". Every name is a
word of a fixed list and holds nothing that was read from a file. Blk.runOn returns the value or the
failure.

A rule that the type does not enforce. Blk is a state-and-failure function, so Lean would let a
block's text write the whole context (set, modify) or undo a failure (an alternative with <|>, a
catch). That could clear a failed named test, put a round or a column back, or undo a failed
condition with all that it had read. So only this file writes the channel or the field failed, and
no block's text uses set, modify, <|> or a catch on Blk. -/

/-- What a dry run notes of one round. -/
structure RoundNote where
  entry : Fmt.Entry
  kind : Fmt.Kind
  items : List Fmt.Item := []
  opens : List (Fmt.Shape × Fmt.Src) := []
  stored : List Fmt.Stored := []

/-- The channel of a block: the rounds of one chain, as far as they are still to come. -/
structure Chan where
  /-- true in the dry run -/
  dry : Bool
  /-- the number (R7.13) of the first tree that this chain sends: its place in the chain's own list
  of trees, after the trees that the chain takes over -/
  firstTree : Nat := 0
  /-- the number of answers to each out-of-domain sample (Fmt.Plan.samples) -/
  samples : Nat := 1
  /-- the plan's entries of the rounds that are not yet closed -/
  entries : List Fmt.Entry
  /-- the view's rounds that are not yet begun (none in the dry run) -/
  left : List Fmt.RoundView := []
  /-- the round whose message is being received, with the items not yet taken -/
  cur : Option Fmt.RoundView := none
  /-- the view's opened columns that are not yet read. A view has them in the file's order: round
  by round, opening by opening, position by position. A block reads them in that order. Each is the
  tree's key (Blk.takeColumns, Fmt.storedKey), the position, and the column's words. -/
  opened : List (Nat × Nat × List UInt64) := []
  /-- the roots received so far on this chain -/
  roots : Nat := 0
  /-- the entry of the round that was closed last -/
  last : Option Fmt.Entry := none
  /-- a block has compared the number of rows that the last round batches with the entry's -/
  askedRows : Bool := false
  /-- dry run: the items of the open message, the last one first -/
  items : List Fmt.Item := []
  /-- dry run: the rounds closed so far -/
  noted : Array RoundNote := #[]

/-- True if the round that was closed last owes no question: its entry counts no batched rows, or a
block has compared its own number of rows with the entry's (Blk.requireRows). Not asked here: the
C++ channel (blocks/chain/rounds.h) has six more questions of this kind: require_first_list,
require_group, require_codes, require_table, require_combinations, require_sharing. They compare a
block's numbers with what a C++ plan says beside a round. An entry as this program reads it
(Fmt.Entry) has only the number of rows. -/
def Chan.settled (ch : Chan) : Bool :=
  match ch.last with
  | some e => e.rows == 0 || ch.askedRows
  | none => true

/-- What a block's verifier holds: the channel, the statement, the book of trees, and intermediate
values. No test reads these values and the program keeps none: only Blk.notesOn, which tests call to
compare a block with another verifier, turns them on. -/
structure Ctx where
  ch : Chan
  st : Statement := {}
  book : TreeBook := {}
  notes : Array (String × E) := #[]
  /-- whether intermediate values are kept at all -/
  keepNotes : Bool := false
  /-- the name of the first named test on values that has failed (Blk.check) -/
  failed : Option String := none

/-- The name under which a condition fails that has no name of its own. -/
def unnamed : String := "refused"

/-- Why a block has failed. name: the name of the condition, a word of a fixed list that holds
nothing read from a file. place: the part of the protocol in which it failed, if a caller has said
it (Blk.inPlace). Only Blk.inPlace itself reads the place, to test whether it is empty. -/
structure Failure where
  name : String
  place : String := ""
  deriving DecidableEq, Repr, Inhabited

/-- The name under which a block fails if the view does not have the shape of the block's course:
an item, a round or an opened column is missing, is of another kind, or is left over. -/
def shapeName : String := "view-shape"

/-- The name under which a block fails if its course is not the given plan's: a round's name, its
number of elements drawn from the elements other than 0 or its number of batched rows differs, or
that number was never compared (Chan.settled); the plan has too few or too many entries; a call
needs a closed round and there is none; or a dry run ends with a message still open. -/
def planName : String := "plan"

/-- A missing value, met inside a block, is a failure without a name of its own. -/
instance : MonadLift Option (Except Failure) where
  monadLift x :=
    match x with
    | some a => .ok a
    | none => .error { name := unnamed }

/-- A missing value is lifted to the failure without a name. -/
theorem liftOption_none {α : Type} :
    (liftM (none : Option α) : Except Failure α) = .error { name := unnamed } := rfl

/-- A value that is there is lifted to itself. -/
theorem liftOption_some {α : Type} (a : α) : (liftM (some a) : Except Failure α) = .ok a := rfl

/-- A block: it changes what the verifier holds and returns a value, or fails under a name. -/
abbrev Blk : Type → Type := StateT Ctx (Except Failure)

namespace Blk

/-- What a block gives when it is run from a context: its value and the context that it leaves, or
nothing if it fails. Tests that run a block by hand, and laws on a run, are written with this
function and not with the block applied to a context: so they do not depend on how a failure is
written. A named test that has failed (Blk.check) is no failure here: it shows only in the field
failed of the context that is left. -/
def outcome {α : Type} (b : Blk α) (c : Ctx) : Option (α × Ctx) := (b c).toOption

/-- b, run from the context c, succeeds with the value x and leaves the context c'. -/
def Yields {α : Type} (b : Blk α) (c : Ctx) (x : α) (c' : Ctx) : Prop :=
  b.outcome c = some (x, c')

/-- Fails under the name. -/
def fail {α : Type} (name : String := unnamed) : Blk α := fun _ => .error { name := name }

/-- A public condition: fails unless b is true, in both readings. -/
def must (b : Bool) (name : String := unnamed) : Blk Unit := fun c =>
  if b then .ok ((), c) else .error { name := name }

/-- A condition on values: fails unless b is true; does nothing in the dry run. -/
def test (b : Bool) (name : String := unnamed) : Blk Unit := fun c =>
  if b || c.ch.dry then .ok ((), c) else .error { name := name }

/-- A condition on values under a name, for the protocol's own tests. If b is false, the name of the
first such test is kept and the block goes on; the run on a view is refused at its end. So a
refusal can say which test has failed, and the intermediate values are kept, unless the block fails
outright later: then both are lost. A block's course does not depend on values, so it goes on after
a failed test as after one that holds; only later conditions under Blk.checkOnView are then not
computed. Does nothing in the dry run. -/
def check (name : String) (b : Bool) : Blk Unit := fun c =>
  if b || c.ch.dry || c.failed.isSome then .ok ((), c)
  else .ok ((), { c with failed := some name })

/-- A value that only a run on a view needs. The dry run takes dflt and does not compute f. This is
how the dry run is spared the arithmetic: whatever is heavy and has no part in a block's course
(rows, batched rows, folded vectors) is computed under this call or under Blk.getOnView,
Blk.testOnView, Blk.checkOnView or Blk.addRowsOnView. -/
def onView {α : Type} (dflt : α) (f : Unit → α) : Blk α := fun c =>
  .ok (if c.ch.dry then dflt else f (), c)

/-- Blk.onView for a value that may be missing: the dry run takes dflt; on a view the block fails if
f gives nothing. -/
def getOnView {α : Type} (dflt : α) (f : Unit → Option α) (name : String := unnamed) : Blk α :=
  fun c =>
    if c.ch.dry then .ok (dflt, c)
    else
      match f () with
      | some a => .ok (a, c)
      | none => .error { name := name }

/-- A condition, public or on values, on what only a run on a view computes. Fails at once if it is
false. The dry run does not compute it. -/
def testOnView (f : Unit → Bool) (name : String := unnamed) : Blk Unit := fun c =>
  if c.ch.dry || f () then .ok ((), c) else .error { name := name }

/-- Blk.check for a condition that the dry run does not compute. -/
def checkOnView (name : String) (f : Unit → Bool) : Blk Unit := fun c =>
  if c.ch.dry || c.failed.isSome || f () then .ok ((), c)
  else .ok ((), { c with failed := some name })

/-- The value of x; fails if there is none. For a value whose presence depends on public data
alone. -/
def get {α : Type} (x : Option α) (name : String := unnamed) : Blk α := fun c =>
  match x with
  | some a => .ok (a, c)
  | none => .error { name := name }

/-- True in the dry run. -/
def isDry : Blk Bool := fun c => .ok (c.ch.dry, c)

/-- The answers to each out-of-domain sample, as the chain's plan has them. -/
def samples : Blk Nat := fun c => .ok (c.ch.samples, c)

/-- The number (R7.13) of the first tree that this chain sends: it comes after the trees that the
chain takes over. -/
def firstTree : Blk Nat := fun c => .ok (c.ch.firstTree, c)

/-- The plan's entry of the round that was closed last. Fails if no round has been closed. -/
def lastEntry : Blk Fmt.Entry := fun c =>
  match c.ch.last with
  | some e => .ok (e, c)
  | none => .error { name := planName }

/-- Keeps an intermediate value under a name. No test reads it. -/
def note (what : String) (value : E) : Blk Unit := fun c =>
  .ok ((), if c.keepNotes then { c with notes := c.notes.push (what, value) } else c)

/-- Blk.note for a value that is computed only if intermediate values are kept. -/
def noteBy (what : String) (value : Unit → E) : Blk Unit := fun c =>
  .ok ((), if c.keepNotes then { c with notes := c.notes.push (what, value ()) } else c)

/-- The statement. -/
def statement : Blk Statement := fun c => .ok (c.st, c)

/-- Replaces the statement by S. -/
def setStatement (S : Statement) : Blk Unit := fun c => .ok ((), { c with st := S })

/-- The next item of the open message. In the dry run the item is noted and dflt is returned. On a
view the item is taken from the round; roots are not among a view's items. On a view, i is not
compared with the item's kind: the caller must match on what it gets, as recvE and recvAnswer do. -/
def item (i : Fmt.Item) (dflt : Fmt.ItemValue) : Blk Fmt.ItemValue := fun c =>
  if c.ch.dry then .ok (dflt, { c with ch := { c.ch with items := i :: c.ch.items } })
  else
    let loaded : Option (Fmt.RoundView × List Fmt.RoundView) :=
      match c.ch.cur with
      | some r => some (r, c.ch.left)
      | none =>
        match c.ch.left with
        | [] => none
        | r :: t => some (r, t)
    match loaded with
    | none => .error { name := shapeName }
    | some (r, t) =>
      match r.vals with
      | [] => .error { name := shapeName }
      | g :: gs =>
        .ok (g, { c with ch := { c.ch with cur := some { r with vals := gs }, left := t } })

/-- Receives an element of the extension field. -/
def recvE : Blk E := do
  match ← item .e (.e zeroE.triple) with
  | .e x => pure (E.ofTriple x)
  | _ => fail shapeName

/-- Receives an answer to an out-of-domain sample. -/
def recvAnswer : Blk E := do
  match ← item .answer (.answer zeroE.triple) with
  | .answer x => pure (E.ofTriple x)
  | _ => fail shapeName

/-- Receives count elements of the extension field and appends them to acc. The depth of the
recursion does not grow with the count. -/
def recvEsInto : Nat → Array E → Blk (Array E)
  | 0, acc => pure acc
  | n + 1, acc => do
    let x ← recvE
    recvEsInto n (acc.push x)

/-- Receives count elements of the extension field. -/
def recvEs (count : Nat) : Blk (List E) := do
  pure (← recvEsInto count #[]).toList

/-- Receives a root. Returns its number on this chain, in the order of sending. A view does not
hold roots: the strict reader checks every opening against them. -/
def recvRoot : Blk Nat := fun c =>
  let ch := if c.ch.dry then { c.ch with items := Fmt.Item.root :: c.ch.items } else c.ch
  .ok (c.ch.roots, { c with ch := { ch with roots := c.ch.roots + 1 } })

/-- What a dry run takes as drawn: zeros, as many of each kind as the plan's entry says. -/
def dryDrawn (e : Fmt.Entry) (k : Fmt.Kind) : Fmt.Drawn where
  elems := List.replicate e.drawE zeroE.triple
  poss := List.replicate e.poss 0
  trits := List.replicate e.trits 0
  digest := if k == .sealed then some (ByteArray.mk (Array.replicate 32 0)) else none

/-- Closes the open message's round under its name and kind, and returns what the verifier drew.
The name must be that of the plan's next entry. nz: how many of the round's elements the block
takes as drawn from the non-zero elements; it must be the entry's number. If the entry of the round
closed before counts batched rows, a block must have compared its own count with it
(Chan.settled). On a view every item of the round must have been taken, and
the numbers of draws must be the entry's. The kind is noted in the dry run, for the description; the
run on a view does not read it. -/
def close (name : String) (kind : Fmt.Kind) (nz : Nat := 0) : Blk Fmt.Drawn := fun c =>
  match c.ch.entries with
  | [] => .error { name := planName }
  | e :: es =>
    if e.name != name || e.drawNZ != nz || !c.ch.settled then .error { name := planName }
    else if c.ch.dry then
      .ok (dryDrawn e kind, { c with ch := { c.ch with
        entries := es, last := some e, askedRows := false, items := [],
        noted := c.ch.noted.push { entry := e, kind := kind, items := c.ch.items.reverse } } })
    else
      let loaded : Option (Fmt.RoundView × List Fmt.RoundView) :=
        match c.ch.cur with
        | some r => some (r, c.ch.left)
        | none =>
          match c.ch.left with
          | [] => none
          | r :: t => some (r, t)
      match loaded with
      | none => .error { name := shapeName }
      | some (r, t) =>
        if r.vals.isEmpty && r.drawn.elems.length == e.drawE && r.drawn.poss.length == e.poss &&
            r.drawn.trits.length == e.trits then
          .ok (r.drawn, { c with ch := { c.ch with
            entries := es, last := some e, askedRows := false, cur := none, left := t } })
        else .error { name := shapeName }

/-- Tests that the round that was closed last batches this number of rows: the number that the
plan's entry counts (require_rows in blocks/chain/rounds.h: the number that the round's planned
error counts). The dry run does not build the rows that are batched, so it only notes that the
question was asked. -/
def requireRows (rows : Nat) : Blk Unit := fun c =>
  match c.ch.last with
  | some e =>
    if c.ch.dry || e.rows == rows then
      .ok ((), { c with ch := { c.ch with askedRows := true } })
    else .error { name := planName }
  | none => .error { name := planName }

/-- Closes a round in which the verifier says nothing. -/
def closeEmpty (name : String) : Blk Unit := do
  let _ ← close name .nothing

/-- Closes a round of elements and returns them. nz: how many of them are drawn from the non-zero
elements (all or none, which the strict reader requires of the entry). -/
def closeElems (name : String) (nz : Nat := 0) : Blk (List E) := do
  pure ((← close name .elems nz).elems.map E.ofTriple)

/-- Closes a round in which one element is drawn, and returns it. -/
def closeOne (name : String) (kind : Fmt.Kind := .elems) (nz : Nat := 0) : Blk E := do
  match (← close name kind nz).elems with
  | [x] => pure (E.ofTriple x)
  | _ => fail shapeName

/-- Closes a round of positions below 2^logN. The plan's entry must have this range and at least one
position. Returns the positions and the elements that the round draws after them (none or one, which
the strict reader requires of the entry). -/
def closePositions (name : String) (logN : Nat) : Blk (Positions × List E) := do
  let d ← close name .positions
  let e ← lastEntry
  must (e.logN == logN && decide (0 < e.poss))
  pure (Positions.ofDraws logN d.poss, d.elems.map E.ofTriple)

/-- The present statement and book: what a later chain of the same session starts from. -/
def handOver : Blk (Statement × TreeBook) := fun c => .ok ((c.st, c.book), c)

end Blk

/-- What a chain's block starts from: the plan's entries of the chain's rounds, the plan's number of
answers to a sample, the number of the first tree that the chain sends (it is not in the plan; it is
the field firstTree of the chain's description, Fmt.Spec), and the statement and the book of trees.
For a first chain the statement holds only the codes and the book is empty. -/
structure Start where
  entries : List Fmt.Entry
  /-- the answers to each out-of-domain sample -/
  samples : Nat := 1
  /-- the number (R7.13) of the first tree that this chain sends: its place in the chain's own list
  of trees, after the trees that the chain takes over -/
  firstTree : Nat := 0
  st : Statement
  book : TreeBook := {}

namespace Blk

/-- The name under which a run fails if a message length of the statement's codes is not a power of
two. -/
def codesName : String := "codes"

/-- Runs a block from a start: in the dry run, or on a view's rounds and opened columns. Fails if a
message length of the statement's codes is not a power of two, or if the block fails. A value here
is no verdict: Blk.walk and Blk.runOn look at the named tests that failed and at what is left
over. -/
def runNamed {α : Type} (b : Blk α) (s : Start) (dry : Bool) (rounds : List Fmt.RoundView)
    (opened : List (Nat × Nat × List UInt64)) (keepNotes : Bool := false) :
    Except Failure (α × Ctx) :=
  if s.st.codes.lengthsOk then
    b { ch := { dry := dry, entries := s.entries, samples := s.samples, firstTree := s.firstTree,
                left := rounds, opened := opened },
        st := s.st, book := s.book, keepNotes := keepNotes }
  else .error { name := codesName }

/-- The same without the name of a failure. For tests and laws. -/
def runFrom {α : Type} (b : Blk α) (s : Start) (dry : Bool) (rounds : List Fmt.RoundView)
    (opened : List (Nat × Nat × List UInt64)) (keepNotes : Bool := false) : Option (α × Ctx) :=
  (b.runNamed s dry rounds opened keepNotes).toOption

/-- The dry run. Returns the rounds of the chain's description, each with the stored trees that it
opens, and the block's value. It fails, under a name, if a public condition fails, if an entry of
the plan is left over, if a message is left open, or if the last round's number of batched rows was
not asked (Chan.settled). The program goes by Blk.dryRun, which drops the name. -/
def dryRunNamed {α : Type} (b : Blk α) (s : Start) :
    Except Failure (List (Fmt.Round × List Fmt.Stored) × α) :=
  match b.runNamed s true [] [] with
  | .error e => .error e
  | .ok (a, c) =>
    if c.ch.entries.isEmpty && c.ch.items.isEmpty && c.ch.settled then
      .ok (c.ch.noted.toList.map fun n => (⟨n.entry, n.kind, n.items, n.opens⟩, n.stored), a)
    else .error { name := planName }

/-- The dry run, without the name of a failure. -/
def dryRun {α : Type} (b : Blk α) (s : Start) :
    Option (List (Fmt.Round × List Fmt.Stored) × α) :=
  (b.dryRunNamed s).toOption

/-- The rounds of the chain's description, each with the stored trees that it opens. -/
def rounds {α : Type} (b : Blk α) (s : Start) : Option (List (Fmt.Round × List Fmt.Stored)) :=
  (b.dryRun s).map (·.1)

/-- The run on a view's rounds. opened: the view's opened columns. The walk fails if the block
fails, if a named test has failed, if the block leaves a message's round unclosed or an entry of the
plan or an opened column unused, or if the last round's number of batched rows was not asked
(Chan.settled). Rounds that the block has not begun are returned, not refused: Blk.decides and
Blk.runOn refuse them. -/
def walk {α : Type} (b : Blk α) (s : Start) (opened : List (Nat × Nat × List UInt64)) :
    Walk α := fun l =>
  match b.runNamed s false l opened with
  | .error _ => none
  | .ok (a, c) =>
    if c.ch.cur.isNone && c.ch.entries.isEmpty && c.ch.opened.isEmpty && c.ch.settled &&
        c.failed.isNone then
      some (a, c.ch.left)
    else none

/-- The decision that a block makes on a view: the walk (Blk.walk) succeeds and uses up all
rounds. -/
def decides (b : Blk Unit) (s : Start) (v : Fmt.View) : Bool :=
  Walk.decides (b.walk s v.opened) v

/-- The run on a whole view, once, for the verdict and for its reason: the block's value, or why the
run is refused. It gives a value exactly where the walk succeeds and leaves no round
(OnBytes/Iop/GroundLaws.lean, runOn_ok_iff). The reason: if the block failed outright, that
failure, also where a named test had failed before (a failure drops the context, and the test's name
with it); else the first named test that failed; else what was left over (planName, then
shapeName). -/
def runOn {α : Type} (b : Blk α) (s : Start) (v : Fmt.View) : Except Failure α :=
  match b.runNamed s false v.rounds v.opened with
  | .error e => .error e
  | .ok (a, c) =>
    match c.failed with
    | some name => .error { name := name }
    | none =>
      if !(c.ch.entries.isEmpty && c.ch.settled) then .error { name := planName }
      else if c.ch.cur.isNone && c.ch.opened.isEmpty && c.ch.left.isEmpty then .ok a
      else .error { name := shapeName }

/-- The name under which a run on a view is refused; nothing if it is not refused. For tests. -/
def failureOn {α : Type} (b : Blk α) (s : Start) (v : Fmt.View) : Option String :=
  match b.runOn s v with
  | .error e => some e.name
  | .ok _ => none

/-- The intermediate values that a run on a view keeps, for comparison with another verifier. None
if the block fails outright. -/
def notesOn {α : Type} (b : Blk α) (s : Start) (v : Fmt.View) : Array (String × E) :=
  match b.runNamed s false v.rounds v.opened true with
  | .error _ => #[]
  | .ok (_, c) => c.notes

/-- Gives a block a name: a failure inside it that has no name of its own gets this one. -/
def named {α : Type} (name : String) (b : Blk α) : Blk α := fun c =>
  match b c with
  | .error e => .error (if e.name == unnamed then { e with name := name } else e)
  | .ok x => .ok x

/-- Says in which part of the protocol a block runs: a failure inside it that has no place yet gets
this one. -/
def inPlace {α : Type} (place : String) (b : Blk α) : Blk α := fun c =>
  match b c with
  | .error e => .error (if e.place.isEmpty then { e with place := place } else e)
  | .ok x => .ok x

end Blk

/-! ## Arithmetic on rows -/

/-- True if both runs are on the same entries of the same table. -/
def Run.liesAs (a b : Run) : Bool :=
  a.oracle == b.oracle && a.part == b.part && a.first == b.first && a.step == b.step &&
    a.coeffs.size == b.coeffs.size

/-- x times the run, with coefficients of its own. -/
def Run.scaled (r : Run) (x : E) : Run :=
  { r with coeffs := .own (
      match r.coeffs with
      | .own c => c.map (mulE x)
      | .stretch v start count =>
        Array.ofFn (n := count) fun j => scaleE (v.getD (start + j.val) 0) x) }

/-- The run plus x times another run on the same entries. -/
def Run.addScaled (r other : Run) (x : E) : Run :=
  { r with coeffs := .own (
      match other.coeffs with
      | .own c =>
        Array.ofFn (n := r.coeffs.size) fun j => maddE (r.coeffs.get j.val) x (c.getD j.val zeroE)
      | .stretch v start count =>
        Array.ofFn (n := r.coeffs.size) fun j =>
          if j.val < count then maddS (r.coeffs.get j.val) (v.getD (start + j.val) 0) x
          else r.coeffs.get j.val) }

namespace Row

/-- Adds a structured coefficient vector on a table. -/
def add (r : Row) (o : Nat) (part : Part) (v : Tensor) : Row :=
  { r with terms := r.terms.push ⟨o, part, v⟩ }

/-- Adds a whole coefficient vector on a main table. -/
def addForm (r : Row) (o : Nat) (c : Form) : Row := { r with forms := r.forms.push ⟨o, c⟩ }

/-- Adds a run of coefficients. -/
def addRun (r : Row) (o : Nat) (part : Part) (first step : Nat) (c : Coeffs) : Row :=
  { r with runs := r.runs.push ⟨o, part, first, step, c⟩ }

/-- Adds a coefficient on a single entry. -/
def addUnit (r : Row) (o : Nat) (part : Part) (index : Nat) (coeff : E) : Row :=
  { r with units := r.units.push ⟨o, part, index, coeff⟩ }

/-- The whole coefficient of the row on one entry. -/
def coefficient (r : Row) (o : Nat) (part : Part) (index : Nat) : E :=
  let s1 := r.terms.foldl (fun s t =>
    if t.oracle == o && t.part == part then addE s (t.v.entry index) else s) zeroE
  let s2 := r.units.foldl (fun s u =>
    if u.oracle == o && u.part == part && u.index == index then addE s u.coeff else s) s1
  let s3 := r.runs.foldl (fun s w =>
    if w.oracle == o && w.part == part && w.first ≤ index && 0 < w.step &&
        (index - w.first) % w.step == 0 && (index - w.first) / w.step < w.coeffs.size then
      addE s (w.coeffs.get ((index - w.first) / w.step)) else s) s2
  r.forms.foldl (fun s f =>
    if f.oracle == o && part == .main then addE s (f.c.entry index) else s) s3

/-- The row plus x times the runs of another row, and nothing else of it. A run on the same entries
as a run of this row is added into that run: a batching of many rows of one geometry, such as a
code's generator rows, then leaves one run and not one for each row. -/
def addRunsScaled (r other : Row) (x : E) : Row :=
  { r with runs := other.runs.foldl (fun runs w =>
      match runs.findIdx? (·.liesAs w) with
      | some i => runs.modify i (·.addScaled w x)
      | none => runs.push (w.scaled x)) r.runs }

/-- The row plus x times another row, coefficients and target. -/
def addScaled (r other : Row) (x : E) : Row :=
  let r1 := r.addRunsScaled other x
  { r1 with
    terms := r1.terms ++ other.terms.map fun t => { t with v := t.v.scale x }
    units := r1.units ++ other.units.map fun u => { u with coeff := mulE u.coeff x }
    forms := r1.forms ++ other.forms.map fun f => { f with c := f.c.scale x }
    target := maddE r1.target x other.target }

/-- The oracle messages that the row names. -/
def oracles (r : Row) : List Nat :=
  (r.terms.map (·.oracle)).toList ++ (r.units.map (·.oracle)).toList ++
    (r.runs.map (·.oracle)).toList ++ (r.forms.map (·.oracle)).toList

/-- The row r on another oracle message: each of its terms, single entries, runs and forms names
o. -/
def renamed (r : Row) (o : Nat) : Row :=
  { r with
    terms := r.terms.map fun t => { t with oracle := o }
    units := r.units.map fun u => { u with oracle := o }
    runs := r.runs.map fun w => { w with oracle := o }
    forms := r.forms.map fun f => { f with oracle := o } }

end Row

/-! ## The layout of a group -/

/-- Places blocks of 2^(size i) rows from row 0 by decreasing size, ties in the given order. A
member without a size takes no block. Returns the first row of each block and the rows taken in
all. -/
def layBlocks (sizes : Array (Option Nat)) : Array (Option Nat) × Nat :=
  let top := sizes.foldl (fun m s => max m (s.getD 0)) 0
  (List.range (top + 1)).reverse.foldl (fun acc e =>
    (List.range sizes.size).foldl (fun (acc : Array (Option Nat) × Nat) i =>
      if sizes.getD i none == some e then (acc.1.setIfInBounds i (some acc.2), acc.2 + 2 ^ e)
      else acc) acc) (Array.replicate sizes.size none, 0)

namespace Statement

/-- The layout of group g. -/
def layout (S : Statement) (g : Nat) : Option GroupLayout :=
  (S.groups[g]?).map fun G =>
    let sizes (part : Part) : Array (Option Nat) :=
      (Array.range G.members.size).map fun i =>
        let o := G.members.getD i noId
        if S.has o part && !(part == .main && G.kept.getD i false) then some (S.rowBits o part)
        else none
    let mask := layBlocks (sizes .mask)
    let main := layBlocks (sizes .main)
    let h := ceilLog2 mask.2
    { k := max (max (ceilLog2 main.2) h) 1, h := h,
      logEll := (S.codes.base.getD G.code default).logEll,
      logEllZk := (S.codes.mask.getD G.maskCode default).logEll,
      members := G.members, kept := G.kept, mainFirst := main.1, maskFirst := mask.1 }

end Statement

/-- The index, in a group's table with 2^groupRowBits rows, of entry index of a member's table with
2^rowBits rows whose block begins at row first. -/
def groupIndex (index rowBits first groupRowBits : Nat) : Nat :=
  (first + index % 2 ^ rowBits) + (index / 2 ^ rowBits) * 2 ^ groupRowBits

/-- Changes the form on the kept member o, which is entered at its place if it is not there. -/
def onKept (kept : Array KeptForm) (o : Nat) (f : Form → Form) : Array KeptForm :=
  match kept.findIdx? (·.oracle == o) with
  | some i => kept.modify i fun x => { x with c := f x.c }
  | none =>
    let before := kept.filter (·.oracle < o)
    let behind := kept.filter (o < ·.oracle)
    before ++ #[⟨o, f {}⟩] ++ behind

/-- The row with its mask table written out: zeros, if it had none yet. -/
def GroupRow.ready (acc : GroupRow) (L : GroupLayout) : GroupRow :=
  if acc.d.isEmpty then { acc with d := Array.replicate (2 ^ (L.h + L.logEllZk)) zeroE } else acc

/-- acc plus x times coeff on one entry of a member's table, carried to the group's tables. -/
def addEntryTo (S : Statement) (L : GroupLayout) (x : E) (acc : GroupRow) (o : Nat) (part : Part)
    (index : Nat) (coeff : E) : Option GroupRow :=
  match L.find o with
  | none => none
  | some i =>
    let a := S.rowBits o part
    match part with
    | .mask =>
      match L.maskFirst.getD i none with
      | none => none
      | some first =>
        let j := groupIndex index a first L.h
        if j < acc.d.size then some { acc with d := acc.d.modify j fun y => maddE y x coeff }
        else none
    | .main =>
      if L.kept.getD i false then
        some { acc with kept := onKept acc.kept o fun f => f.addEntry index (mulE x coeff) }
      else
        match L.mainFirst.getD i none with
        | none => none
        | some first =>
          some { acc with c := acc.c.addEntry (groupIndex index a first L.k) (mulE x coeff) }

/-- acc plus x times a structured vector on a member's table. -/
def addTermTo (S : Statement) (L : GroupLayout) (x : E) (acc : GroupRow) (t : Term) :
    Option GroupRow :=
  match L.find t.oracle with
  | none => none
  | some i =>
    let v := t.v.scale x
    let a := S.rowBits t.oracle t.part
    match t.part with
    | .main =>
      if L.kept.getD i false then
        some { acc with kept := onKept acc.kept t.oracle fun f => f.add v }
      else
        match L.mainFirst.getD i none with
        | none => none
        | some first =>
          if L.k < a then none
          else some { acc with c := acc.c.add (v.insertChoice a (L.k - a) (first / 2 ^ a)) }
    | .mask =>
      match L.maskFirst.getD i none with
      | none => none
      | some first =>
        if L.h < a then none
        else some { acc with d := (v.insertChoice a (L.h - a) (first / 2 ^ a)).addTo acc.d }

/-- acc plus x times a run of coefficients, entry by entry. -/
def addRunTo (S : Statement) (L : GroupLayout) (x : E) (acc : GroupRow) (w : Run) :
    Option GroupRow :=
  (List.range w.coeffs.size).foldlM (fun acc j =>
    addEntryTo S L x acc w.oracle w.part (w.first + w.step * j) (w.coeffs.get j)) acc

/-- acc plus x times a whole coefficient vector on a member's main table. -/
def addFormTo (S : Statement) (L : GroupLayout) (x : E) (acc : GroupRow) (f : MainForm) :
    Option GroupRow :=
  match L.find f.oracle with
  | none => none
  | some i =>
    if L.kept.getD i false then
      some { acc with kept := onKept acc.kept f.oracle fun c => c.addForm f.c x }
    else
      let a := S.rowBits f.oracle .main
      match L.mainFirst.getD i none with
      | none => none
      | some first =>
        if L.k < a then none
        else some { acc with c := acc.c.addForm (f.c.insertChoice a (L.k - a) (first / 2 ^ a)) x }

/-- acc plus x times the row, with every coefficient vector carried from its member's table to the
group's tables. Nothing if the row names an oracle message or a table that the layout does not have,
or if an entry is beyond the group's mask table. An index on a main table is not bounded here:
Blk.addRow bounds it for open rows, and the sampling makes the sample rows. -/
def addToGroupRow (S : Statement) (L : GroupLayout) (row : Row) (x : E) (acc : GroupRow) :
    Option GroupRow := do
  let acc1 ← row.terms.foldlM (addTermTo S L x) (acc.ready L)
  let acc2 ← row.units.foldlM (fun acc u =>
    addEntryTo S L x acc u.oracle u.part u.index u.coeff) acc1
  let acc3 ← row.runs.foldlM (addRunTo S L x) acc2
  let acc4 ← row.forms.foldlM (addFormTo S L x) acc3
  pure { acc4 with target := maddE acc4.target x row.target }

/-! ## Calls on the statement

What the C++ types enforce and these do not. In blocks/iop/relation.h only the sampling block can
set the mark that an oracle message is sampled (sampled_elsewhere(), which every caller can call,
copies a mark that was set in another statement), and no caller can change the rows that begin_run()
hands over. In blocks/iop/mask.h a mask entry that was handed out is a value that cannot be copied.
Here Blk.onOracle and Blk.setStatement are open to every block, RunInput is plain data, and
Blk.takeMask returns a number. So nothing in this file tests that only the sampling and
Blk.sampledElsewhere mark a message as sampled, that a batching takes all rows of a RunInput, or
that a number from Blk.takeMask is used once. -/

namespace Blk

/-- The oracle message number o. -/
def oracle (o : Nat) : Blk Oracle := do get ((← statement).oracles[o]?)

/-- The group number g. -/
def group (g : Nat) : Blk Group := do get ((← statement).groups[g]?)

/-- Changes the oracle message number o. -/
def onOracle (o : Nat) (f : Oracle → Oracle) : Blk Unit := fun c =>
  if o < c.st.oracles.size then
    .ok ((), { c with st := { c.st with oracles := c.st.oracles.modify o f } })
  else .error { name := unnamed }

/-- Changes the group number g. -/
def onGroup (g : Nat) (f : Group → Group) : Blk Unit := fun c =>
  if g < c.st.groups.size then
    .ok ((), { c with st := { c.st with groups := c.st.groups.modify g f } })
  else .error { name := unnamed }

/-- A new group under a main code and a mask code. Returns its number. -/
def newGroup (code : Nat) (maskCode : Nat := 0) : Blk Nat := do
  let S ← statement
  let c ← get S.codes.base[code]?
  let z ← get S.codes.mask[maskCode]?
  must (decide (z.logN ≤ c.logN))
  setStatement { S with groups := S.groups.push { code := code, maskCode := maskCode } }
  pure S.groups.size

/-- An oracle message that is not sampled becomes the mask of one fold, or of the last step of one
proximity test. This can be done once. -/
def spendAsMask (o : Nat) : Blk Unit := do
  let x ← oracle o
  must (!x.sampled && x.shape.answers == 0 && !x.spentAsMask)
  onOracle o fun x => { x with spentAsMask := true }

/-- The oracle message o becomes a member of group g, with all its rows. Only a sampled message can
join, and none after the group's proximity test has begun. A message without main rows may join a
group of any main code. kept: its main rows are read and tested with the group and not folded with
the group's other rows (GroupLayout). -/
def join (g o : Nat) (kept : Bool := false) : Blk Unit := do
  let G ← group g
  let x ← oracle o
  must (x.sampled && !G.inRun)
  must (x.shape.mainRows == 0 || x.shape.code == G.code)
  must (x.shape.maskRows == 0 || x.shape.maskCode == G.maskCode)
  must (!G.members.contains o)
  must (!kept || decide (0 < x.shape.mainRows))
  let pos := (G.members.filter (· < o)).size
  onGroup g fun G => { G with
    members := G.members.insertIdxIfInBounds pos o, kept := G.kept.insertIdxIfInBounds pos kept }
  onOracle o fun x => { x with groups := x.groups ++ [g] }

/-- The next number, from n on, whose low logRows bits name a real row. fuel bounds the steps;
2^logRows is enough if there is a real row. When the fuel is used up, the number reached is returned
untested. -/
def nextRealRow (rows logRows : Nat) : Nat → Nat → Nat
  | 0, n => n
  | fuel + 1, n => if n % 2 ^ logRows < rows then n else nextRealRow rows logRows fuel (n + 1)

/-- Takes the next free mask entry of o. Returns its index in o's mask table. -/
def takeMask (o : Nat) : Blk Nat := do
  let x ← oracle o
  let l ← get x.ledger
  must (!l.closed && decide (0 < l.left))
  let n := nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next
  onOracle o fun x => { x with ledger := some { l with next := n + 1, left := l.left - 1 } }
  pure n

/-- Takes the next count free mask entries of o and appends their indices to acc. -/
def takeMasksInto (o : Nat) : Nat → Array Nat → Blk (Array Nat)
  | 0, acc => pure acc
  | n + 1, acc => do
    let a ← takeMask o
    takeMasksInto o n (acc.push a)

/-- Takes the next count free mask entries of o. -/
def takeMasks (o count : Nat) : Blk (List Nat) := do
  pure (← takeMasksInto o count #[]).toList

/-- Closes the ledger of o, if it has one: from then on no entry is handed out. -/
def closeLedger (o : Nat) : Blk Unit :=
  onOracle o fun x => { x with ledger := x.ledger.map fun l => { l with closed := true } }

/-- A summand of a row (a term, a single entry, a run or a form) fits its place: the oracle message
is a member of the group, has the table, the number of variables is the table's, and the index is
within the table. -/
def placeOk (S : Statement) (G : Group) (o : Nat) (part : Part) (vars index : Nat) : Bool :=
  G.members.contains o && S.has o part && vars == S.tableBits o part &&
    decide (index < 2 ^ S.tableBits o part)

/-- A new open row on group g. Every oracle message that it names is a member of g, and it has the
coefficient 0 on every entry that masks an answer to a sample (Oracle.pad). It is not a sample row:
only the sampling (OnBytes/Iop/Send.lean) makes those. The dry run keeps no rows: it tests only that
the group is there and still takes rows (its proximity test has not begun) and that the row is not
marked as a sample row. -/
def addRow (g : Nat) (row : Row) : Blk Unit := do
  let S ← statement
  let G ← group g
  must (!G.inRun && row.kind != .sample)
  if ← isDry then return
  must (row.terms.all fun t => t.v.ok && placeOk S G t.oracle t.part t.v.vars 0)
  must (row.units.all fun u => placeOk S G u.oracle u.part (S.tableBits u.oracle u.part) u.index)
  must (row.runs.all fun w =>
    w.coeffs.ok && decide (0 < w.coeffs.size) && decide (1 ≤ w.step) &&
      placeOk S G w.oracle w.part (S.tableBits w.oracle w.part)
        (w.first + w.step * (w.coeffs.size - 1)))
  must (row.forms.all fun f =>
    placeOk S G f.oracle .main (S.tableBits f.oracle .main) 0 &&
      f.c.fits (S.tableBits f.oracle .main))
  test (G.members.all fun o =>
    ((S.oracles[o]?).map (·.pad)).getD [] |>.all fun p => isZeroE (row.coefficient o p.1 p.2))
  onGroup g fun G => { G with rows := G.rows.push row }

/-- New open rows on group g, which only a run on a view computes. -/
def addRowsOnView (g : Nat) (rows : Unit → Option (List Row)) : Blk Unit := do
  let G ← group g
  must (!G.inRun)
  let l ← getOnView [] rows
  l.forM (addRow g)

/-- The layout of group g. -/
def layout (g : Nat) : Blk GroupLayout := do get ((← statement).layout g)

/-- The proximity test on g begins. Its rows and members are final and its members' ledgers are
closed. Returns the layout and the rows in the fixed order: the plain rows as they were created;
each member's sample rows, the members as they were sent; the generator rows as they were
created. -/
def beginRun (g : Nat) : Blk RunInput := do
  let G ← group g
  must (!G.inRun && !G.members.isEmpty)
  let L ← layout g
  let S ← statement
  let samples := G.members.foldl (fun a o =>
    a ++ ((S.oracles[o]?).map (·.sampleRows)).getD #[]) #[]
  G.members.forM closeLedger
  onGroup g fun G => { G with inRun := true, rows := #[] }
  let plain := G.rows.filter (·.kind == .plain)
  pure ⟨L, plain ++ samples ++ G.rows.filter (·.kind == .generator)⟩

/-- Every oracle message that the row names has been sampled: what the row says is then about
definite messages. -/
def requireSampled (row : Row) : Blk Unit := do
  let S ← statement
  must (row.oracles.all fun o => ((S.oracles[o]?).map (·.sampled)).getD false)

/-- For the end of a protocol: the proximity test of every group has begun (Blk.beginRun; this test
cannot tell whether it was carried through), and every sampled oracle message is a member of a
group. A row or an oracle message that no test takes in would have been claimed and never checked.
This test cannot tell of a row that was never added to a group, such as one that waits to be batched
or split. -/
def requireAllTested : Blk Unit := do
  let S ← statement
  must (S.groups.all (·.inRun) && S.oracles.all fun x => !x.sampled || !x.groups.isEmpty)

end Blk

/-! ## Which oracle messages share a tree -/

/-- Places the oracle messages of one prover's message in trees (R7.12; lay_trees in
blocks/iop/context.h). Those of one class whose main rows have one length share a tree. An oracle
message without main rows joins the first tree of its class or, if there is none, a new tree that
holds only mask rows. Trees are numbered as they arise; parts are in a tree in the order of sending.
Nothing if mask rows of two lengths meet in one tree, or mask rows are longer than the main rows of
their tree. -/
def layTrees (codes : Codes) (sent : Array OracleNotice) : Option TreeLay := do
  let pass (maskOnly : Bool) (s : Array TreeShape × Array Nat × Array Nat) :
      Array TreeShape × Array Nat × Array Nat :=
    (List.range sent.size).foldl (fun s i =>
      let n := sent.getD i default
      if (n.shape.mainRows == 0) != maskOnly then s
      else
        let logN := (codes.base.getD n.shape.code default).logN
        let fits (t : Nat) : Bool :=
          s.2.1.getD t noId == n.leafClass && (maskOnly || (s.1.getD t {}).logN == logN)
        match (List.range s.1.size).find? fits with
        | some t => (s.1, s.2.1, s.2.2.setIfInBounds i t)
        | none =>
          (s.1.push (if maskOnly then {} else { logN := logN }), s.2.1.push n.leafClass,
            s.2.2.setIfInBounds i s.1.size)) s
  let laid := pass true (pass false (#[], #[], Array.replicate sent.size 0))
  let tree := laid.2.2
  -- The state: the trees; each message's place in its tree; each tree's width of mask symbols so
  -- far. Only numbers are read from a tree before Array.modify, so the tree is not shared and its
  -- arrays grow without being copied.
  let filled ← (List.range sent.size).foldlM
    (fun (s : Array TreeShape × Array Nat × Array Nat) i => do
      let n := sent.getD i default
      let at0 := tree.getD i 0
      let zk := (codes.mask.getD n.shape.maskCode default).logN
      let before := (s.1.getD at0 {}).mainSymbols.size
      if 0 < n.shape.maskRows && 0 < s.2.2.getD at0 0 && (s.1.getD at0 {}).logNzk != zk then none
      else
        pure (s.1.modify at0 fun t =>
            { t with
              logNzk := if 0 < n.shape.maskRows then zk else t.logNzk
              mainSymbols := t.mainSymbols.push (n.shape.mainRows * n.shape.mainDeg)
              maskSymbols := t.maskSymbols.push (n.shape.maskRows * 3) },
          s.2.1.push before, s.2.2.modify at0 (· + n.shape.maskRows * 3)))
    (laid.1, #[], Array.replicate laid.1.size 0)
  let shapes := filled.1.map fun t => if t.mainWidth == 0 then { t with logN := t.logNzk } else t
  if shapes.all fun t => t.maskWidth == 0 || t.logNzk ≤ t.logN then
    pure { tree := tree, part := filled.2.1, shapes := shapes }
  else none

namespace Blk

/-- The book of trees. -/
def theBook : Blk TreeBook := fun c => .ok (c.book, c)

/-- Replaces the book of trees by B. -/
def setBook (B : TreeBook) : Blk Unit := fun c => .ok ((), { c with book := B })

/-- The conditions on the shape of an oracle message that is sent (Statement::sent in
blocks/iop/relation.h): it has rows, the codes of the rows that it has exist, and mainDeg is 1 or 3.
Unlike shapeFaultless it looks at the list of codes, and it asks mainDeg also of a message without
main rows. -/
def shapeOk (codes : Codes) (s : OracleShape) : Bool :=
  decide (0 < s.mainRows + s.maskRows) &&
    (s.mainRows == 0 || decide (s.code < codes.base.size)) &&
    (s.maskRows == 0 || decide (s.maskCode < codes.mask.size)) &&
    (s.mainDeg == 1 || s.mainDeg == 3)

/-- Receives the roots of all oracle messages of the present prover's message, enters the messages
into the statement and places them in trees. Returns the messages' numbers, in the order given. -/
def receiveOracles (sent : Array OracleNotice) : Blk (Array Nat) := do
  let S ← statement
  let B ← theBook
  let first ← firstTree
  must (sent.all fun n => shapeOk S.codes n.shape)
  must (S.oracles.size == B.place.size)
  let lay ← get (layTrees S.codes sent)
  let base := B.trees.size
  let ids := (Array.range sent.size).map (· + S.oracles.size)
  let mut trees := B.trees
  for s in lay.shapes do
    let n ← recvRoot
    trees := trees.push { shape := s, number := first + n, src := .own n }
  for i in List.range sent.size do
    let t := base + lay.tree.getD i 0
    let unsampled := (sent.getD i default).shape.answers == 0
    trees := trees.modify t fun x => { x with
      parts := x.parts.push (S.oracles.size + i), oneList := x.oneList || unsampled }
  setStatement { S with oracles := S.oracles ++ sent.map fun n => { shape := n.shape } }
  setBook { trees := trees,
            place := B.place ++ (Array.range sent.size).map fun i =>
              (base + lay.tree.getD i 0, lay.part.getD i 0) }
  pure ids

/-- True if, as far as both lists go, each opened column has the key, is at the list's position and
has W words. The shorter list ends the comparison: the caller compares the lengths. A loop: the
depth of the recursion does not grow with the number of positions. -/
def columnsFit (key W : Nat) : List (Nat × Nat × List UInt64) → List Nat → Bool
  | y :: ys, x :: xs => y.1 == key && y.2.1 == x && y.2.2.length == W && columnsFit key W ys xs
  | _, _ => true

/-- The columns of one tree at a list of positions in the tree's own range. In the dry run the
opening is noted at the round that was closed last. On a view the next columns are taken; each must
have the tree's key, be at the list's position and have the tree's width. The key is the tree's
number less Chan.firstTree, or 0 if the number is lower. It is not a name: a tree that was taken
over can have the key of one of the chain's own trees. The order of the columns tells them apart. -/
def takeColumns (t : Tree) (xs : Array Nat) : Blk (Array (Array F)) := fun c =>
  let W := t.shape.mainWidth + t.shape.maskWidth
  if c.ch.dry then
    if c.ch.noted.isEmpty then .error { name := planName }
    else
      let sh : Fmt.Shape := { a := t.shape.logN, W := W, stored := false, tree := t.number }
      .ok (xs.map fun _ => Array.replicate W 0,
        { c with ch := { c.ch with noted := c.ch.noted.modify (c.ch.noted.size - 1) fun n =>
            { n with opens := n.opens ++ [(sh, t.src)] } } })
  else
    let got := c.ch.opened.take xs.size
    if got.length == xs.size && columnsFit (t.number - c.ch.firstTree) W got xs.toList then
      .ok ((got.map fun y => y.2.2.toArray).toArray,
        { c with ch := { c.ch with opened := c.ch.opened.drop xs.size } })
    else .error { name := shapeName }

/-- The rule on what shares a leaf (R7.17 (a), (b)), tested at every opening. A leaf is opened
whole, so all parts of a tree are shown at every list at which the tree is opened. So the sampled
parts must belong to the same groups, and a tree that holds the mask of one step is opened once in
all, its other parts belonging to one group at most. A layout that breaks the rule is public: a
fault of a block's text, never of a proof. The call also counts the opening. -/
def countOpening (t : Nat) : Blk Unit := do
  let S ← statement
  let B ← theBook
  let tree ← get B.trees[t]?
  let groups := tree.parts.toList.filterMap fun o =>
    (S.oracles[o]?).bind fun x => if x.shape.answers == 0 then none else some x.groups
  must (match groups with
    | [] => true
    | a :: l => l.all (· == a) && (!tree.oneList || decide (a.length ≤ 1)))
  must (!tree.oneList || tree.lists == 0)
  setBook { B with trees := B.trees.modify t fun x => { x with lists := x.lists + 1 } }

/-- The list at which a tree is opened under a list of positions: the list itself, or for a shorter
tree the list of the draws modulo the tree's length. -/
def ownList (tree : Tree) (pos : Positions) : Array Nat :=
  if tree.shape.logN == pos.logN then pos.all
  else (listOfT (pos.draws.map (· % 2 ^ tree.shape.logN)).toList).toArray

/-- The loop of openTrees: what was opened is appended to acc. The depth of the recursion does not
grow with the number of trees. -/
def openTreesInto (B : TreeBook) (pos : Positions) :
    List Nat → Array (Nat × Array Nat × Array (Array F)) →
      Blk (List (Nat × Array Nat × Array (Array F)))
  | [], acc => pure acc.toList
  | t :: ts, acc => do
    countOpening t
    let tree ← get B.trees[t]?
    must (decide (tree.shape.logN ≤ pos.logN))
    let xs := ownList tree pos
    let cols ← takeColumns tree xs
    openTreesInto B pos ts (acc.push (t, xs, cols))

/-- Opens the trees at these places of the book B, one after the other. Returns for each its place,
the list at which it was opened, and the columns at that list. -/
def openTrees (B : TreeBook) (pos : Positions) (ts : List Nat) :
    Blk (List (Nat × Array Nat × Array (Array F))) := openTreesInto B pos ts #[]

/-- The symbols of one oracle message in a leaf's column c. Its main symbols begin at the word
mainSkip and its mask symbols at the word maskSkip. A symbol over the extension field is three
words. -/
def columnOf (x : Oracle) (mainSkip maskSkip : Nat) (c : Array F) : Column :=
  let three (start b : Nat) : E :=
    E.mk3 (c.getD (start + 3 * b) 0) (c.getD (start + 3 * b + 1) 0) (c.getD (start + 3 * b + 2) 0)
  { main := (Array.range x.shape.mainRows).map fun b =>
      if x.shape.mainDeg == 1 then ofF (c.getD (mainSkip + b) 0) else three mainSkip b
    mask := (Array.range x.shape.maskRows).map fun b => three maskSkip b }

/-- The symbols of the oracle message o, which is part p.2 of tree p.1, at every position of the
list, out of the opened trees' columns. Nothing if the tree is not among them. -/
def symbolsOf (S : Statement) (B : TreeBook) (pos : Positions)
    (cols : List (Nat × Array Nat × Array (Array F))) (o : Nat) (p : Nat × Nat) :
    Option (Array Column) := do
  let tree ← B.trees[p.1]?
  let x ← S.oracles[o]?
  let mine ← cols.find? (·.1 == p.1)
  let mainSkip := (tree.shape.mainSymbols.extract 0 p.2).foldl (· + ·) 0
  let maskSkip := tree.shape.mainWidth + (tree.shape.maskSymbols.extract 0 p.2).foldl (· + ·) 0
  (Array.range pos.all.size).mapM fun i => do
    let here ←
      if tree.shape.logN == pos.logN then some i
      else mine.2.1.idxOf? (pos.all.getD i 0 % 2 ^ tree.shape.logN)
    let c ← mine.2.2[here]?
    pure (columnOf x mainSkip maskSkip c)

/-- Reads the openings of the oracle messages' trees at the list and returns the symbols: entry
w of the result belongs to the w-th oracle message asked for, and its entry i to the i-th position
of the list. Rows are read at the position modulo their length. The oracle messages asked for must
be all that their trees hold: a leaf is opened whole, so an opening that left one out would read
that one at a list that is not its own. Unlike read_opened (blocks/iop/context.h) this call checks
no opening against a root: the strict reader has done that before there is a view. -/
def readOpened (ids : Array Nat) (pos : Positions) : Blk (Array (Array Column)) := do
  let S ← statement
  let B ← theBook
  let places ← get (ids.mapM fun o => B.place[o]?)
  let trees := listOfT (places.map (·.1)).toList
  must (trees.all fun t => ((B.trees[t]?).map (·.parts)).getD #[] |>.all ids.contains)
  let cols ← openTrees B pos trees
  get ((ids.zip places).mapM fun y => symbolsOf S B pos cols y.1 y.2)

/-- Reads the opening of a stored table (a tree that is made once and read by many runs) after the
round of positions that was closed last. t says how a reader finds the tree: its shape, the bytes of
a leaf's salt, the statement's item that holds the root, and its share of the round's draws (R7.19).
Returns the list of that share (each position once, increasing, modulo the tree's length) and the
columns at the list. -/
def readStored (t : Fmt.Stored) (pos : Positions) : Blk (Array Nat × Array (Array F)) := fun c =>
  let xs := listOfT ((Fmt.partOf t pos.draws.toList).map (· % 2 ^ t.sh.a))
  if c.ch.dry then
    if c.ch.noted.isEmpty then .error { name := planName }
    else
      .ok ((xs.toArray, (xs.map fun _ => Array.replicate t.sh.W 0).toArray),
        { c with ch := { c.ch with noted := c.ch.noted.modify (c.ch.noted.size - 1) fun n =>
            { n with stored := n.stored ++ [t] } } })
  else
    let got := c.ch.opened.take xs.length
    if got.length == xs.length && columnsFit (Fmt.storedKey t.item) t.sh.W got xs then
      .ok ((xs.toArray, (got.map fun y => y.2.2.toArray).toArray),
        { c with ch := { c.ch with opened := c.ch.opened.drop xs.length } })
    else .error { name := shapeName }

/-- The oracle message mine of this statement is the oracle message theirs of another statement of
the same session, where it has been sampled. (One oracle message can be tested in several
statements, each with its own chain; every test takes in the one sample.) The sample rows are
copied; a message from elsewhere gives no mask entries here. Not tested here, and the caller's duty
(sampled_elsewhere in blocks/iop/relation.h):
 - that the two are one oracle message (same tree, same root): only shapes and codes are compared;
 - that its root, the seed of its sample and its answers are fixed before the first challenge of
   this statement's chain, that is, that they are in the chain's first query. A statement knows
   nothing of chains.
Nor does a proximity test that begins here close the message's ledger in the other statement. -/
def sampledElsewhere (mine : Nat) (other : Statement) (theirs : Nat) : Blk Unit := do
  let S ← statement
  let x ← oracle mine
  let y ← get other.oracles[theirs]?
  let a := x.shape
  let b := y.shape
  must (y.sampled && !x.sampled)
  must (a.mainRows == b.mainRows && a.mainDeg == b.mainDeg && a.maskRows == b.maskRows &&
    a.answers == b.answers)
  must (a.mainRows == 0 || S.codes.base[a.code]? == other.codes.base[b.code]?)
  must (a.maskRows == 0 || S.codes.mask[a.maskCode]? == other.codes.mask[b.maskCode]?)
  onOracle mine fun x => { x with
    sampled := true, sampleRows := y.sampleRows.map (·.renamed mine), pad := y.pad }

/-- Enters oracle messages whose trees another chain of the session has sent (R7.13 (c)). No root is
received. given: for each tree that the messages make, in the order in which the trees arise, its
number (R7.13) and where a reader takes its root and start from. Tested here: every notice is of a
message that is sampled (answers is not 0). The messages enter as not yet sampled;
Blk.sampledElsewhere marks them. Not tested here, and the caller's duty: that these are all the
messages in these trees where they were sent (R7.17 (d): a leaf is opened whole); only then does the
test show that no tree holds the mask of one step (R7.17 (c)). And that trees are taken over before
the chain sends its first own tree: Chan.firstTree counts them. -/
def adoptOracles (sent : Array OracleNotice) (given : Array (Nat × Fmt.Src)) :
    Blk (Array Nat) := do
  let S ← statement
  let B ← theBook
  must (sent.all fun n => shapeOk S.codes n.shape && n.shape.answers != 0)
  must (S.oracles.size == B.place.size)
  let lay ← get (layTrees S.codes sent)
  must (lay.shapes.size == given.size)
  let base := B.trees.size
  let mut trees := B.trees
  for i in List.range given.size do
    let x := given.getD i (0, .own 0)
    trees := trees.push { shape := lay.shapes.getD i {}, number := x.1, src := x.2 }
  for i in List.range sent.size do
    trees := trees.modify (base + lay.tree.getD i 0) fun x => { x with
      parts := x.parts.push (S.oracles.size + i) }
  setStatement { S with oracles := S.oracles ++ sent.map fun n => { shape := n.shape } }
  setBook { trees := trees,
            place := B.place ++ (Array.range sent.size).map fun i =>
              (base + lay.tree.getD i 0, lay.part.getD i 0) }
  pure ((Array.range sent.size).map (· + S.oracles.size))

end Blk

/-- The book as a later chain of the session holds it. Each tree that the earlier chain has sent
counts as taken over: src says, for its number in the earlier chain's order of sending, where a
reader takes root and start from. -/
def TreeBook.goesOn (B : TreeBook) (src : Nat → Fmt.Src) : TreeBook :=
  { B with trees := B.trees.map fun t =>
      match t.src with
      | .own n => { t with src := src n }
      | .given _ _ => t }

end OnBytes
