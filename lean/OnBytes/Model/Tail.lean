-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Tail.lean: the smallness test, with which each of the three kinds of sub-proof ends.

A sub-proof has committed to integer matrices M_mu, packed into symbols (OnBytes/Model/FormF.lean).
The smallness test is the protocol's means to bound every cell and to tie the cells to the
evaluations that the rest of the sub-proof has used. This file computes the verifier's side of it.

This file follows verifier/src/vf_smallness_test.h and vf_smallness_test_members.inc of the C++
verifier, whose identifiers call this part the tail. A definition that has the name of a C++
routine follows that routine. The others are loops, or parts of a C++ routine, most of them of the
long routines objectsF, coefficientsF and tileSelfTestF.
   shapeF, piecesF, addTreesF             on public numbers, before a proof is read
   closeFuns, drawMatrixF, transcriptF    the messages
   objectsF (linJoin9, linBits9, weightsF, powersF, foldSums, leadF, linTie, linRead)   the claims
   selfTestF, coefficientsF, tileSelfTestF   the weights, and tests on them
A sub-proof calls them in this order: shape, addTrees and t2Plan when its plan is made; then, on a
proof, closeFuns, transcript, t2Batch, objectsF, selfTest, coefficients, rkSelfTest and doorH. Here
shape only calls shapeF, and so on; rkSelfTest only calls tileSelfTestF. t2Plan, t2Batch and doorH
are in OnBytes/Model/Trees.lean. The types do not enforce that order; the routines test parts of it.
Nothing here ties the public numbers to what the chain's reader has hashed: the sub-proof's plan
must do that (shapeF, addTreesF).

The docstring of HTailF2 describes the test's three steps, lists what the C++ files have and this
file has not, and says where each word is explained. That of Tail.names says how a failure gets its
name.

What this file does not claim. No theorem on the routines is stated here. Nothing here proves that
the cells of an accepted proof are small, or that this file agrees with the C++.
-/
import OnBytes.Model.Psc
import OnBytes.Model.Look
import OnBytes.Model.Trees

namespace OnBytes.Model

/-- The C++ verifier's names that this file writes as strings. shapeF and piecesF can also return a
name of Forest.names, and addTreesF a name of Trees.names. Names that occur only in comments are not
listed. The C++ verifier appends a hyphen and the name of a matrix or of a table to five names
(shape-matrix, shape-foreign, shape-functional, internal-t2f-unit, internal-t2f-functional), and the
name of an array to internal-t2f-untyped. Here the name ends before the hyphen.

Names of refusals. The functions that make the shapes and the list (shapeF, piecesF, addTreesF,
borderMeans, ownEntry, t2BL) return the name under which the C++ verifier refuses, without the
sub-proof's prefix that the C++ puts before some names. The small functions on public numbers that a
routine calls (zzCol, tabAt, closeFuns, powersF, leadF, foldSums and similar ones) return none where
the C++ verifier refuses. A routine in SubM or LinkM fails under the name that is the argument of
mustAs or testAs (OnBytes/Model/Frame.lean). As a rule it is the C++ verifier's name for the
failure; a comment or the docstring says where the C++ has other names. Where a routine unwraps a
none (SubM.get, SubM.ask) or calls SubM.must, the failure has no name of its own. The C++ verifier's
name is then in a comment or in the docstring, for a reader who compares the two programs. Two cases
stand apart. The C++ tests only in objectsF whether the lookup has run (internal-f-exist); here each
routine that needs tl.heard unwraps it, without a note. And some conditions have no line in the C++
routines, so the C++ has no name for them. Six fail on their own: that the list of matrices has NM
entries and that it has a column (both in drawMatrixF), that nU is what addTreesF was given
(selfTestF), that the array of U1 or U3 has a column (linRead; it fails here under internal-L-row),
and the lengths of hasU (shapeF) and of nU (addTreesF), which the C++ signatures state. The last two
fail here under internal-t2f-lists. Two more are conjuncts of tileSelfTestF's tests: the length of
the row weights of BZ's third virtual row (planesShapeHeld), and s.m <= 3 s.mS (tieWeightsHeld). A
name that begins with "internal" marks a test of the program on itself. It is meant to fail on no
file. The exceptions are the tests that a weight is not 0 and that the row weights of a tie differ:
an unlucky challenge can fail them; no bound on how often is stated or proved here. Either way the
run is not accepted: a call whose only refusals have such names ends NOT CHECKED (internalName and
cpStagesRun, OnBytes/Model/Stages.lean). -/
def Tail.names : List String :=
  ["hid-call-floor", "hid-k-range", "hid-tau", "internal-border-count", "internal-eq-index",
    "internal-f-exist", "internal-f-fun-closed", "internal-f-fun-moved", "internal-f-fun-open",
    "internal-f-join-place", "internal-f-matrix-order", "internal-f-padding-key",
    "internal-f-read-weights", "internal-f-table-read", "internal-f-tail-slot",
    "internal-f-tie-weights", "internal-L-row",
    "internal-t2-order", "internal-t2f-TX-order", "internal-t2f-ZF-order", "internal-t2f-blocks",
    "internal-t2f-functional", "internal-t2f-lists", "internal-t2f-map", "internal-t2f-unit",
    "internal-t2f-untiled", "internal-t2f-untyped", "plan-link", "policy-tau-hb", "shape-foreign",
    "shape-functional", "shape-matrix", "t2f-columns-range", "t2f-weight-class"]

/-! ## Constants and small functions -/

/-- The number of bits of the low digit of a combination plus beta. -/
def t2D0 : Nat := 10

/-- The number of bits of the high digit of a combination plus beta. -/
def t2D1 : Nat := lbz + 1 - t2D0

/-- The high digit has 8 bits, so the table of its lookup call has 2^8 rows. The number is fixed
here because the call of the high digits is named R8d and callHeld has its k written out as 8. -/
theorem t2D1_eq : t2D1 = 8 := by decide

/-- The loop of t2BL. fuel bounds the number of blocks. -/
def t2BLLoop (R : Nat) : (fuel r0 : Nat) → List (Nat × Nat)
  | 0, _ => []
  | fuel + 1, r0 =>
    if r0 < R then
      let Rp := 2 ^ Nat.log2 (R - r0)
      (r0, Rp) :: t2BLLoop R fuel (r0 + Rp)
    else []

/-- The blocks (first row, number of rows) that tile the rows 0, .., R - 1. A block is a run of rows
of ZZ, the array of the digits (HTailF2), whose length is a power of two. Each block is the largest
power of two that is not above what is left. Refuses (internal-t2f-blocks) unless each first row is
a multiple of its block's number of rows. -/
def t2BL (R : Nat) : Except String (Array (Nat × Nat)) :=
  let o := t2BLLoop R (Nat.log2 R + 1) 0
  if o.any fun x => x.1 % x.2 != 0 then .error "internal-t2f-blocks" else .ok o.toArray

/-- The weight of claim number c, one factor at a time. The tests on the weights use it to compute
again, independently, the power that Fork.kapAt computes by powE. -/
def t2fKappaByText (theta : E) (c : Nat) : E :=
  (List.range c).foldl (fun p _ => mulE p theta) oneE

/-- The sum of a vector's entries. -/
def sumE (v : Array E) : E := v.foldl addE zeroE

/-- True if L holds the entries first, .., first + count - 1 and none of them is 0. -/
def noneZero (L : Array E) (first count : Nat) : Bool :=
  decide (first + count ≤ L.size) && (L.extract first (first + count)).all fun x => !isZeroE x

/-- A symbol array that the sub-proof reads and to which an earlier sub-proof, its owner, has
committed. It holds one whole matrix. -/
structure T2Foreign where
  /-- the array's name in this sub-proof's list -/
  name : String := ""
  /-- the number of columns -/
  K : Nat := 0
  /-- the owner's count: 1 + the number of sub-proofs other than the owner that read the array -/
  a : Nat := 0
  /-- the owner's number of rows of cells -/
  m : Nat := 0
  /-- the owner's TMat.wp for the matrix: no line of the parameter file sets it, so it is 0 -/
  wp : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- The indices of the arrays in the sub-proof's list. An array is a committed matrix in the
sub-proof's list. Names taken from the C++ call an array a tree (gtTree, addTreesF, Fork.trees,
Run2.tree); in the comments a tree is always a tree of the lookup, whose keys are cut into trees of
one size (OnBytes/Model/Forest.lean). U1 to U3 are vectors over E, each an array of one row.

The arrays of a sub-proof, in the order of its list: those of the vectors U1 to U3 that it has, the
symbol arrays PK_i of the matrices that no other sub-proof reads, the symbol arrays PX_i of those
that another one reads, ZZ, BZ, and the symbol arrays PF_i that an earlier sub-proof has committed
to. ZZ has tau rows and 2 mz columns, where mz is the number of rows of cells of all matrices: the
low digits first, then the high digits. -/
structure T2Map where
  /-- U1 to U4; none for one that the sub-proof does not have. No sub-proof has U4; the C++ keeps
  the fourth place -/
  U : Array (Option Nat) := #[none, none, none, none]
  /-- the digits of the combinations -/
  ZZ : Nat := 0
  /-- the planes of the lookup's counts -/
  BZ : Nat := 0
  /-- the symbol arrays that another sub-proof reads -/
  TX : Array Nat := #[]
  /-- the symbol arrays that an earlier sub-proof has committed to -/
  FT : Array Nat := #[]
  /-- the symbol arrays that no other sub-proof reads -/
  PK : Array Nat := #[]
  /-- the number of arrays -/
  count : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-! ## The state of the smallness test -/

/-- The state of the smallness test of one sub-proof. The fields tau to plFor are set from public
numbers, funClosed to heard while the messages are read, vt to lsTail while the claims are added.
The letters in such names as t2BL, f9, nX4 and HTailF2 are the C++ verifier's and mean nothing here.

The test. A cell is an entry of a matrix M_mu. Three cells of one column are packed into one symbol,
so m rows of cells give ceil(m / 3) rows of symbols.
 1. The verifier draws a matrix C with entries in -1, 0, 1: tau entries for each column of each
    M_mu. The prover commits to the array ZZ. It holds the tau random combinations Z = M_mu C of
    every row of cells. Each is stored as Z + beta, with beta = 2^lbz = 2^17, cut into a low digit
    of 10 bits and a high digit of 8 bits. The prover also commits to BZ, the counts of a lookup as
    planes of bits.
 2. A lookup (OnBytes/Model/Look.lean) tests that each low digit is below 2^10 and each high digit
    below 2^8. If they are, every combination is in the range from -beta to beta - 1.
 3. Linear claims link ZZ to the rest. A tie, one for each matrix, says that the combinations are
    those of the matrix's symbols. A read, one for each table and each of its segments, says that a
    weighted sum of rows of cells, combined by C, is the same combination of the entries that the
    sub-proof holds in its vector U1 or U3.
All claims go into the sub-proof's one equation (OnBytes/Model/Trees.lean). A claim says that an
affine form in hidden values is 0 (the word "hidden" names a value's part in the protocol and claims
nothing: see OnBytes/Model/Hide.lean); claim number c enters the one equation with the weight
theta^c, where theta is the batching element.

Words. Each word is explained at the definition that it belongs to: cell, tie, read, claim and
"hidden" above, array, tree and the arrays' names at T2Map, block at t2BL, fold at foldColumns,
piece and key at piecesF, equation at equationsF, table and fun at closeFuns, plane at linBits9. A
virtual row of an array is a public combination of its rows, through which the claims read it (HRow,
OnBytes/Model/Hide.lean). A slot is the place of one scalar that the prover sends, and Fork is the
state of one sub-proof's check (same file). That file also explains chain, plan, dry run and mask
row. E is the extension field (OnBytes/Base.lean). Link, moment, the request's shape and the layout
are explained at the head of OnBytes/Model/Trees.lean.

Parts of vf_smallness_test.h and vf_smallness_test_members.inc without a counterpart in this file:
the planning of the rounds (planRounds; see OnBytes/Params/SubRounds.lean), the branch of
drawMatrixF for a transcript other than the proof's one chain, the hash of the list of tables (the
list itself is kept and compared), guards on mutable objects and pointers (symShapesHeldF, runT,
f9.cl, funLaidF), the test in transcriptF that ZZ and BZ have roots before the lookup's first
challenge (internal-f-order; rootInH, called just before, marks both or fails), the comparison in
tileSelfTestF of each call's alpha with the lookup's (a Call here holds no challenge), the empty
calls z[0] and z[3] with the test in tileSelfTestF that they are empty, the names of sections
(F.section), which no decision reads, the field nXof, which nothing reads, and the indices TT, BT,
YY and KK of T2Map, which nothing sets. -/
structure HTailF2 where
  /-- the run's number of random combinations; set before shape is called -/
  tau : Nat := 160
  /-- the run's log2 of the most keys in one tree of a lookup; set before shape is called -/
  lidb : Nat := lidbSealed
  /-- the number of rows of cells of all matrices together -/
  mz : Nat := 0
  /-- the number of matrices -/
  NM : Nat := 0
  /-- the matrices, in the sub-proof's order -/
  mats : Array TMat := #[]
  /-- for each matrix: its first row among the rows of cells of all matrices -/
  off : Array Nat := #[]
  /-- for each matrix: its first column in its symbol array -/
  col0 : Array Nat := #[]
  /-- for each matrix: its symbol array -/
  gtTree : Array Nat := #[]
  /-- for each matrix: the virtual row used in its symbol array -/
  gtRow : Array Nat := #[]
  /-- the number of columns of each PX_i -/
  kTX : Array Nat := #[]
  /-- the arrays of earlier sub-proofs -/
  ft : Array T2Foreign := #[]
  /-- the indices of the arrays in the sub-proof's list -/
  ix : T2Map := {}
  /-- the blocks of the tau rows of ZZ -/
  blocks : Array (Nat × Nat) := #[]
  /-- the lookup call of the low digits -/
  z1 : CallZ := { call := {} }
  /-- the lookup call of the high digits -/
  z2 : CallZ := { call := {} }
  /-- the public numbers of the lookup that holds both calls -/
  f9 : Forest.Shape := {}
  /-- the matrix of each PK_i -/
  pkMat : Array Nat := #[]
  /-- the matrix of each PX_i -/
  pxMat : Array Nat := #[]
  /-- for each matrix: the shape of its symbol array -/
  shp : Array ShP := #[]
  /-- the lengths of the vectors U1 to U3 -/
  nUF : Array Nat := #[0, 0, 0]
  /-- the first entry of the part of U1, and of U3, that holds tables. addTreesF makes U1's part
  empty and U3's part the whole of U3, so every table is in U3 -/
  tabFirst : Array Nat := #[0, 0]
  /-- the length of the part of U1, and of U3, that holds tables -/
  tabLen : Array Nat := #[0, 0]
  /-- the place of each PX_i, as its owner records it -/
  plOwn : Array PlaceF := #[]
  /-- the place of each PF_i, as its reader records it -/
  plFor : Array PlaceF := #[]
  /-- the list of tables is closed -/
  funClosed : Bool := false
  /-- the tables, as they were when the list was closed -/
  funs : Array HFun := #[]
  /-- the entries of the drawn matrix: tau for each column of each matrix -/
  cfF : Array Int := #[]
  /-- for each matrix: the index of its first column among the columns of all matrices; a last entry
  holds their count -/
  cfFirst : Array Nat := #[]
  /-- how many times the matrix has been drawn -/
  foldDrawn : Nat := 0
  /-- the first slot of the smallness test's messages -/
  slotA : Nat := 0
  /-- the slot after the last slot of the smallness test's messages -/
  slotB : Nat := 0
  /-- what the lookup has received and drawn -/
  heard : Option Forest.Heard := none
  /-- the weights of the combinations in the reads: the powers of the batching element -/
  vt : Array E := #[]
  /-- the weights of the combinations in the ties: the same vector as vt. It is not Fork.vp -/
  vp : Array E := #[]
  /-- for each matrix: the weights of its rows of symbols in its tie -/
  rowX : Array (Array E) := #[]
  /-- for each matrix: the weights of the rows of symbols that share one row of the array. There is
  one such row, so this is the vector (1) -/
  loX : Array (Array E) := #[]
  /-- the index of each matrix's first equation; a last entry holds the index of the first read's
  first equation -/
  eqFirst : Array Nat := #[]
  /-- for each matrix and column c: the sum over the combinations u of vp[u] C[c][u] -/
  gamX : Array (Array E) := #[]
  /-- for each matrix and column c: the sum over the combinations u of vt[u] C[c][u] -/
  gamV : Array (Array E) := #[]
  /-- for each matrix: its sums gamX and gamV have been computed -/
  foldTakenF : Array Bool := #[]
  /-- the index of the claim on the lookup's key vectors among the claims -/
  joinObj9 : Option Nat := none
  /-- the factor of the planes' value in the first claim that reads the planes -/
  bitFactor9 : E := zeroE
  /-- for each matrix: the index of its tie among the claims -/
  tieObj : Array Nat := #[]
  /-- for each array of the list: the number of ties added on it -/
  tiesOn : Array Nat := #[]
  /-- the number of reads added -/
  nX4Laid : Nat := 0
  /-- the weights on the slots from slotA up to slotB, as the smallness test's own claims left them
  -/
  lsTail : Array E := #[]

namespace HTailF2

/-- The number of blocks of ZZ's rows. -/
def zzBlocks (tl : HTailF2) : Nat := tl.blocks.size

/-- The virtual row of ZZ that the reads use. The rows before it belong to the pieces of the two
lookup calls. -/
def zzRowReads (tl : HTailF2) : Nat := 2 * tl.zzBlocks

/-- The virtual row of ZZ that the ties use. -/
def zzRowTies (tl : HTailF2) : Nat := 2 * tl.zzBlocks + 1

/-- The column of ZZ that holds a digit of row i of cells of matrix mu. plane 0: the low digit;
plane 1: the high digit. -/
def zzCol (tl : HTailF2) (mu plane i : Nat) : Option Nat :=
  if decide (mu < tl.NM) && decide (plane ≤ 1) && decide (i < (tl.mats.getD mu {}).m) then
    some (plane * tl.mz + tl.off.getD mu 0 + i)
  else none

/-- The entry of U1 or U3 that holds column c, segment sg of the table Fn. -/
def tabAt (tl : HTailF2) (Fn : HFun) (c sg : Nat) : Option Nat :=
  if decide (Fn.mat < tl.NM) && Fn.len != 0 then
    let M := tl.mats.getD Fn.mat {}
    let nsg := M.m / Fn.len
    if decide (c < M.k) && decide (sg < nsg) then some (Fn.start + c * nsg + sg) else none
  else none

/-- The call of the low digits for q = 0, of the high digits for q = 1. -/
def zOf (tl : HTailF2) (q : Nat) : CallZ := if q == 0 then tl.z1 else tl.z2

/-- The number of columns of BZ. BZ has 32 rows. -/
def bzColumns (tl : HTailF2) : Nat := 2 ^ (tl.f9.kT + tl.f9.cK)

/-- The number of scalars that the smallness test sends: those of its lookup. -/
def smallElems (tl : HTailF2) : Nat := Forest.elems tl.f9

/-- The number of columns of all matrices together. In names, fold means the random combinations
(foldSums, foldColumns, foldDrawn). -/
def foldColumns (tl : HTailF2) : Nat := tl.mats.foldl (fun s M => s + M.k) 0

/-- The number of lookups that have run: 0 or 1. -/
def groupsRun (tl : HTailF2) : Nat := if tl.heard.isSome then 1 else 0

/-- The number of bits of a tree's index in the lookup. -/
def rKF (tl : HTailF2) : Nat := tl.f9.rK

/-! ### Shapes from the list of matrices -/

/-- Makes the two lookup calls. A key is a value that is looked up, and a padding key fills a place
of the lookup that belongs to no cell. A piece is the rectangle of ZZ that one lookup call reads in
one block (Piece, OnBytes/Model/Forest.lean). Each call reads one half of ZZ's columns, in one piece
for each block of rows. Counts the padding keys of each tree of the lookup: the places after a
piece's columns in every row of the piece, and all keys after the last piece. Refuses unless tau is
a power of two or the sum of two (at tau = 160: blocks of 128 and 32 rows), and unless each call has
at least 2^10 keys. Forest.pubAsk tests the counts here, on the public numbers, and not only when a
proof is read (Forest.pad). placeZ also fills in each call's own field pub, by another rule; nothing
here reads that field. -/
def piecesF (tl : HTailF2) : Except String HTailF2 := do
  let bz ← t2BL tl.tau
  if bz.isEmpty || bz.size > 2 then throw "internal-t2f-blocks"
  let piece (row : Nat) (b : Nat × Nat) (c0 : Nat) : Piece :=
    { tree := tl.ix.ZZ, row := row, r0 := b.1, Rp := b.2, c0 := c0, Cp := tl.mz }
  let low := (Array.range bz.size).map fun i => piece i (bz.getD i (0, 0)) 0
  let high := (Array.range bz.size).map fun i => piece (bz.size + i) (bz.getD i (0, 0)) tl.mz
  -- the C++ verifier's names of the two calls
  let z1 := placeZ low "R10z" t2D0 tl.lidb
  let z2 := placeZ high "R8d" t2D1 tl.lidb
  if z1.call.n < 10 || z2.call.n < 10 then throw "hid-call-floor"
  let f9 ← Forest.shape #[z1.call, z2.call] tl.lidb
  let mut pub := Forest.noPub f9
  for q in [0, 1] do
    let c := if q == 0 then z1 else z2
    let mut stop := 0
    for p in c.pieces do
      if p.Cp < p.CP then
        for rr in List.range p.Rp do
          pub ← Forest.pubRun f9 pub q (p.off + rr * p.CP + p.Cp) (p.CP - p.Cp)
      stop := max stop (p.off + 2 ^ p.b)
    pub ← Forest.pubRun f9 pub q stop (2 ^ c.call.n - stop)
  Forest.pubAsk f9 pub
  pure { tl with blocks := bz, z1 := z1, z2 := z2, f9 := { f9 with pub := pub }, heard := none }

/-- Sets the shapes of the smallness test from the list m of matrices. TMat.kind is 0 for a matrix
that this sub-proof commits to and 1 for a matrix of an earlier sub-proof. Any other kind is refused
(t2f-weight-class): by the C++ comment, kind 2 is a matrix of weights, which cannot occur in a
sub-proof of a request. For kind 1, TMat.foreign says which array of f holds the matrix, and the
matrix is the whole of that array. The matrices of kind 1 take the arrays of f in order, each array
once. For kind 0, txOf[mu] = none means that no other sub-proof reads the matrix, and some i means
that it has the array PX_i, with i = 0, 1, .. in the order of the list. hasU has four entries:
hasU[n] says whether the sub-proof has the vector U(n+1). No sub-proof has U4, so hasU[3] must be
false. Of tl only the fields tau and lidb are read. The argument tau must equal tl.tau.

All arguments are public numbers of the model and of the run. This function does not tie them to
what the chain's reader has hashed. The sub-proof's plan, which makes them, must do that. -/
def shapeF (tl : HTailF2) (m : Array TMat) (txOf : Array (Option Nat)) (f : Array T2Foreign)
    (hasU : Array Bool) (tau : Nat) : Except String HTailF2 := do
  let NM := m.size
  if tau != tl.tau then throw "hid-tau"
  if txOf.size != NM || hasU.size != 4 || hasU.getD 3 false then throw "internal-t2f-lists"
  let mut pkMat : Array Nat := #[]
  let mut pxMat : Array Nat := #[]
  let mut kTX : Array Nat := #[]
  for mu in List.range NM do
    let M := m.getD mu {}
    if M.kind == 0 then
      match txOf.getD mu none with
      | some i =>
        if i != pxMat.size then throw "internal-t2f-TX-order"
        pxMat := pxMat.push mu
        kTX := kTX.push M.k
      | none => pkMat := pkMat.push mu
  -- A list has fewer than 256 matrices.
  if NM ≥ 256 then throw "plan-link"
  -- The list of arrays, in order: the U1 .. U3 that the sub-proof has, PK_i, PX_i, ZZ, BZ, PF_i.
  let mut count := 0
  let mut U : Array (Option Nat) := #[]
  for n in List.range 4 do
    if hasU.getD n false then
      U := U.push (some count)
      count := count + 1
    else U := U.push none
  let PK := (Array.range pkMat.size).map (count + ·)
  count := count + pkMat.size
  let TX := (Array.range pxMat.size).map (count + ·)
  count := count + pxMat.size
  let ZZ := count
  let BZ := count + 1
  count := count + 2
  let FT := (Array.range f.size).map (count + ·)
  count := count + f.size
  let mut mz := 0
  let mut off : Array Nat := #[]
  let mut gtTree : Array Nat := #[]
  let mut nextF := 0
  let mut nPK := 0
  let mut plOwn : Array PlaceF := Array.replicate pxMat.size {}
  let mut plFor : Array PlaceF := Array.replicate f.size {}
  for mu in List.range NM do
    let M := m.getD mu {}
    if M.m == 0 then throw "shape-matrix"
    if M.k == 0 || M.k > kcap then throw "hid-k-range"
    off := off.push mz
    mz := mz + M.m
    if M.kind == 0 then
      match txOf.getD mu none with
      | none =>
        gtTree := gtTree.push (PK.getD nPK 0)
        nPK := nPK + 1
      | some i =>
        gtTree := gtTree.push (TX.getD i 0)
        plOwn := plOwn.modify i fun pl => { pl with matrix := some (0, M.k, M.m) }
    else if M.kind == 1 then
      let j ← match M.foreign with
        | some j => pure j
        | none => throw "shape-foreign"
      let X ← match f[j]? with
        | some X => pure X
        | none => throw "shape-foreign"
      if M.ttOff != 0 || M.k != X.K || M.m != X.m || M.wp != X.wp then
        throw "shape-foreign"
      if j != nextF then throw "internal-t2f-ZF-order"
      nextF := nextF + 1
      gtTree := gtTree.push (FT.getD j 0)
      plFor := plFor.modify j fun pl => { pl with matrix := some (M.ttOff, M.k, M.m) }
    else throw "t2f-weight-class"
  if nextF != f.size then throw "internal-t2f-ZF-order"
  if 2 * mz ≥ 2 ^ 32 then throw "t2f-columns-range"
  piecesF
    { tau := tl.tau, lidb := tl.lidb, mz := mz, NM := NM, mats := m, off := off,
      col0 := Array.replicate NM 0, gtTree := gtTree, gtRow := Array.replicate NM 0, kTX := kTX,
      ft := f,
      ix := { U := U, ZZ := ZZ, BZ := BZ, TX := TX, FT := FT, PK := PK, count := count },
      pkMat := pkMat, pxMat := pxMat, plOwn := plOwn, plFor := plFor }

/-- The name under which the sub-proofs call shapeF. As in the C++, seven routines have two names.
-/
def shape (tl : HTailF2) (m : Array TMat) (txOf : Array (Option Nat)) (f : Array T2Foreign)
    (hasU : Array Bool) (tau : Nat) : Except String HTailF2 := tl.shapeF m txOf f hasU tau

/-- The number of linear claims that objectsF adds. First come the lookup's own claims
(Forest.lins). Four more claims of the lookup follow: one on the key vectors and three on the
planes. Then comes one tie for each matrix. The reads are last, nX4 in all: one for each table and
each of its segments. The calling sub-proof computes nX4 from its shapes, adds lins to the number of
its own claims and tests the total after its last claim. -/
def linsF (tl : HTailF2) (nX4 : Nat) : Nat := Forest.lins tl.f9 + 4 + tl.NM + nX4

/-- The name under which the sub-proofs call linsF. -/
def lins (tl : HTailF2) (nX4 : Nat) : Nat := tl.linsF nX4

/-- tau rounded up to a power of two: how many consecutive equation indices each row of symbols, or
each read, is given. -/
def stepF (tl : HTailF2) : Nat := 2 ^ clog2 tl.tau

/-- The number of indices that the smallness test's equations take. An equation of the smallness
test is another thing than the sub-proof's one equation: one of the many identities that a tie or a
read adds up, each under its own power of theta, the batching element. The number of indices is not
below the number of equations: tau and each matrix's number of rows of symbols are rounded up to
powers of two, and an index that names no equation stays unused. A tie is one claim, but it adds up
one equation for each row i of symbols and each combination u. A read adds up one for each u.
Equation (mu, i, u), for row i of symbols of matrix mu and combination u, has the index
eqFirst[mu] + i stepF + u, where eqFirst[mu] is the sum over the earlier matrices of stepF times
their number of rows of symbols rounded up to a power of two. The q-th read has the indices
eqFirst[NM] + q stepF + u. The equation with index j is weighted by the power planClaims + j of the
batching element, after the powers of the sub-proof's own claims; planClaims is the number of claims
in the sub-proof's plan (Fork.planClaimsF). The round of that element is planned with
planClaims + equationsF rows. By the C++ comment the numbering is that of blocks/iop/rng.h. -/
def equationsF (tl : HTailF2) (nX4 : Nat) : Nat :=
  tl.mats.foldl (fun n M => n + tl.stepF * 2 ^ clog2 ((M.m + 2) / 3)) 0 + nX4 * tl.stepF

/-- The same number as equationsF, as the run has it. doorH adds it to the number of claims and
tests that the batching element's round has that many rows in the plan. Only the reads are counted
as objectsF adds them. The matrices' equations are not counted: powersF has numbered them (eqFirst)
from the same matrices, by the same arithmetic as equationsF. Returns none before objectsF has run
(C++: internal-f-draws). -/
def equationsLaidF (tl : HTailF2) : Option Nat :=
  if tl.eqFirst.size != tl.NM + 1 then none
  else some (tl.eqFirst.getD tl.NM 0 + tl.nX4Laid * tl.stepF)

/-- The sub-proof that reads the array PF_iF records which array it means: the owner's number, and
the position of the array among the owner's symbol arrays (the PK_i, then the PX_i). The two numbers
are written once into the reader's record plFor[iF], which the plan compares with the owner's own
record (ownEntry, samePlaceF). -/
def borderMeans (tl : HTailF2) (iF ownerNo index : Nat) : Except String HTailF2 :=
  match tl.plFor[iF]? with
  | none => .error "internal-border-count"
  | some pl =>
    if pl.owner.isSome then .error "internal-border-count"
    else
      let meant : PlaceF := { pl with owner := some ownerNo, rootIndex := some index }
      .ok { tl with plFor := tl.plFor.set! iF meant }

/-- Records no, this sub-proof's number, as the owner in the record of each PX_i. -/
def ownerIs (tl : HTailF2) (no : Nat) : HTailF2 :=
  { tl with plOwn := tl.plOwn.map fun pl => { pl with owner := some no } }

/-- The owner's record of the place of a matrix that another sub-proof reads. The callers pass the
role "qa" or "stream". "qa" means the matrix named qa, any other role the matrix named xbO. The
record is found by that name in the owner's own list of matrices. It must never be looked up through
a field of a reader: the plan compares it with the reader's record (samePlaceF). -/
def ownEntry (tl : HTailF2) (role : String) : Except String PlaceF :=
  let want := if role == "qa" then "qa" else "xbO"
  let found := (List.range tl.pxMat.size).find? fun i =>
    (tl.mats.getD (tl.pxMat.getD i 0) {}).name == want
  match found with
  | none => .error "internal-border-count"
  | some i =>
    let pl := tl.plOwn.getD i {}
    if pl.whole then .ok pl else .error "internal-border-count"

/-! ### The list of arrays -/

/-- Fills in a record of a matrix's place from the shape of its symbol array. n: what the list
records about that array. hb: as in addTreesF. -/
def declared (pl : PlaceF) (n : N2) (hb : Nat) : PlaceF :=
  let s := n.p.getD {}
  { pl with
    sh := n.p, hb := hb, mS := s.mS, lanes := lanes, padRows := s.R * s.J, J := s.J, K := s.k,
    off := 0 }

/-- Adds the sub-proof's arrays to its list, in the order of the list (T2Map). nU: the lengths of U1
to U3. aTX[i]: 1 + the number of other sub-proofs whose lists of matrices contain the matrix of
PX_i. hb: the security level in bits for the records of shared matrices (PlaceF.hb). hbLine: the
security level in bits as the statement has it. tau must not be below hbLine. That bound is about
the statement's level and not about hb, which is less by the bits of proof of work (PlaceF.hb). The
C++ routine has no argument hbLine: it reads the variable statedTarget.hb. Nothing here ties hb,
hbLine, nU or aTX to the parameters that the chain's reader has hashed, or hb to hbLine. The
sub-proof's plan, which passes them in, must do that. -/
def addTreesF (tl : HTailF2) (F : Fork) (T : Tail2) (nU aTX : Array Nat) (hb hbLine : Nat) :
    Except String (HTailF2 × Fork × Tail2) := do
  if !T.nt.isEmpty then throw "internal-t2-order"
  let mut T : Tail2 := { T with link := true }
  let mut F : Fork := F
  if aTX.size != tl.pxMat.size || nU.size != 3 then throw "internal-t2f-lists"
  if tl.tau < hbLine then throw "policy-tau-hb"
  if (tl.ix.U.getD 3 none).isSome then throw "internal-t2f-lists"
  for n in List.range 3 do
    if let some want := tl.ix.U.getD n none then
      -- one row over E (ec = 3), no other reader, one virtual row
      let (got, F', T') ← t2AddN F T ("U" ++ toString (n + 1)) 1 (nU.getD n 0) 3 1 false 1
      if got != want then throw "internal-t2f-map"
      F := F'
      T := T'
  for i in List.range tl.pkMat.size do
    let M := tl.mats.getD (tl.pkMat.getD i 0) {}
    let (got, F', T') ← t2AddP F T ("PK" ++ toString i) M.m M.k M.wp 1 false
    if some got != tl.ix.PK[i]? then throw "internal-t2f-map"
    F := F'
    T := T'
  for i in List.range tl.pxMat.size do
    let M := tl.mats.getD (tl.pxMat.getD i 0) {}
    let (got, F', T') ← t2AddP F T ("PX" ++ toString i) M.m M.k M.wp (aTX.getD i 0) false
    if some got != tl.ix.TX[i]? then throw "internal-t2f-map"
    F := F'
    T := T'
  -- virtual rows: one for each piece, one for the reads, one for the ties
  let (gotZ, FZ, TZ) ← t2AddN F T "ZZ" tl.tau (2 * tl.mz) 1 1 false (2 * tl.zzBlocks + 2)
  if gotZ != tl.ix.ZZ then throw "internal-t2f-map"
  -- three virtual rows, one for each claim of linBits9
  let (gotB, FB, TB) ← t2AddN FZ TZ "BZ" 32 tl.bzColumns 1 1 false 3
  if gotB != tl.ix.BZ then throw "internal-t2f-map"
  F := FB
  T := TB
  for i in List.range tl.ft.size do
    let X := tl.ft.getD i {}
    let (got, F', T') ← t2AddP F T X.name X.m X.K X.wp X.a true
    if some got != tl.ix.FT[i]? then throw "internal-t2f-map"
    F := F'
    T := T'
  let nt := T.nt
  let plOwn := (Array.range tl.pxMat.size).map fun i =>
    { declared (tl.plOwn.getD i {}) (nt.getD (tl.ix.TX.getD i 0) {}) hb with
      rootIndex := some (tl.pkMat.size + i) }
  let plFor := (Array.range tl.ft.size).map fun i =>
    declared (tl.plFor.getD i {}) (nt.getD (tl.ix.FT.getD i 0) {}) hb
  let shp := (Array.range tl.NM).map fun mu => (nt.getD (tl.gtTree.getD mu 0) {}).p.getD {}
  let fits := (List.range tl.NM).all fun mu =>
    (shp.getD mu {}).m == (tl.mats.getD mu {}).m && (shp.getD mu {}).k == (tl.mats.getD mu {}).k
  if !fits then throw "internal-t2f-map"
  let tabLen3 := if (tl.ix.U.getD 2 none).isSome then nU.getD 2 0 else 0
  pure
    ({ tl with
        nUF := #[nU.getD 0 0, nU.getD 1 0, nU.getD 2 0], tabFirst := #[0, 0],
        tabLen := #[0, tabLen3], plOwn := plOwn, plFor := plFor, shp := shp }, F, T)

/-- The name under which the sub-proofs call addTreesF. -/
def addTrees (tl : HTailF2) (F : Fork) (T : Tail2) (nU aTX : Array Nat) (hb hbLine : Nat) :
    Except String (HTailF2 × Fork × Tail2) := tl.addTreesF F T nU aTX hb hbLine

/-! ### The messages -/

/-- True if two tables agree in every field. -/
def sameFun (a b : HFun) : Bool :=
  a.mat == b.mat && a.len == b.len && a.tree == b.tree && a.start == b.start && a.phi == b.phi

/-- True while the list of tables is open. A sub-proof adds a table only then. -/
def funOpen (tl : HTailF2) : Bool := !tl.funClosed

/-- The sub-proof closes its list of tables, before the matrix is drawn. A table (HFun,
OnBytes/Model/Look.lean) is a part of U1 or U3. It has one entry for each column of a matrix and
each segment of len rows of cells: that segment of the column, summed under the weights phi. The
table of a lookup call is another thing: the list of the values that a key may have (Call,
OnBytes/Model/Frame.lean). In names, fun means a table of the first kind (funs, closeFuns,
shape-functional). -/
def closeFuns (tl : HTailF2) (funs : Array HFun) : Option HTailF2 :=
  if tl.funClosed then none else some { tl with funClosed := true, funs := funs }

/-- True if the list of tables is still the list that was closed: closed, of the same length, and
every table equal in its five fields. objectsF tests it where the list is passed in, and each kind
of sub-proof tests it again after all claims are added. It guards against a slip of this program,
not against an adversary: only the verifier writes the list. -/
def funsHeld (tl : HTailF2) (funs : Array HFun) : Bool :=
  tl.funClosed && funs.size == tl.funs.size &&
    (List.range funs.size).all fun i => sameFun (funs.getD i {}) (tl.funs.getD i {})

/-- Draws the matrix (SubM.trits). The chain's reader makes each entry from two drawn bits: 0 if the
first bit is 0, else 1 or -1 by the second (Fmt.drawTrits). So an entry is 0 with probability 1/2 if
the bits are uniform. It is one vector for the whole sub-proof: matrix by matrix in the order of the
list, column by column, tau entries for each column. Fails, without a name, if the list of matrices
has not NM entries or has no column; the C++ routine has no such line. -/
def drawMatrixF (tl : HTailF2) : SubM HTailF2 := do
  let cfFirst := tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0]
  SubM.must (cfFirst.size == tl.NM + 1 && tl.foldColumns != 0)
  let cfF ← SubM.trits tl.foldColumns tl.tau
  pure { tl with cfF := cfF, cfFirst := cfFirst }

/-- True if the prover can no longer change array number tree of the sub-proof's list. S is the
chain's statement. The array is looked up in the layout, and the oracle message that holds it in the
request's shape. For an array of the present link, the message's moment must be one of the moments
received so far. For an array of an earlier link, the message's life must reach the present link;
such a message is sent again at the present link's start. In both cases the statement must record
the message, as it is named in the present link, as sampled. OnBytes/Iop/Ground.lean explains oracle
messages and their samples, OnBytes/Iop/Req.lean a message's life. -/
def arrayFixed (L : LinkCtx) (S : Statement) (tree : Nat) : Bool :=
  match L.arrayOf[tree]? with
  | none => false
  | some (born, name) =>
    match (L.check.rows.layout.link.getD born []).find? fun A => A.name == name with
    | none => false
    | some a =>
      match (L.check.frame.shape.link[born]?).bind fun l => l.messages[a.message]? with
      | none => false
      | some m =>
        decide (born ≤ L.link) &&
          (if born == L.link then decide (m.moment < L.moments)
           else decide (L.link ≤ born + m.life)) &&
          (((L.check.frame.whereIs born a.message).bind fun o => S.oracles[o]?).any (·.sampled))

/-- Tests the order on which the draw of the matrix relies. When the matrix is drawn, the prover
must have no choice left in anything that the matrix is applied to: the symbol arrays of all
matrices in the list, whichever link committed to them, and the sub-proof's vectors over E, which
hold the tables. A table's entries that could still be chosen after the draw could be shifted by a
vector in the matrix's kernel, and the test's equations would not see the shift. The moment of each
array is set by the program's own lists and by no file, so this test fails only if the program is at
fault. -/
def fixedBeforeTheMatrixF (tl : HTailF2) : LinkM Unit := do
  let L ← get
  let S ← LinkM.sub (liftM Blk.statement)
  LinkM.mustAs "internal-f-matrix-order"
    (L.check.link == L.link && decide (L.link < L.check.links) && tl.gtTree.size == tl.NM &&
      tl.gtTree.all (arrayFixed L S) &&
      (List.range 4).all fun n => (tl.ix.U.getD n none).all (arrayFixed L S))

/-- The messages of the smallness test. First the matrix is drawn. The draw must come after the
chain has sampled, and the prover has answered for, every oracle message that the test reads: the
symbol arrays, those of earlier sub-proofs too, and the vectors that the reads use. The reads'
weights must be fixed as well: the list of tables is closed, which is tested here. The error that
the design counts for this round, 2^-tau, rests on that order: the cells and the tables' entries are
then one object that is fixed before the draw. No theorem here says so. fixedBeforeTheMatrixF tests
the order of the samples. That order also follows from the order of the calling routine, from the
plan's order of rounds, from rootInH, which takes a commitment only if the arrays named are exactly
the layout's at that moment, and from Blk.close, which closes only the plan's next round.
Then the chain receives the commitment to ZZ and BZ, and the lookup on the digits runs. The test's
equations get no challenge of their own: each is weighted by a power of the sub-proof's batching
element (equationsF). -/
def transcriptF (tl : HTailF2) : LinkM HTailF2 := do
  LinkM.mustAs "internal-f-fun-open" tl.funClosed
  LinkM.mustAs "internal-t2f-map" (tl.shp.size == tl.NM)
  let slotA ← LinkM.sub SubM.slot
  tl.fixedBeforeTheMatrixF
  let tl ← LinkM.sub tl.drawMatrixF
  rootInH [tl.ix.ZZ, tl.ix.BZ]
  let g ← LinkM.sub (Forest.pad #[tl.z1.call, tl.z2.call] tl.f9.pub tl.lidb)
  let slotB ← LinkM.sub SubM.slot
  pure { tl with foldDrawn := tl.foldDrawn + 1, slotA := slotA, slotB := slotB, heard := some g }

/-- The name under which the sub-proofs call transcriptF. -/
def transcript (tl : HTailF2) : LinkM HTailF2 := tl.transcriptF

/-! ### The claims -/

/-- Sets what follows from the batching element theta: the weights of the combinations, theta^u both
in the reads and in the ties; the weights of each matrix's rows of symbols, (theta^stepF)^i; and the
indices of the equations (eqFirst). Returns none if theta is not drawn, if the plan has no claims,
or if a symbol array does not hold one row of symbols in each row and no further row (J = 1, Rd = 0,
R = Rr = mS = ceil(m / 3)). -/
def powersF (tl : HTailF2) (F : Fork) : Option HTailF2 :=
  let oneRowEach := (List.range tl.NM).all fun mu =>
    let s := tl.shp.getD mu {}
    s.J == 1 && s.Rd == 0 && s.R == s.mS && s.Rr == s.mS &&
      s.mS == ((tl.mats.getD mu {}).m + 2) / 3
  if !F.thetaDrawnF || F.planClaimsF == 0 || !oneRowEach then none
  else
    let vt := powers F.theta tl.tau
    let step := powE F.theta tl.stepF
    some { tl with
      vt := vt, vp := vt,
      eqFirst := tl.shp.foldl
        (fun a s => a.push (a.getD (a.size - 1) 0 + tl.stepF * 2 ^ clog2 s.mS)) #[0],
      rowX := tl.shp.map fun s => powers step s.mS,
      loX := tl.shp.map fun _ => #[oneE] }

/-- The factor that brings the claim that is added next, which gets theta^(its index) like every
claim, to theta^(planClaims + first). planClaims is the number of claims in the plan
(Fork.planClaimsF). Returns none if that many claims have been added (C++: internal-f-draws). -/
def leadF (F : Fork) (first : Nat) : Option E :=
  if F.nClaim ≥ F.planClaimsF then none
  else some (powE F.theta (F.planClaimsF - F.nClaim + first))

/-- The sum over the combinations u of v[u] times entry u of one column of the drawn matrix. base is
the index of the column's first entry in cf. -/
def foldColumn (cf : Array Int) (base tau : Nat) (v : Array E) : E :=
  ((v.extract 0 tau).foldl
    (fun (s : E × Nat) y =>
      let x := cf.getD (base + s.2) 0
      (if x == 0 then s.1 else if x < 0 then subE s.1 y else addE s.1 y, s.2 + 1))
    (zeroE, 0)).1

/-- Computes gamX[mu] and gamV[mu], the drawn matrix's columns of matrix mu summed under the weights
vp and vt. They are computed once for each matrix: a second call for the same matrix returns none
(C++: internal-f-draws), and each kind of sub-proof tests at its end that every matrix has had its
call (foldAllTakenF). -/
def foldSums (tl : HTailF2) (mu : Nat) : Option HTailF2 :=
  let taken := if tl.foldTakenF.size != tl.NM then Array.replicate tl.NM false else tl.foldTakenF
  if mu ≥ tl.NM || taken.getD mu true then none
  else
    let first := tl.cfFirst.getD mu 0
    let sums (v : Array E) : Array E :=
      (Array.range (tl.mats.getD mu {}).k).map fun c =>
        foldColumn tl.cfF ((first + c) * tl.tau) tl.tau v
    let underVp := sums tl.vp
    some { tl with
      foldTakenF := taken.set! mu true,
      gamX := tl.gamX.set! mu underVp,
      -- powersF gives the ties and the reads the same weights; then one sum serves both.
      gamV := tl.gamV.set! mu (if tl.vt == tl.vp then underVp else sums tl.vt) }

/-- True if every matrix has had its call of foldSums. -/
def foldAllTakenF (tl : HTailF2) : Bool :=
  tl.foldTakenF.size == tl.NM && tl.foldTakenF.all id

/-- Counts the places first, .., first + left - 1 of a lookup call by the trees that hold them. A
tree has 2^dT places. The call has 2^iota trees, of which base is the first. read[y] is the count of
tree y. Each step takes the places up to the end of one tree. Returns none if a place is after the
call's last tree. fuel bounds the number of steps. -/
def placesRead (dT iota base : Nat) : (fuel : Nat) → Array Nat → (first left : Nat) →
    Option (Array Nat)
  | 0, read, _, left => if left == 0 then some read else none
  | fuel + 1, read, first, left =>
    if left == 0 then some read
    else
      let b := first / 2 ^ dT
      let take := min left ((b + 1) * 2 ^ dT - first)
      if b ≥ 2 ^ iota then none
      else
        placesRead dT iota base fuel (read.modify (base + b) (· + take)) (first + take)
          (left - take)

/-- The claim on the lookup's key vectors, as one claim with runs on ZZ (Run2,
OnBytes/Model/Trees.lean). It says that the following is 0:
  sum_q e_q (alpha - q theta - sum over the pieces of eq(zp, off / 2^b) sum_r eq(zr, r)
     sum_(cc < Cp) eq(zc, cc) ZZ[r0 + r][c0 + cc])
  + sum_(y >= NT) eq(zy, y) (alpha - padding key of call 0)
  - (the hidden value at the end of the key side).
alpha, theta (the lookup's shift, not the batching element), e_q, zk, zy and the hidden value are
fields of Forest.Heard (OnBytes/Model/Look.lean); NT is a field of Forest.Shape; off, b, r0, c0 and
Cp are fields of Piece. The point of a call is zk = (zp | zr | zc). The factor eq(zr, r) is the
weight of the piece's virtual row on ZZ's rows (coefficientsF). Forest.join is the same claim on
forms. Here it is written out by hand, and Forest.joinAdded marks it as added in the sub-proof's
list of owed claims; the mark does not see what was added.

The claim reads nothing at a padding place. That is right only if the padding key of both calls,
before the shift, is 0, which is tested first. So the padding is described twice: by its number in
each tree (f9.pub, from which the lookup's public factor and the target of the counts are made) and
by the places at which this claim reads nothing. The places that the runs do read are counted by
tree where the runs are made, and Forest.paddingLaid refuses unless the two descriptions agree. -/
def linJoin9 (tl : HTailF2) : SubM HTailF2 := do
  let g ← SubM.get tl.heard
  let h := tl.f9
  mustAs "internal-f-padding-key" ([0, 1].all fun q => let c := (tl.zOf q).call; c.tauAt c.t0 == 0)
  let mut constant := zeroE
  let mut runs : Array Run2 := #[]
  let mut read := Forest.noPub h
  -- A piece's column weights are eqTab of its point zc. Pieces with equal points share them.
  let mut point : Array E := #[]
  let mut table : Array E := #[oneE]
  for q in [0, 1] do
    let c := tl.zOf q
    let zk := g.zk.getD q #[]
    let n := c.call.n
    constant := addE constant (mulE (g.e.getD q zeroE) (subE g.alpha (scaleNat g.theta q)))
    for p in c.pieces do
      mustAs "internal-eq-index"
        (decide (p.b ≤ n) && eqIndexOK (zk.extract 0 (n - p.b)) (p.off / 2 ^ p.b))
      let zc := zk.extract (n - p.b + p.a) (n - p.b + p.a + clog2 p.CP)
      if zc != point then
        point := zc
        table := eqTab zc
      runs := runs.push
        { tree := p.tree, row := p.row, first := p.c0,
          coef := subE zeroE
            (mulE (g.e.getD q zeroE) (eqOne (zk.extract 0 (n - p.b)) (p.off / 2 ^ p.b))),
          w := table, n := p.Cp }
      -- The places that this run reads, counted by tree. All other places count as padding.
      for rr in List.range p.Rp do
        let i := h.iota.getD q 0
        -- C++ refuses here under: internal-f-join-place
        read ← SubM.get
          (placesRead h.dT i (h.first.getD q 0) (2 ^ i + 1) read (p.off + rr * p.CP) p.Cp)
  let ey := eqTab g.zy
  for y in List.range (2 ^ h.rK - h.NT) do
    constant := addE constant (mulE (ey.getD (h.NT + y) zeroE) (subE g.alpha (g.padKey 0)))
  mustAs "internal-f-join-place" (read.all fun x => decide (x ≤ 2 ^ h.dT))
  Forest.paddingLaid g (read.map fun x => 2 ^ h.dT - x)
  let number ← SubM.claims
  t2Lin (Aff.ofConst constant - g.cEnd) runs
  Forest.joinAdded g
  pure { tl with joinObj9 := some number }

/-- The three claims that read the planes of the lookup's counts, on BZ. Plane j of the counts holds
bit j of each count. Forest.planeLins adds the same three claims from forms, for another arrangement
of the planes in a matrix. Here they are written out by hand, and Forest.planesAdded marks them as
added. The docstring of Forest.pad in OnBytes/Model/Look.lean explains the lookup's parts. Bit X =
(t | c | j) of the planes, with t the row of the call's table, c the call and j the plane, is in row
X / KB and column X mod KB of BZ, where KB is bzColumns. So the index of a row of BZ is the first
five bits of t. BZ has three virtual rows, one for each claim. Row 0: the claim of the sumcheck over
the table side's leaves, in which the planes' value at the first point, zb0, has the public factor
eps (alpha - 1 - the lookup's table at its point). Row 1: the planes' value at the second point,
zb1, equals the value that the bits' sumcheck ended with. Row 2: the counts sum to the number of
keys that are not padding. -/
def linBits9 (tl : HTailF2) : SubM HTailF2 := do
  let g ← SubM.get tl.heard
  let h := tl.f9
  let KB := tl.bzColumns
  let runOn (row : Nat) (coef : E) (w : Array E) : Run2 :=
    { tree := tl.ix.BZ, row := row, first := 0, coef := coef, w := w, n := KB }
  let w0 := eqTab (g.zb0.extract 5 (5 + h.kT + h.cK))
  let w1 := eqTab (g.zb1.extract 5 (5 + h.kT + h.cK))
  let bitFactor := mulE g.leaves.eps g.leavesA
  let (leavesRow, _) ← pscRow g.leaves oneE
  t2Lin leavesRow #[runOn 0 bitFactor w0]
  t2Lin (Aff.slot g.sBit) #[runOn 1 (subE zeroE oneE) w1]
  let w := (Array.range KB).map fun u => ofNat (2 ^ (u % 32))
  t2Lin (Aff.ofConst (subE zeroE (ofNat (2 ^ h.v - h.padding)))) #[runOn 2 oneE w]
  Forest.planesAdded g
  pure { tl with bitFactor9 := bitFactor }

/-- Tests that the tables on vector number un (0: U1; 2: U3) tile the part of it that holds tables:
sorted by their first entries they follow each other without gap or overlap, from the part's first
entry to its last. Returns the number of their segments, or none. -/
def tablesTile (tl : HTailF2) (funs : Array HFun) (un : Nat) : Option Nat :=
  let iv := (funs.toList.filter fun Fn => Fn.tree == un).map fun Fn =>
    let M := tl.mats.getD Fn.mat {}
    (Fn.start, M.k * (M.m / Fn.len), M.m / Fn.len)
  let first := tl.tabFirst.getD (un / 2) 0
  let walked := (iv.mergeSort fun a b => decide (a.1 ≤ b.1)).foldl
    (fun (s : Option (Nat × Nat)) x =>
      s.bind fun (pos, segments) =>
        if x.2.1 != 0 && x.1 == pos then some (pos + x.2.1, segments + x.2.2) else none)
    (some (first, 0))
  walked.bind fun (pos, segments) =>
    if pos == first + tl.tabLen.getD (un / 2) 0 &&
        ((tl.ix.U.getD un none).isNone || decide (pos ≤ tl.nUF.getD un 0)) then
      some segments
    else none

/-- True if no two members of the list are equal. -/
def allDistinct : List Nat → Bool
  | [] => true
  | x :: t => !t.contains x && allDistinct t

/-- x times 2^10: the weight of a high digit from that of its low digit. -/
def highDigit (x : E) : E := scaleNat x (2 ^ t2D0)

/-- The constant -beta x. The digits hold a combination plus beta, and x is the sum of the weights
under which a claim reads combinations. -/
def lessBeta (x : E) : Aff := Aff.ofConst (subE zeroE (scaleNat x (2 ^ lbz)))

/-- Adds the tie of matrix mu. It is not the Tie of Look.lean, which is a part of the lookup. Let
wl be the left and wr the right weights of the tie (FormF.lean). The claim says
  sum_u vp[u] sum_i wl[i] (low digit + 2^10 high digit - beta)(i, u)
    = sum over the symbols (i', c) of rowX[i'] wr[c] symbol(i', c).
The weights vp[u] and rowX[i'] are the weights of the virtual rows on the rows of ZZ and of the
symbol array (coefficientsF). The whole claim is multiplied by the factor leadF. -/
def linTie (tl : HTailF2) (mu : Nat) : SubM Unit := do
  let s := tl.shp.getD mu {}
  -- C++ refuses here under: internal-sym-point, internal-f-draws, internal-f-zzcol
  let wl ← SubM.get (tieLeft s (tl.rowX.getD mu #[]) (tl.loX.getD mu #[]))
  let wr ← SubM.get (tieRight s (tl.loX.getD mu #[]) (tl.gamX.getD mu #[]))
  let lead ← SubM.ask fun F => leadF F (tl.eqFirst.getD mu 0)
  let c0 ← SubM.get (tl.zzCol mu 0 0)
  let c1 ← SubM.get (tl.zzCol mu 1 0)
  let ZZ := tl.ix.ZZ
  t2Lin (lessBeta (mulE lead (mulE (sumE tl.vp) (sumE wl))))
    #[{ tree := ZZ, row := tl.zzRowTies, first := c0, coef := lead, w := wl, n := s.m },
      { tree := ZZ, row := tl.zzRowTies, first := c1, coef := highDigit lead, w := wl, n := s.m },
      { tree := tl.gtTree.getD mu 0, row := 0, first := 0, coef := subE zeroE lead, w := wr,
        n := s.J * s.k }]

/-- The entries of U1 or U3 that the read of segment sg of the table Fn reads, for the columns c,
.., c + count - 1 of the table's matrix. The argument minus is -lead, the negative of the read's
factor (linRead). The entry of column c gets the coefficient minus * gc[c]. tU: the index of the
array that holds the vector; cols: the number of its columns, not 0. Entry x of the vector is entry
x mod cols of virtual row x / cols, as in uEnt (Look.lean). The entries are appended to ents. The
Bool stays true while no gc[c] is 0. Returns none if the table has no such entry (C++:
internal-f-table-index). The caller has tested that the rows' indices fit 32 bits. -/
def readEnts (tl : HTailF2) (Fn : HFun) (sg tU cols : Nat) (minus : E) (gc : Array E) :
    (count c : Nat) → Array Ent → Bool → Option (Array Ent × Bool)
  | 0, _, ents, noneIsZero => some (ents, noneIsZero)
  | count + 1, c, ents, noneIsZero =>
    match tl.tabAt Fn c sg with
    | none => none
    | some pos =>
      let g := gc.getD c zeroE
      tl.readEnts Fn sg tU cols minus gc count (c + 1)
        (ents.push { tree := tU, row := pos / cols, idx := pos % cols, coef := mulE minus g })
        (noneIsZero && !isZeroE g)

/-- Adds the read of segment sg of the table Fn. laid: the number of reads added before. sums: the
sum of Fn.phi times the sum of vt, which is the same for all segments of a table. Let M be the
table's matrix and i0 = sg Fn.len the segment's first row of cells. The claim says
  sum_u vt[u] sum_j Fn.phi[j] (low digit + 2^10 high digit - beta)(i0 + j, u)
    = sum over the columns c of gamV[c] (the vector's entry for column c, segment sg).
That entry is meant to hold sum_j Fn.phi[j] M[i0 + j][c]. No gamV[c] may be 0: the entry would have
no weight. As in linTie, the whole claim is multiplied by the factor leadF. -/
def linRead (tl : HTailF2) (Fn : HFun) (sg laid : Nat) (sums : E) : SubM Unit := do
  let mu := Fn.mat
  -- C++ refuses here under: internal-t2f-unit, internal-f-draws, internal-f-table-index,
  -- internal-f-zzcol
  let tU ← SubM.get (tl.ix.U.getD Fn.tree none)
  let lead ← SubM.ask fun F => leadF F (tl.eqFirst.getD tl.NM 0 + laid * tl.stepF)
  let cols ← SubM.ask fun F => some (((F.trees[tU]?).map (·.K)).getD 0)
  let k := (tl.mats.getD mu {}).k
  -- The entries' indices rise with the column, so the last column's row is the largest.
  mustAs "internal-L-row" (cols != 0 &&
    ((tl.tabAt Fn (k - 1) sg).all fun last => decide (last / cols < 2 ^ 32)))
  let (ents, noneIsZero) ← SubM.get
    (tl.readEnts Fn sg tU cols (subE zeroE lead) (tl.gamV.getD mu #[]) k 0
      (Array.emptyWithCapacity k) true)
  testAs "internal-f-table-read" noneIsZero
  let f := { lessBeta (mulE lead sums) with ents := ents }
  let c0 ← SubM.get (tl.zzCol mu 0 (sg * Fn.len))
  let c1 ← SubM.get (tl.zzCol mu 1 (sg * Fn.len))
  let ZZ := tl.ix.ZZ
  t2Lin f
    #[{ tree := ZZ, row := tl.zzRowReads, first := c0, coef := lead, w := Fn.phi, n := Fn.len },
      { tree := ZZ, row := tl.zzRowReads, first := c1, coef := highDigit lead, w := Fn.phi,
        n := Fn.len }]

/-- The loop of markRead, for the columns c, .., c + count - 1. t0: the first entry of the part that
holds tables; marks: the part's marks. -/
def markLoop (tl : HTailF2) (Fn : HFun) (sg t0 : Nat) : (count c : Nat) → Array Bool →
    Option (Array Bool)
  | 0, _, marks => some marks
  | count + 1, c, marks =>
    match tl.tabAt Fn c sg with
    | none => none
    | some pos =>
      if decide (t0 ≤ pos) && !marks.getD (pos - t0) true then
        tl.markLoop Fn sg t0 count (c + 1) (marks.set! (pos - t0) true)
      else none

/-- Marks the entries of U1 or U3 that the read of segment sg of the table Fn reads. rd holds a mark
for each entry of the part of U1, and of U3, that holds tables. Returns none if an entry is outside
its part or is marked already. -/
def markRead (tl : HTailF2) (Fn : HFun) (sg : Nat) (rd : Array (Array Bool)) :
    Option (Array (Array Bool)) :=
  let part := Fn.tree / 2
  -- The part's marks are taken out of rd while they are changed, so that they are changed in place.
  let marks := rd.getD part #[]
  let rest := rd.set! part #[]
  (tl.markLoop Fn sg (tl.tabFirst.getD part 0) (tl.mats.getD Fn.mat {}).k 0 marks).map
    fun marks => rest.set! part marks

/-- Computes, once the batching element is drawn, its powers (powersF) and the sums over the drawn
matrix's columns (foldSums), for all matrices. Where powersF returns none, the C++ refuses under
internal-f-draws or internal-sym-shape; where foldSums does, under internal-f-draws. -/
def weightsF (tl : HTailF2) : SubM HTailF2 := do
  let tl ← SubM.ask fun F => tl.powersF F
  SubM.get ((List.range tl.NM).foldlM (fun (x : HTailF2) mu => x.foldSums mu)
    { tl with gamX := Array.replicate tl.NM #[], gamV := Array.replicate tl.NM #[] })

/-- Adds the claims of the smallness test, in this order: the lookup's own claims; the claim on its
key vectors; the three claims on the planes; one tie for each matrix; the reads. The reads are added
matrix by matrix in the order of the list; for each matrix the tables on U1 first, then those on U3;
the segments of a table in rising order. Among its tests: funs is the list that was closed before
the matrix was drawn; every entry of a part that holds tables is read exactly once, with a weight
that is not 0; the tables tile the part; the numbers of claims are the expected ones. Only the
claims of the smallness test are counted as reads: what other claims of the sub-proof read of a
table is not seen here. -/
def objectsF (tl : HTailF2) (funs : Array HFun) : SubM HTailF2 := do
  mustAs "internal-f-fun-closed" (tl.funClosed && funs.size == tl.funs.size)
  mustAs "internal-f-fun-moved" (tl.funsHeld funs)
  -- No claim of the sub-proof's own part has put a weight on a slot of the smallness test.
  testAs "internal-f-tail-slot"
    (← SubM.ask fun F => some ((F.LS.extract tl.slotA tl.slotB).all isZeroE))
  let g ← SubM.get tl.heard
  let before ← SubM.claims
  Forest.objects g
  -- Forest.lins, written out a second time as a check: 31 claims of the lookup's tie, one for each
  -- level of the key side (v) and of the table side (d), one of the bits' sumcheck
  mustAs "internal-f-exist" ((← SubM.claims) - before == 31 + tl.f9.v + tl.f9.d + 1)
  let before ← SubM.claims
  let tl ← tl.linJoin9
  let tl ← tl.linBits9
  mustAs "internal-f-exist" ((← SubM.claims) - before == 4)
  let tl ← tl.weightsF
  let mut tieObj : Array Nat := #[]
  let mut tiesOn : Array Nat := Array.replicate (← SubM.ask fun F => some F.trees.size) 0
  for mu in List.range tl.NM do
    tieObj := tieObj.push (← SubM.claims)
    tl.linTie mu
    tiesOn := tiesOn.modify (tl.gtTree.getD mu 0) (· + 1)
  let mut rd : Array (Array Bool) := tl.tabLen.map fun n => Array.replicate n false
  let mut laid := 0
  for mu in List.range tl.NM do
    let M := tl.mats.getD mu {}
    for un in [0, 2] do
      for Fn in funs do
        if Fn.mat == mu && Fn.tree == un then
          mustAs "internal-t2f-unit" (tl.ix.U.getD un none).isSome
          mustAs "shape-functional" (Fn.len != 0 && M.m % Fn.len == 0 && Fn.phi.size == Fn.len)
          let sums := mulE (sumE Fn.phi) (sumE tl.vt)
          for sg in List.range (M.m / Fn.len) do
            -- C++ refuses here under: internal-f-table-read
            rd ← SubM.get (tl.markRead Fn sg rd)
            tl.linRead Fn sg laid sums
            laid := laid + 1
  mustAs "internal-t2f-functional"
    (funs.all fun Fn => decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2))
  mustAs "internal-f-table-read" (rd.all fun a => a.all id)
  -- C++ refuses here under: internal-t2f-table-outside, internal-t2f-tables-overlap,
  -- internal-f-tables-gap
  let segments1 ← SubM.get (tl.tablesTile funs 0)
  let segments3 ← SubM.get (tl.tablesTile funs 2)
  -- Counted from the claims: one tie on each symbol array and none on any other array, with arrays
  -- and claim indices all different; as many reads as the tables have segments.
  let kinds ← SubM.ask fun F => some (F.trees.map (·.kind))
  mustAs "internal-f-exist" ((List.range kinds.size).all fun t =>
    tiesOn.getD t 0 == (if kinds.getD t .table == .symbols then 1 else 0))
  mustAs "internal-f-exist" (tiesOn.foldl (· + ·) 0 == tl.NM && laid == segments1 + segments3)
  mustAs "internal-f-exist" (allDistinct tieObj.toList && allDistinct tl.gtTree.toList)
  let lsTail ← SubM.ask fun F => some (F.LS.extract tl.slotA tl.slotB)
  pure { tl with tieObj := tieObj, tiesOn := tiesOn, nX4Laid := laid, lsTail := lsTail }

/-! ### The weights on the rows, and tests on the weights -/

/-- The column weights of virtual row r of array t. -/
def weightsOf (F : Fork) (t r : Nat) : Array E := ((F.trees.getD t {}).rows.getD r {}).L

/-- Tests, after all claims are added, that in each virtual row of U1 to U3, ZZ, BZ and the symbol
arrays every column that the row is meant to read has a column weight that is not 0. A column that
no claim reads would be unconstrained. The weights on the rows are set later (coefficientsF). The
routine also tests that the slots of the smallness test still hold the weights that its own claims
left there. nU: the lengths of U1 to U3. They must be those that addTreesF was given; the C++
routine has no such test, and the failure has no name.

What a weight is made of. This paragraph is an argument by reading; no theorem states it. The test
reads weights, and no word of the proof. How far a weight can depend on what the prover has sent is
said next. No sub-proof has U1 or U2: the three plans ask shapeF for U3 alone. On ZZ, BZ and the
symbol arrays only the claims of this file put weights, and their factors are public or drawn; that
holds also for the tables' weights phi, which the sub-proof passes in. An entry of U3 also gets
weights from the sub-proof's other claims. In a layer sub-proof some of these have scalars that the
prover has sent as factors: the shown values (Fork, OnBytes/Model/Hide.lean) of the selector
(stackEndOf, OnBytes/Model/LayerPanels.lean). That does not let a prover make the whole weight 0.
Every entry of U3 has the weight of exactly one read. It is made of drawn values alone: one column
of the drawn matrix, under powers of the batching element whose exponents are planClaimsF, the
number of claims in the plan, or more. Every other claim that names the entry has a lower power
(kapTake), and its factors do not hold that element. The element is drawn after the sub-proof's last
message: t2Batch tests that the slots which its caller counts as taken are all the sub-proof's slots
and that all commitments have come, and its three callers receive no message of the sub-proof after
it; the link's closing, which doorH starts, comes after this test. So the weight is a polynomial in
the element that is fixed before the draw. It is not the zero polynomial unless the column is all 0,
which linRead refuses. A weight is therefore 0 through a slip in this program's claims or through a
challenge's value; no bound on how often is stated or proved here. Either way the test fails under a
name that begins with internal, and the run is not accepted.

What the test does not see: whether a claim other than a read names an entry of U3, since the read's
weight is there in any case. What this test alone covers: the whole weight of an entry of U3, "not
0" on the reads' row of ZZ and on the three rows of BZ, and the comparison of the slots.
tileSelfTestF tests "not 0" again on the pieces' rows and the ties' row of ZZ. On a symbol array it
compares each weight with -ka gam[c] (tieWeightsHeld), and its test on the ties' row shows that ka
is not 0; linRead refuses a gam[c] that is 0, for a matrix that has a table. -/
def selfTestF (tl : HTailF2) (nU : Array Nat) : SubM Unit := do
  let ok ← SubM.ask fun F =>
    let units := (List.range 3).all fun n =>
      match tl.ix.U.getD n none with
      | none => true
      | some t =>
        let Kw := (F.trees.getD t {}).K
        allBelow (nU.getD n 0) fun x =>
          !isZeroE ((weightsOf F t (x / Kw)).getD (x % Kw) zeroE)
    let nb := tl.zzBlocks
    let digits := (List.range nb).all fun b =>
      noneZero (weightsOf F tl.ix.ZZ b) 0 tl.mz &&
        noneZero (weightsOf F tl.ix.ZZ (nb + b)) tl.mz tl.mz
    let linked := noneZero (weightsOf F tl.ix.ZZ tl.zzRowReads) 0 (2 * tl.mz) &&
      noneZero (weightsOf F tl.ix.ZZ tl.zzRowTies) 0 (2 * tl.mz)
    let planes := (List.range 3).all fun r => noneZero (weightsOf F tl.ix.BZ r) 0 tl.bzColumns
    let symbols := (List.range tl.NM).all fun mu =>
      let s := tl.shp.getD mu {}
      noneZero (weightsOf F (tl.gtTree.getD mu 0) 0) 0 (s.J * s.k)
    some (units && digits && linked && planes && symbols,
      F.LS.extract tl.slotA tl.slotB == tl.lsTail)
  SubM.must (nU == tl.nUF)
  testAs "internal-t2f-untyped" ok.1
  mustAs "internal-f-tail-slot" (tl.lsTail.size == tl.slotB - tl.slotA)
  testAs "internal-f-tail-slot" ok.2

/-- The name under which the sub-proofs call selfTestF. -/
def selfTest (tl : HTailF2) (nU : Array Nat) : SubM Unit := tl.selfTestF nU

/-- Sets one of the product forms of HRow (OnBytes/Model/Hide.lean): the equality polynomial of the
point z on the rows from first on. -/
def formPoint (row : HRow) (z : Array E) (first : Nat) : HRow :=
  { row with rowForm := true, rowOnes := false, rowPoint := z, rowFirst := first }

/-- base, base^2, base^4, ..: count members. -/
def squares (base : E) (count : Nat) : Array E :=
  ((List.range count).foldl
    (fun (s : Array E × E) _ => (s.1.push s.2, mulE s.2 s.2)) (#[], base)).1

/-- Sets the product form base^r on row r. Bit t of r gives the factor base^(2^t) if it is 1, and 1
if it is 0. -/
def formPowers (row : HRow) (base : E) (rows : Nat) : HRow :=
  { row with
    rowForm := true, rowOnes := false, rowPoint := #[], rowFirst := 0,
    rowLo := Array.replicate (clog2 rows) oneE, rowHi := squares base (clog2 rows) }

/-- Sets the product form 1 on every row. -/
def formOnes (row : HRow) : HRow :=
  { row with rowForm := true, rowOnes := true, rowPoint := #[], rowFirst := 0 }

/-- Changes virtual row r of array t. -/
def onRow (F : Fork) (t r : Nat) (f : HRow → HRow) : Fork :=
  { F with trees := F.trees.modify t fun X => { X with rows := X.rows.modify r f } }

/-- Sets the weights of every virtual row on the rows of its array, written out and as a product
form (HRow, Hide.lean). The product form is what the chain takes; rowWeights (Trees.lean) compares
the two entry by entry. -/
def coefficientsF (tl : HTailF2) : SubM Unit := do
  let g ← SubM.get tl.heard
  modify fun F => Id.run do
    let theta := F.theta
    let mut F := F
    for n in List.range 4 do
      if let some t := tl.ix.U.getD n none then
        if (F.trees.getD t {}).kind == .table then
          F := onRow F t 0 fun row => formOnes { row with coef := #[oneE] }
    for q in [0, 1] do
      let c := tl.zOf q
      let zk := g.zk.getD q #[]
      for p in c.pieces do
        let zr := zk.extract (c.call.n - p.b) (c.call.n - p.b + p.a)
        let e := eqTab zr
        let R := (F.trees.getD p.tree {}).R
        let w := (Array.range R).map fun r =>
          if p.r0 ≤ r ∧ r < p.r0 + p.Rp then e.getD (r - p.r0) zeroE else zeroE
        F := onRow F p.tree p.row fun row => formPoint { row with coef := w } zr p.r0
    F := onRow F tl.ix.ZZ tl.zzRowReads fun row =>
      formPowers { row with coef := tl.vt } theta tl.tau
    F := onRow F tl.ix.ZZ tl.zzRowTies fun row =>
      formPowers { row with coef := tl.vp } theta tl.tau
    for e in [0, 1] do
      let z := (g.zb e).extract 0 5
      F := onRow F tl.ix.BZ e fun row => formPoint { row with coef := eqTab z } z 0
    F := onRow F tl.ix.BZ 2 fun row => formOnes { row with coef := Array.replicate 32 oneE }
    for mu in List.range tl.NM do
      F := onRow F (tl.gtTree.getD mu 0) 0 fun row =>
        formPowers { row with coef := tl.rowX.getD mu #[] } (powE theta tl.stepF)
          (tl.shp.getD mu {}).mS
    return F

/-- The name under which the sub-proofs call coefficientsF. -/
def coefficients (tl : HTailF2) : SubM Unit := tl.coefficientsF

/-! ### Tests on the weights by a second computation -/

/-- True if x is a power of two. -/
def isPow2 (x : Nat) : Bool := x != 0 && 2 ^ Nat.log2 x == x

/-- One piece of a lookup call, as the second computation expects it. -/
structure Want where
  /-- 0: the call of the low digits; 1: that of the high digits -/
  call : Nat := 0
  /-- the piece's index in its call -/
  i : Nat := 0
  /-- the virtual row of ZZ -/
  row : Nat := 0
  /-- the first row of ZZ -/
  r0 : Nat := 0
  /-- the number of rows -/
  Rp : Nat := 0
  /-- the first column of ZZ -/
  c0 : Nat := 0
  /-- the number of columns -/
  Cp : Nat := 0

/-- The number of blocks of ZZ's rows and the pieces of the two calls, computed again without t2BL
and piecesF. The first block has 2^floor(log2 tau) rows; the second, if there is one, has the
remaining rows. Returns none if rows remain and their number is not a power of two (C++:
internal-t2f-untiled). The second computation is not wholly independent: like t2BL it takes the
logarithm from Nat.log2, so a slip in Nat.log2 is not found. (The C++ goes two ways: a loop that
doubles in t2BL, the top bit of tau in tileSelfTestF.) -/
def wants (tl : HTailF2) : Option (Nat × List Want) :=
  let rows1 := 2 ^ Nat.log2 tl.tau
  let rows2 := tl.tau - rows1
  let nbW := if rows2 != 0 then 2 else 1
  if rows2 != 0 && !isPow2 rows2 then none
  else
    some (nbW, [0, 1].flatMap fun q =>
      { call := q, i := 0, row := q * nbW, r0 := 0, Rp := rows1, c0 := q * tl.mz, Cp := tl.mz } ::
        (if rows2 != 0 then
          [{ call := q, i := 1, row := q * nbW + 1, r0 := rows1, Rp := rows2, c0 := q * tl.mz,
             Cp := tl.mz }]
        else []))

/-- True if the lookup's public numbers are those that are written out here a second time. Both
calls have 2^n9 keys. -/
def forestHeld (tl : HTailF2) (g : Forest.Heard) : Bool :=
  let h := tl.f9
  let n9 := tl.z1.call.n
  let dW := min n9 tl.lidb
  let io := n9 - dW
  tl.z2.call.n == n9 && h.dT == dW && h.kT == 10 && h.NT == 2 ^ (io + 1) && h.rK == io + 1 &&
    h.iota == #[io, io] && h.first == #[0, 2 ^ io] && g.zy.size == io + 1 && g.zx.size == dW &&
    g.e.size == 2

/-- True if one piece of a call with 2^n keys is well placed. The last two conditions say that the
piece's 2^b places begin at a multiple of 2^b and end inside the call. -/
def pieceHeld (n : Nat) (p : Piece) : Bool :=
  p.Rp != 0 && p.Cp != 0 && decide (p.a ≤ 40) && 2 ^ p.a == p.Rp && p.r0 % p.Rp == 0 &&
    decide (p.Cp ≤ p.CP) && isPow2 p.CP && p.b == p.a + clog2 p.CP && decide (p.b ≤ n) &&
    p.off % 2 ^ p.b == 0 && decide (p.off + 2 ^ p.b ≤ 2 ^ n)

/-- True if call q is as expected: its name; a range table (fn = 0) of 2^10 rows for q = 0 and 2^8
for q = 1; counts of 32 bits (kappa = 5; Call.kappa is a number of the lookup, not a claim's
weight); the padding row 0; nbW pieces, each well placed (pieceHeld), whose ranges of places do not
overlap; n = max 10 (clog2 of the pieces' places), at most 44; a point of n coordinates; and iota,
which is n - lidb, or 0 if n is smaller. -/
def callHeld (tl : HTailF2) (g : Forest.Heard) (nbW q : Nat) : Bool :=
  let c := tl.zOf q
  let n := c.call.n
  let keys := c.pieces.foldl (fun s p => s + 2 ^ p.b) 0
  let a := c.pieces.getD 0 {}
  let b := c.pieces.getD 1 {}
  c.call.name == (if q == 0 then "R10z" else "R8d") && c.call.fn == 0 &&
    c.call.k == (if q == 0 then 10 else 8) && c.call.kappa == 5 && c.call.t0 == 0 &&
    c.pieces.size == nbW && decide (10 ≤ n) && decide (n ≤ 44) && (g.zk.getD q #[]).size == n &&
    c.pieces.all (pieceHeld n) &&
    (nbW != 2 || !(decide (a.off < b.off + 2 ^ b.b) && decide (b.off < a.off + 2 ^ a.b))) &&
    n == max 10 (clog2 keys) && c.call.iota == n - tl.lidb

/-- True if the rectangles of two expected pieces overlap. -/
def Want.meets (w x : Want) : Bool :=
  decide (w.r0 < x.r0 + x.Rp) && decide (x.r0 < w.r0 + w.Rp) && decide (w.c0 < x.c0 + x.Cp) &&
    decide (x.c0 < w.c0 + w.Cp)

/-- True if no two rectangles of the list overlap. -/
def noneMeet : List Want → Bool
  | [] => true
  | w :: t => t.all (fun x => !w.meets x) && noneMeet t

/-- True if the pieces of the two calls are the expected ones and tile ZZ: they are inside it, no
two overlap, and their areas add up to ZZ's. -/
def piecesTile (tl : HTailF2) (F : Fork) (W : List Want) : Bool :=
  let T := F.trees.getD tl.ix.ZZ {}
  T.name == "ZZ" && T.R == tl.tau && T.K == 2 * tl.mz && noneMeet W &&
    (W.foldl (fun s w => s + w.Rp * w.Cp) 0) == T.R * T.K &&
    W.all fun w =>
      let p := (tl.zOf w.call).pieces.getD w.i {}
      let row := T.rows.getD w.row {}
      p.tree == tl.ix.ZZ && p.row == w.row && p.r0 == w.r0 && p.Rp == w.Rp && p.c0 == w.c0 &&
        p.Cp == w.Cp && decide (w.r0 + w.Rp ≤ T.R) && decide (w.c0 + w.Cp ≤ T.K) &&
        row.coef.size == T.R && row.L.size == T.K

/-- The weight of call q's trees at the lookup's point, computed again, independently. -/
def callWeightAgain (g : Forest.Heard) (q : Nat) : E :=
  if q == 0 then subE oneE (g.zy.getD 0 zeroE) else g.zy.getD 0 zeroE

/-- True if the lookup's weights of the calls and the calls' points are those of the second
computation: both calls have the point (zy_1, .., zy_(rK - 1) | zx). -/
def pointsHeld (tl : HTailF2) (g : Forest.Heard) : Bool :=
  let n9 := tl.z1.call.n
  let io := n9 - min n9 tl.lidb
  [0, 1].all fun q =>
    g.e.getD q zeroE == callWeightAgain g q &&
      (List.range n9).all fun i =>
        (g.zk.getD q #[]).getD i zeroE ==
          (if i < io then g.zy.getD (1 + i) zeroE else g.zx.getD (i - io) zeroE)

/-- True if, on the rectangle of one expected piece, the weight of entry (r, cc) in the one equation
is -kappa e_q eq(zk, off + r CP + cc), where off + r CP + cc is the entry's place in the call, and
is not 0, and the row weights and the column weights of the piece's virtual row are 0 outside the
rectangle. kappa is the weight of the claim on the key vectors. The weight is a row weight times a
column weight, and so is the expected value. So it is enough to compare the first row and the first
column, in which no weight may be 0. -/
def pieceWeightsHeld (tl : HTailF2) (F : Fork) (g : Forest.Heard) (kappa : E) (w : Want) : Bool :=
  let p := (tl.zOf w.call).pieces.getD w.i {}
  let row := (F.trees.getD tl.ix.ZZ {}).rows.getD w.row {}
  let cv := row.coef
  let L := row.L
  let zk := g.zk.getD w.call #[]
  let ka := mulE kappa (callWeightAgain g w.call)
  let mk := subE zeroE ka
  let cv0 := cv.getD w.r0 zeroE
  let L0 := L.getD w.c0 zeroE
  !isZeroE ka && !isZeroE cv0 && !isZeroE L0 &&
    (EqRun.all zk p.off w.Cp fun cc e =>
      let v := mulE mk e
      !isZeroE v && mulE cv0 (L.getD (w.c0 + cc) zeroE) == v) &&
    ((List.range w.Rp).all fun r =>
      let v := mulE mk (eqPlainF zk (p.off + r * p.CP))
      !isZeroE v && mulE (cv.getD (w.r0 + r) zeroE) L0 == v) &&
    mulE (cv.getD (w.r0 + w.Rp - 1) zeroE) (L.getD (w.c0 + w.Cp - 1) zeroE) ==
      mulE mk (eqPlainF zk (p.off + (w.Rp - 1) * p.CP + (w.Cp - 1))) &&
    allFrom (fun r => isZeroE (cv.getD r zeroE)) w.r0 0 &&
    allFrom (fun r => isZeroE (cv.getD r zeroE)) (cv.size - (w.r0 + w.Rp)) (w.r0 + w.Rp) &&
    allFrom (fun cc => isZeroE (L.getD cc zeroE)) w.c0 0 &&
    allFrom (fun cc => isZeroE (L.getD cc zeroE)) (L.size - (w.c0 + w.Cp)) (w.c0 + w.Cp)

/-- Lexicographic order on the coordinates. It is used only to sort, so that equal elements become
neighbours. -/
def leE (a b : E) : Bool :=
  decide (a.c0 < b.c0) || (a.c0 == b.c0 && (decide (a.c1 < b.c1) ||
    (a.c1 == b.c1 && decide (a.c2 ≤ b.c2))))

/-- True if no two neighbours in the list are equal. -/
def neighboursDiffer : List E → Bool
  | a :: b :: t => a != b && neighboursDiffer (b :: t)
  | _ => true

/-- The powers theta^(np2 R) for R below count. powersF computes each power from the one before it;
here none is. -/
def powersAgain (theta : E) (np2 count : Nat) : Array E :=
  let low := (Array.range 128).map fun i => powE theta (np2 * i)
  let high := (Array.range ((count + 127) / 128)).map fun j => powE theta (np2 * 128 * j)
  (Array.range count).map fun R => mulE (high.getD (R / 128) zeroE) (low.getD (R % 128) zeroE)

/-- The loop of pow2Again. fuel bounds the number of doublings. -/
def doubledTo (x : Nat) : (fuel p : Nat) → Nat
  | 0, p => p
  | fuel + 1, p => if p < x then doubledTo x fuel (2 * p) else p

/-- The least power of two that is not below x, by doubling from 1, for x up to 2^64. For a larger x
the result is 2^64, which is too small; the first computation then gives another number and the
comparison fails. The second computation uses it where the first computes 2 ^ clog2 x. -/
def pow2Again (x : Nat) : Nat := doubledTo x 64 1

/-- The index of matrix mu's first equation, computed again from the list of matrices, with
pow2Again. For mu = NM: of the first read's first equation. -/
def firstAgain (tl : HTailF2) (mu : Nat) : Nat :=
  (List.range mu).foldl
    (fun s nu => s + pow2Again tl.tau * pow2Again (((tl.mats.getD nu {}).m + 2) / 3)) 0

/-- The sum over one column of the drawn matrix, written a second time. cf is the drawn matrix, base
the index of the column's first entry, xi the weights. The count entries from base + u on are taken
one at a time, and s is the sum so far. An entry 1 adds xi[u], an entry -1 takes it away, any other
entry adds nothing. The result equals foldColumn's where all entries are -1, 0 or 1, the only ones
that are drawn; foldColumn and the C++ go by an entry's sign. -/
def sumAgain (cf : Array Int) (base : Nat) (xi : Array E) : (count u : Nat) → E → E
  | 0, _, s => s
  | count + 1, u, s =>
    let x := cf.getD (base + u) 0
    sumAgain cf base xi count (u + 1)
      (if x == 1 then addE s (xi.getD u zeroE) else if x == -1 then subE s (xi.getD u zeroE) else s)

/-- True if the tie of matrix mu meets the public conditions: its symbol array holds one row of
symbols in each row, no further row and no further column (J = 1, R = Rr = mS, Rd = 0, K1 = Kc = k),
the tie's claim is one of the plan's, and all vectors have the expected lengths. Under these
conditions every row and every column of the array holds symbols, so tieWeightsHeld has no other
places to consider. tieLeft and tieRight (FormF.lean) are written for any J. -/
def tieShapeHeld (tl : HTailF2) (F : Fork) (mu : Nat) : Bool :=
  let s := tl.shp.getD mu {}
  let X := F.trees.getD (tl.gtTree.getD mu 0) {}
  let row := X.rows.getD 0 {}
  let mS2 := ((tl.mats.getD mu {}).m + 2) / 3
  X.kind == .symbols && X.rows.size == 1 && X.R == s.Rr && X.K == s.Kc &&
    decide (mu < tl.tieObj.size) && mS2 == s.mS && s.J == 1 && s.R == mS2 && s.Rr == mS2 &&
    s.Rd == 0 && s.k == (tl.mats.getD mu {}).k && s.K1 == s.k && s.Kc == s.k &&
    (tl.rowX.getD mu #[]).size == mS2 && (tl.loX.getD mu #[]).size == 1 &&
    decide (tl.tieObj.getD mu 0 < F.planClaimsF) && row.coef.size == s.Rr && row.L.size == s.k &&
    (tl.gamX.getD mu #[]).size == s.k && (tl.gamV.getD mu #[]).size == s.k

/-- True if the weights of the tie of matrix mu equal a second computation from the drawn matrix and
the batching element theta. The tie's whole factor is ka = theta^(planClaims + the index of the
matrix's first equation), whatever the claim's own index is; planClaims is Fork.planClaimsF. Row i
of symbols has the weight (theta^Np)^i, with Np = tau rounded up to a power of two (pow2Again).
These weights must not be 0 and must differ from each other. The C++ source gives the reason: if two
rows had one weight, a false tie could pass. Only the challenges decide whether that happens, and
the design's error term for the tie is meant to cover these events whether or not they are refused.
No theorem here says so. The low digit of row 3 i + l of cells has the weight ka (theta^Np)^i B^l in
the ties' row of ZZ, with B = 2^20, the radix of FormF.lean; the high digit has 2^10 times that.
Column c of the symbol array has the weight -ka gam[c]. gam[c] is summed a second time by sumAgain,
with the column's index counted afresh and under powers that powE computes. Besides the field's
operations, the two computations still share the constants radb and t2D0 and the function powE, so a
slip in one of these is not found. L5: the column weights of the ties' row of ZZ. -/
def tieWeightsHeld (tl : HTailF2) (F : Fork) (L5 : Array E) (mu : Nat) : Bool :=
  let s := tl.shp.getD mu {}
  let row := (F.trees.getD (tl.gtTree.getD mu 0) {}).rows.getD 0 {}
  let np2 := pow2Again tl.tau
  let ka := powE F.theta (F.planClaimsF + tl.firstAgain mu)
  let hi := powersAgain F.theta np2 s.mS
  let c0 := tl.off.getD mu 0
  let c1 := tl.mz + c0
  let before := (List.range mu).foldl (fun n nu => n + (tl.mats.getD nu {}).k) 0
  let xi2 := (Array.range tl.tau).map fun u => powE F.theta u
  (tl.loX.getD mu #[]).getD 0 zeroE == oneE &&
    (allBelow s.R fun R =>
      row.coef.getD R zeroE == hi.getD R zeroE && !isZeroE (row.coef.getD R zeroE)) &&
    neighboursDiffer (row.coef.toList.mergeSort leE) &&
    decide (s.m ≤ 3 * s.mS) &&
    (allBelow s.mS fun R =>
      -- B^l by repeated multiplication, where tieLeft takes radixPower l
      let x := mulE ka (hi.getD R zeroE)
      let xB := scaleE (fOfNat radb) x
      let xBB := scaleE (fOfNat radb) xB
      allFrom (fun i =>
        let v := if i % 3 == 0 then x else if i % 3 == 1 then xB else xBB
        !isZeroE v && L5.getD (c0 + i) zeroE == v &&
          L5.getD (c1 + i) zeroE == scaleNat v (2 ^ t2D0)) (min 3 (s.m - 3 * R)) (3 * R)) &&
    (allBelow s.k fun c =>
      let gam := sumAgain tl.cfF ((before + c) * tl.tau) xi2 tl.tau 0 zeroE
      (tl.gamX.getD mu #[]).getD c zeroE == gam && (tl.gamV.getD mu #[]).getD c zeroE == gam &&
        row.L.getD c zeroE == mulE (subE zeroE ka) gam)

/-- True if BZ meets the public conditions: 32 rows, bzColumns columns and three virtual rows, a
lookup of two calls, and weight vectors and points of the expected lengths. -/
def planesShapeHeld (tl : HTailF2) (F : Fork) (g : Forest.Heard) : Bool :=
  let B := F.trees.getD tl.ix.BZ {}
  let lKB := tl.f9.kT + tl.f9.cK
  B.rows.size == 3 && B.R == 32 && B.K == tl.bzColumns && tl.f9.NC == 2 && tl.f9.cK == 1 &&
    B.K == 2 ^ lKB &&
    (List.range 3).all (fun r =>
      (B.rows.getD r {}).coef.size == 32 && (B.rows.getD r {}).L.size == B.K) &&
    g.zb0.size == 5 + lKB && g.zb1.size == 5 + lKB

/-- True if the weights on BZ equal a second computation: the row weights of its three virtual rows,
and their column weights, each a claim's weight (t2fKappaByText) times the claim's factor times an
equality weight or a power of two. The factor of the first claim is not computed again: it is
bitFactor9, as linBits9 left it. jo: the index of the claim on the key vectors among the claims; the
three claims that read the planes follow it. -/
def planesWeightsHeld (tl : HTailF2) (F : Fork) (g : Forest.Heard) (jo : Nat) : Bool :=
  let B := F.trees.getD tl.ix.BZ {}
  let kp := t2fKappaByText F.theta (jo + 3)
  (B.rows.getD 2 {}).coef.all (· == oneE) &&
    ([0, 1].all fun e =>
      let row := B.rows.getD e {}
      let z := g.zb e
      let mk := mulE (t2fKappaByText F.theta (jo + 1 + e))
        (if e == 0 then tl.bitFactor9 else subE zeroE oneE)
      ((List.range 32).all fun r => row.coef.getD r zeroE == eqPlainF (z.extract 0 5) r) &&
        EqRun.all (z.extract 5 z.size) 0 B.K fun x e => row.L.getD x zeroE == mulE mk e) &&
    allBelow B.K fun x =>
      (B.rows.getD 2 {}).L.getD x zeroE == scaleNat kp (2 ^ (x % 32))

/-- True if the public numbers of the reads are fit for readWeightsAgain. L4: the column weights of
the reads' row of ZZ, one for each digit of each row of cells. Each table on one of the matrices, in
U1 or U3, has as many weights as a segment has rows, and its segments fill the matrix's rows of
cells. These tables have as many segments as objectsF has added reads (nX4Laid). The matrices' rows
of cells add up to mz. Any other table is passed over, as in the C++; objectsF has refused it
(internal-t2f-functional). -/
def readShapeHeld (tl : HTailF2) (L4 : Array E) : Bool :=
  let read := tl.funs.filter fun Fn => decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2)
  L4.size == 2 * tl.mz &&
    (read.all fun Fn =>
      let m := (tl.mats.getD Fn.mat {}).m
      m != 0 && Fn.len != 0 && m % Fn.len == 0 && Fn.phi.size == Fn.len) &&
    read.foldl (fun q Fn => q + (tl.mats.getD Fn.mat {}).m / Fn.len) 0 == tl.nX4Laid &&
    (List.range tl.NM).foldl (fun n mu => n + (tl.mats.getD mu {}).m) 0 == tl.mz

/-- The column weights of the reads' row of ZZ, computed a second time. Read q, in the order in
which objectsF adds the reads, stands for the equations with the indices firstR + q Np + u, for u
below tau. firstR is the first index after the ties' equations (firstAgain), and Np is tau rounded
up to a power of two (pow2Again). So the read's whole factor is kr =
theta^(planClaims + firstR + q Np), whatever its claim's own index is; planClaims is
Fork.planClaimsF. In the read's segment the low digit of row j of cells has the weight kr phi[j],
the high digit 2^10 times that. A column's weight is the sum over the tables on its matrix. The C++
source gives the purpose: if two reads stood under one power of theta, errors in two tables could
cancel. No theorem here says that they cannot. The matrices' first columns are counted afresh
(before), where the first computation takes off. Besides the field's operations, the two
computations share the lists of tables and of matrices, tau, theta, planClaims, t2D0 and powE, so a
slip in one of these is not found. The order of the reads is written out a second time, not derived
in another way. The C++ routine reads the list that objectsF was given, through a pointer
(funLaidF). Here the closed list tl.funs is read: objectsF has tested that the given list equals it
in all five fields (funsHeld). -/
def readWeightsAgain (tl : HTailF2) (F : Fork) : Array E := Id.run do
  let np2 := pow2Again tl.tau
  let firstR := tl.firstAgain tl.NM
  let byStep := powE F.theta np2
  let mut want := Array.replicate (2 * tl.mz) zeroE
  let mut q := 0
  let mut before := 0
  for mu in List.range tl.NM do
    let m := (tl.mats.getD mu {}).m
    for un in [0, 2] do
      for Fn in tl.funs do
        if Fn.mat == mu && Fn.tree == un then
          let mut kr := powE F.theta (F.planClaimsF + firstR + q * np2)
          for sg in List.range (m / Fn.len) do
            for j in List.range Fn.len do
              let v := mulE kr (Fn.phi.getD j zeroE)
              let x := before + sg * Fn.len + j
              want := want.modify x (addE · v)
              want := want.modify (tl.mz + x) (addE · (scaleNat v (2 ^ t2D0)))
            kr := mulE kr byStep
          q := q + m / Fn.len
    before := before + m
  pure want

/-- True if the column weights L4 of the reads' row of ZZ are those of the second computation. By
the C++ comment no value of theta makes this test fail: it compares two computations of one
polynomial in theta. -/
def readWeightsHeld (tl : HTailF2) (F : Fork) (L4 : Array E) : Bool :=
  let want := tl.readWeightsAgain F
  allBelow (2 * tl.mz) fun x => L4.getD x zeroE == want.getD x zeroE

/-- Tests the weights that the claims and coefficientsF have set against a second computation. The
pieces of the two lookup calls tile ZZ exactly: no two overlap, and their areas add up to ZZ's. The
weights of the ties and of the claims on the planes are compared entry by entry. Those of the claim
on the key vectors are compared on the first row, the first column and one corner of each piece;
pieceWeightsHeld says why that is enough. Both computations take mz, NM and the indices of the
arrays from shapeF, those of the ties also off, and the factor of the first claim on the planes from
linBits9, so a slip there is not found.

Of the reads, the row weights and the column weights of their row of ZZ are compared, and with the
column weights the power of theta of each read whose weights phi are not all 0 (readWeightsAgain).
What has no second computation: the reads' weights on U1 and U3, their constant terms, and that the
index at which another claim of the sub-proof reads a table is the index that the read uses. These
rest on the one computation in objectsF, on "not 0" at every place (selfTestF), and on the tiling of
the tables and the count of the reads at the end of objectsF. By the C++ comment a slip there would
refuse honest proofs, unless the prover's program had the same slip. Nothing here tests that.

Where joinObj9 or wants is none, the C++ refuses under internal-t2f-untiled. The C++ tests the
reads' weights before BZ's; here they come last, because BZ's tests stand in one statement with the
ties'. The C++ test that objectsF has left its list of tables (funLaidF) has no counterpart:
joinObj9, which objectsF alone sets, is unwrapped first. -/
def tileSelfTestF (tl : HTailF2) : SubM Unit := do
  let g ← SubM.get tl.heard
  let jo ← SubM.get tl.joinObj9
  let (nbW, W) ← SubM.get tl.wants
  let rowsZZ ← SubM.ask fun F => some (F.trees.getD tl.ix.ZZ {}).rows.size
  mustAs "internal-t2f-untiled"
    (rowsZZ == 2 * nbW + 2 && tl.forestHeld g && [0, 1].all (tl.callHeld g nbW))
  mustAs "internal-t2f-untiled" (← SubM.ask fun F => some (tl.piecesTile F W))
  testAs "internal-t2f-untiled" (tl.pointsHeld g)
  testAs "internal-t2f-untiled" (← SubM.ask fun F =>
    let kappa := t2fKappaByText F.theta jo
    some (W.all (tl.pieceWeightsHeld F g kappa)))
  -- C++ refuses here under: internal-f-tie-weights, internal-sym-rowvec, internal-sym-weight,
  -- internal-f-fold-array, internal-f-bz-weights, internal-t2f-untiled (BZ's virtual rows)
  mustAs "internal-f-tie-weights" (← SubM.ask fun F =>
    let T := F.trees.getD tl.ix.ZZ {}
    some ((T.rows.getD (2 * nbW) {}).coef.size == tl.tau &&
      (T.rows.getD (2 * nbW + 1) {}).coef.size == tl.tau &&
      (T.rows.getD (2 * nbW + 1) {}).L.size == 2 * tl.mz &&
      tl.gamX.size == tl.NM && tl.gamV.size == tl.NM &&
      (List.range tl.NM).all (tl.tieShapeHeld F) &&
      tl.shp.foldl (fun n s => n + s.m) 0 == tl.mz && tl.planesShapeHeld F g))
  -- C++ refuses here under the first five of these names
  testAs "internal-f-tie-weights" (← SubM.ask fun F =>
    let T := F.trees.getD tl.ix.ZZ {}
    let c4 := (T.rows.getD (2 * nbW) {}).coef
    let c5 := (T.rows.getD (2 * nbW + 1) {}).coef
    let L5 := (T.rows.getD (2 * nbW + 1) {}).L
    some (((List.range tl.tau).all fun u =>
        c4.getD u zeroE == powE F.theta u && c5.getD u zeroE == c4.getD u zeroE) &&
      (List.range tl.NM).all (tl.tieWeightsHeld F L5) && tl.planesWeightsHeld F g jo))
  let L4 ← SubM.ask fun F => some ((F.trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).L
  mustAs "internal-f-read-weights" (tl.readShapeHeld L4)
  testAs "internal-f-read-weights" (← SubM.ask fun F => some (tl.readWeightsHeld F L4))

/-- The name under which the sub-proofs call tileSelfTestF. -/
def rkSelfTest (tl : HTailF2) : SubM Unit := tl.tileSelfTestF

end HTailF2

end OnBytes.Model
