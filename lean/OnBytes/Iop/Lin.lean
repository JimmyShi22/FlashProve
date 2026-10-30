-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/Lin.lean: linear claims of many requests on one committed table, on the verifier's side.
C++ counterpart: blocks/iop/lin.h (the routines whose names end in _verify_on_shape, and what they
call); for the last section, blocks/iop/member.h.

Words. E is the extension field; (x) is the tensor product. Chain, oracle message, mask row, group
and book of trees: see OnBytes/Iop/Ground.lean. Sample, answer and pad: see OnBytes/Iop/Send.lean,
whose block is SEND. A seal is the digest that a chain's last round draws. A row of the table or of
M is a row of a matrix. A row named in brackets, such as (Eval), is an open row: a linear equation
with a public target on oracle messages, which the proximity test on their group tests. The number
of a message or group is its index in Statement. A chain's statement is another thing: the statement
items of its first hash call. docs/format/FORMAT.md calls this block "the test on the table".

What the block starts from and leaves: the header of the section The public shape. Messages, in
three parts, each on a hash chain of its own and told in its section's header: a request's first
part (W, row (Eval)), the shared part (G_u, Omega, row (Fold)), a request's second part (row (Dot)).

Main definitions: LinShape.ok, linOk, LinClaim, linEvalRow, linFoldRow, linDotRow, linFirstVerify,
linSharedVerify, linSharedTestsVerify, linAdopt, linSecondVerify, linSecondTestsVerify,
memberWeightsOnRows, memberFirstVerify.

What this file does not do.
 - It tests no equation of its own. Every claim becomes a row, and the proximity tests test the
   rows. (When a row is added, Blk.addRow tests that it has the coefficient 0 on every pad.)
 - The caller must connect the three chains, which is not tested here: see the section Second part.
 - The C++ programs compare three things with those for which the plan's error bounds were computed:
   the table, whether the test on it is its one-time test or a later one, and the number of requests
   that can share the point. Here the plan is an input, and these comparisons are not made.
 - No theorem is stated here.
-/
import OnBytes.Chain.Draws
import OnBytes.Iop.Foldeq
import OnBytes.Iop.Split
import OnBytes.Iop.Prox
import OnBytes.Iop.Batt

namespace OnBytes

open Params (LinShape IoppStage)

/-! ## The public shape

What the block starts from. The table (OnBytes/Iop/Foldeq.lean) has 2^v rows and holds a matrix M
with matrixRows rows and 2^(kLo + v) columns: the entry (y, j + 2^kLo r) of M is at place
j + 2^kLo y of row r of the table. Each request of a batch has one claim, with public g (weights on
the rows of M), psi (a point on its columns) and target:
    < g (x) eq(psi, .), M >  +  (mask entries of the request's own oracle messages)  =  target.
What it leaves. No claim: the block ends in proximity tests. -/

namespace Params.LinShape

/-- The number of bits that index the rows of the matrix. -/
def kRow (S : LinShape) : Nat := ceilLog2 S.matrixRows

/-- G_u and Omega differ in code, so the row (Fold) is split. -/
def sharedSplitNeeded (S : LinShape) : Bool := S.fold.u.code != S.omega.code

/-- W and Omega differ in code, so the row (Dot) is split. -/
def ownSplitNeeded (S : LinShape) : Bool := S.w.code != S.omega.code

/-- A split's message: sampled, of mask rows only, under its groups' mask code. -/
def splitMessageOk (o : OracleShape) (maskCode : Nat) : Bool :=
  o.mainRows == 0 && o.maskRows != 0 && decide (1 ≤ o.answers) && o.maskCode == maskCode

/-- Omega or W: main rows over E, sampled. -/
def vectorMessageOk (o : OracleShape) : Bool :=
  shapeFaultless o && o.mainRows != 0 && o.mainDeg == 3 && decide (1 ≤ o.answers)

/-- The conditions on the shape by itself. -/
def ok (S : LinShape) : Bool :=
  S.fold.ok &&
  decide (1 ≤ S.matrixRows) && decide (S.kLo ≤ 30) && decide (S.kRow ≤ 30) &&
  decide (S.kCol ≤ 60) &&
  decide (S.matrixRows * 2 ^ S.kLo ≤ S.fold.index.plain) &&
  vectorMessageOk S.omega && vectorMessageOk S.w &&
  (S.fold.u.maskRows == 0 || S.fold.u.maskCode == S.sharedMaskCode) &&
  (S.w.maskRows == 0 || S.w.maskCode == S.ownMaskCode) &&
  -- Omega joins groups with different mask codes, so it must not have mask rows
  S.omega.maskRows == 0 &&
  -- oracle messages that are opened at different lists of positions share no leaf
  (!S.sharedSplitNeeded || S.omegaLeafClass != S.sharedSplitLeafClass) &&
  (!S.ownSplitNeeded || S.wLeafClass != S.ownSplitLeafClass) &&
  (!S.sharedSplitNeeded || splitMessageOk S.sharedSplit S.sharedMaskCode) &&
  (!S.ownSplitNeeded || splitMessageOk S.ownSplit S.ownMaskCode)

end Params.LinShape

/-- The conditions on the shape with the codes that it names. The first part and the shared part
ask this at their start. -/
def linOk (codes : Codes) (S : LinShape) : Bool :=
  S.ok && foldeqOk codes S.fold &&
  decide (S.omega.code < codes.base.size) && decide (S.w.code < codes.base.size) &&
  decide (S.sharedMaskCode < codes.mask.size) && decide (S.ownMaskCode < codes.mask.size) &&
  decide (S.matrixRows ≤ vectorRoom codes S.omega S.omegaRowsHigh) &&
  decide (2 ^ S.kCol ≤ vectorRoom codes S.w S.wRowsHigh)

/-- The notice of the fresh mask message of a proximity test's first fold, for a mask that is sent
ahead. leafClass: that of the oracle message with which it goes out: both are opened at one list of
positions, the same for both, so they share a tree. Nothing for a test without stages. -/
def linMaskNotice (test : List IoppStage) (leafClass : Nat) : Option OracleNotice :=
  test.head?.map fun s => foldMaskNotice { ioppFoldShape s {} with maskLeafClass := leafClass }

/-- What the prover's message with W holds, in order. Nothing if a mask is due and testOwn is []. -/
def linMessageW (S : LinShape) : Option (Array OracleNotice) := do
  let a : Array OracleNotice := #[⟨S.w, S.wLeafClass⟩]
  let b := if S.ownSplitNeeded then a.push ⟨S.ownSplit, S.ownSplitLeafClass⟩ else a
  if S.masksAhead then pure (b.push (← linMaskNotice S.testOwn S.wLeafClass)) else pure b

/-- What the prover's message with G_u holds beside G_u: the fresh mask of the first fold of the
test on G_u's group, if masks are sent ahead. -/
def linWithU (S : LinShape) : Option (Array OracleNotice) := do
  if S.masksAhead then pure #[← linMaskNotice S.testU S.fold.leafClass] else pure #[]

/-- What the prover's message with Omega holds, in order. -/
def linMessageOmega (S : LinShape) : Array OracleNotice :=
  let a : Array OracleNotice := #[⟨S.omega, S.omegaLeafClass⟩]
  if S.sharedSplitNeeded then a.push ⟨S.sharedSplit, S.sharedSplitLeafClass⟩ else a

/-- One request's claim:
< g (x) eq(psi, .), M > + sum of coeff * (mask entry) = target.
Not tested here, and the caller's duty: every field, the target and the row weights too, follows
from what the request's first chain has absorbed before its seal. -/
structure LinClaim where
  /-- the row weights are the sum of these; each has kRow variables; entries from matrixRows on do
  not count -/
  g : List Tensor := []
  /-- kCol coordinates -/
  psi : List E := []
  /-- entries of mask rows of the request's own oracle messages -/
  masks : Array Single := #[]
  /-- the target -/
  target : E := zeroE
  deriving Inhabited

/-! ## The rows

(Fold) and (Dot) sum over the rows of M only, those below matrixRows. A row's number has kRow bits,
and a form that ran on over all 2^kRow indices would read entries that mean nothing. -/

/-- Row (Eval): the claim on W. -/
def linEvalRow (S : LinShape) (claim : LinClaim) (w : Nat) (wLay : VectorLay) : Option Row := do
  guard (claim.psi.length == S.kCol)
  pure (addLaid { units := claim.masks, target := claim.target } w wLay [Tensor.eq claim.psi])

/-- Row (Fold): Omega against the folded row. psi: the shared point. -/
def linFoldRow (S : LinShape) (psi zeta : List E) (u : FoldedRow) (omega : Nat)
    (omegaLay : VectorLay) : Option Row := do
  guard (psi.length == S.kCol && zeta.length == S.kRow)
  let onOmega ← tensorBelow (Tensor.eq zeta) 0 S.kRow S.matrixRows
  let onU ← tensorBelow (Tensor.eq (psi.take S.kLo ++ zeta) (negE oneE)) S.kLo S.kRow S.matrixRows
  pure (u.addAll (addLaid {} omega omegaLay onOmega) onU)

/-- Row (Dot): the row weights on Omega against W at the shared point psi. -/
def linDotRow (S : LinShape) (weights : List Tensor) (psi : List E) (omega : Nat)
    (omegaLay : VectorLay) (w : Nat) (wLay : VectorLay) : Option Row := do
  guard (psi.length == S.kCol && weights.all (·.vars == S.kRow))
  let cut ← weights.mapM fun g => tensorBelow g 0 S.kRow S.matrixRows
  pure (addLaid (addLaid {} omega omegaLay cut.flatten) w wLay [Tensor.eq psi (negE oneE)])

/-! ## First part: a request by itself

Each request: SEND of W = g^T M, one entry of E for each column.
Row (Eval): W at psi, plus the masks, is the target.
If W and Omega differ in code, the second part's row (Dot) reads two groups and is split
(OnBytes/Iop/Split.lean), with a message of mask rows only that is sent with W. -/

/-- What the first part passes to the second. -/
structure LinFirst where
  /-- the number of W -/
  w : Nat := noId
  /-- the number of the split's mask message, if there is one -/
  split : Nat := noId
  /-- the group of W, the oracle messages of the claim's masks and the split's mask message -/
  own : Nat := noId
  /-- the mask of the first fold of the test on that group, if it went out with W -/
  mask : Option Nat := none
  /-- the claim -/
  claim : LinClaim := {}
  deriving Inhabited

/-- How W is laid out in its oracle message. -/
def linLayW (codes : Codes) (S : LinShape) : VectorLay := vectorLay codes S.w S.wRowsHigh

/-- How Omega is laid out in its oracle message. -/
def linLayOmega (codes : Codes) (S : LinShape) : VectorLay :=
  vectorLay codes S.omega S.omegaRowsHigh

/-- The request's own group and the row (Eval). ids: the oracle messages of W's prover message. -/
def linFirstRows (S : LinShape) (claim : LinClaim) (ids : Array Nat) : Blk LinFirst := do
  let w ← Blk.get ids[0]?
  let own ← Blk.newGroup S.w.code S.ownMaskCode
  for o in listOfT (claim.masks.toList.map (·.oracle)) do
    Blk.join own o
  Blk.join own w
  let split ← if S.ownSplitNeeded then Blk.get ids[1]? else pure noId
  if S.ownSplitNeeded then Blk.join own split
  let mask ← if S.masksAhead then (do pure (some (← Blk.get ids.back?))) else pure none
  let st ← Blk.statement
  Blk.addRowsOnView own fun _ => (linEvalRow S claim w (linLayW st.codes S)).map ([·])
  pure { w := w, split := split, own := own, mask := mask, claim := claim }

/-- The first part. After it the caller may add rows of its own to the group; then it seals the
chain. -/
def linFirstVerify (S : LinShape) (claim : LinClaim) : Blk LinFirst := do
  let st ← Blk.statement
  Blk.must (linOk st.codes S)
  let ids ← sendVerify (← Blk.get (linMessageW S))
  let out ← linFirstRows S claim ids
  let lay := linLayW st.codes S
  Blk.note "LIN: (Eval)'s target" claim.target
  Blk.noteBy "LIN: (Eval) on W<1>" fun _ =>
    ((linEvalRow S claim out.w lay).map (·.coefficient out.w .main (lay.index 1))).getD zeroE
  pure out

/-! ## Shared part: once for a batch. No claim is among the parameters.

The verifier draws the shared point (psiLo, gamma), kLo + v elements.
The table is folded at gamma (Foldeq.lean): SEND of G_u, the oracle message that holds the folded
row; then the prover opens columns of the table. SEND of Omega = M eq(shared point, .), one entry
for each row of M. The verifier draws zeta, a point on the rows of M. Row (Fold): Omega at zeta
is what the folded row gives. Then a proximity test on the group of G_u and, if Omega has a group
of its own, one on that group.
If G_u and Omega differ in code, (Fold) reads two groups and is split (OnBytes/Iop/Split.lean), with
a message of mask rows only that is sent with Omega. -/

/-- What the shared part returns. -/
structure LinShared where
  /-- the shared point: kCol coordinates -/
  psi : List E := []
  /-- the point on the rows of the matrix -/
  zeta : List E := []
  /-- where the folded row is -/
  u : FoldedRow := {}
  /-- the number of Omega -/
  omega : Nat := noId
  /-- the number of the split's mask message, if there is one -/
  split : Nat := noId
  /-- the group of G_u -/
  groupU : Nat := noId
  /-- the group of Omega; the same group if G_u and Omega have one code -/
  groupOmega : Nat := noId
  /-- the mask of the first fold of the test on G_u's group, if it went out with G_u -/
  mask : Option Nat := none
  deriving Inhabited

/-- True if the oracle message o has a tree to itself. Omega's leaves are opened by the shared test
and by every request's own test, so no other oracle message may share them. -/
def linAloneInItsTree (book : TreeBook) (o : Nat) : Bool :=
  match (book.place[o]?).bind fun p => book.trees[p.1]? with
  | some t => t.parts.size == 1
  | none => false

/-- The shared part up to the row (Fold). Not tested here, and the caller's duty: the chain's
statement holds the table's root, its record and the root of the binding tree. -/
def linSharedVerify (S : LinShape) (key : TableKey) : Blk LinShared := do
  let st ← Blk.statement
  Blk.must (linOk st.codes S)
  let psi ← drawPoint "LIN point" S.kCol
  let groupU ← Blk.newGroup S.fold.u.code S.sharedMaskCode
  let groupOmega ←
    if S.sharedSplitNeeded then Blk.newGroup S.omega.code S.sharedMaskCode else pure groupU
  let (u, others) ← foldeqVerify key S.fold (psi.drop S.kLo) groupU (← Blk.get (linWithU S))
  let mask ← if S.masksAhead then (do pure (some (← Blk.get others[0]?))) else pure none
  let ids ← sendVerify (linMessageOmega S)
  let omega ← Blk.get ids[0]?
  Blk.must (linAloneInItsTree (← Blk.theBook) omega)
  Blk.join groupOmega omega
  let split ← if S.sharedSplitNeeded then Blk.get ids[1]? else pure noId
  if S.sharedSplitNeeded then
    Blk.join groupOmega split
    Blk.join groupU split
  let zeta ← drawPoint "LIN zeta" S.kRow
  let lay := linLayOmega st.codes S
  let row ← Blk.getOnView {} fun _ => linFoldRow S psi zeta u omega lay
  Blk.noteBy "LIN: (Fold) on Omega<0>" fun _ => row.coefficient omega .main (lay.index 0)
  Blk.noteBy "LIN: (Fold) on G_u<1>" fun _ => row.coefficient u.oracle .main (u.lay.index 1)
  if S.sharedSplitNeeded then splitVerify row groupOmega groupU split
  else Blk.addRow groupU row
  pure { psi := psi, zeta := zeta, u := u, omega := omega, split := split, groupU := groupU,
         groupOmega := groupOmega, mask := mask }

/-- The shared part's proximity tests. After them the caller seals the chain. -/
def linSharedTestsVerify (S : LinShape) (x : LinShared) : Blk Unit := do
  ioppVerify x.groupU S.testU S.choice x.mask
  if S.sharedSplitNeeded then ioppVerify x.groupOmega S.testOmega S.choice

/-! ## Second part: a request by itself, on a chain whose statement holds two seals

Each request: row (Dot): < g, Omega > = W at the shared point. Then a proximity test on
W, the claim's mask messages and Omega; if (Dot) is split, Omega has its own group and test.

The caller must connect the three chains; this file does not test it. The seal of a request's
first chain, hashed with a salt, is a leaf of the binding tree, whose root is part of the shared
chain's statement: this is meant to put the shared point after every claim, every W and every
answer. Both seals are part of the second chain's statement. A request's first chain and the
shared chain hold the same codes, shape and table (lin.h, lin_second_verify, compares them; its
reason: under two shapes that differ in matrixRows a claim on another matrix than the committed
one could pass). The second part gets the first part's shape. Everything in a claim, target and
row weights too, must follow from what the request's first chain has absorbed before its seal.
The protocol's argument: a prover that may name one of them later could fit it to the challenges. -/

/-- Enters an oracle message that was sent and sampled on another chain of the session: same shape,
same tree, same sample rows. theirs: its number there; leafClass: its class of leaves; returns its
number here. It must have a tree to itself. fromBook: the other chain's book of trees in the form
for a later chain (TreeBook.goesOn), in which the tree has its root and start (Tree.src). The tree
keeps the number under which its leaves were hashed. The caller's duties: this chain's own trees are
numbered after it, and this chain's statement holds the other chain's seal, which ties the two. -/
def linAdopt (fromSt : Statement) (fromBook : TreeBook) (theirs leafClass : Nat) : Blk Nat := do
  Blk.must (linAloneInItsTree fromBook theirs)
  let place ← Blk.get fromBook.place[theirs]?
  let tree ← Blk.get fromBook.trees[place.1]?
  Blk.must (match tree.src with
    | .given _ _ => true
    | .own _ => false)
  let x ← Blk.get fromSt.oracles[theirs]?
  let ids ← Blk.adoptOracles #[⟨x.shape, leafClass⟩] #[(tree.number, tree.src)]
  let mine ← Blk.get ids[0]?
  Blk.sampledElsewhere mine fromSt theirs
  pure mine

/-- What the second part passes to its tests. -/
structure LinSecond where
  /-- the number that Omega has on this chain -/
  omega : Nat := noId
  /-- the request's own group, or a second one if W and Omega differ in code -/
  aroundOmega : Nat := noId
  deriving Inhabited

/-- The second part up to the row (Dot). It runs on a chain that continues the request's first
chain: the statement and the book of trees are those that the first chain has left. sharedSt,
sharedBook, shared: what the shared chain has left. Not tested here (lin.h, lin_second_verify, tests
both): that this chain's statement holds the seal of that shared chain, and that the shared chain
ran under the same codes, shape and table. linOk is not asked again: S must be the shape of the
first part. -/
def linSecondVerify (S : LinShape) (first : LinFirst) (sharedSt : Statement)
    (sharedBook : TreeBook) (shared : LinShared) : Blk LinSecond := do
  let omega ← linAdopt sharedSt sharedBook shared.omega S.omegaLeafClass
  let around ←
    if S.ownSplitNeeded then Blk.newGroup S.omega.code S.ownMaskCode else pure first.own
  Blk.join around omega
  if S.ownSplitNeeded then Blk.join around first.split
  let st ← Blk.statement
  let layOmega := linLayOmega st.codes S
  let layW := linLayW st.codes S
  let row ← Blk.getOnView {} fun _ =>
    linDotRow S first.claim.g shared.psi omega layOmega first.w layW
  Blk.noteBy "LIN: (Dot) on Omega<0>" fun _ => row.coefficient omega .main (layOmega.index 0)
  Blk.noteBy "LIN: (Dot) on W<1>" fun _ => row.coefficient first.w .main (layW.index 1)
  if S.ownSplitNeeded then splitVerify row around first.own first.split
  else Blk.addRow first.own row
  pure { omega := omega, aroundOmega := around }

/-- The second part's proximity tests. -/
def linSecondTestsVerify (S : LinShape) (first : LinFirst) (x : LinSecond) : Blk Unit := do
  ioppVerify first.own S.testOwn S.choice first.mask
  if S.ownSplitNeeded then ioppVerify x.aroundOmega S.testOwnOmega S.choice

/-! ## How a request arrives at its claim

The rows that a request's sub-proofs have left on the matrix are batched into one
(OnBytes/Iop/Batt.lean), and that one is the claim. -/

/-- A row on the matrix (TensorRow, OnBytes/Iop/Batt.lean) as a claim of the test on the table. -/
def memberClaim (row : TensorRow) : LinClaim where
  g := row.g
  psi := row.psi
  masks := (row.masks.map fun m => (⟨m.1.oracle, .mask, m.1.index, m.2⟩ : Single)).toArray
  target := row.target

/-- The logarithm of the largest aligned block of rows that begins at start and ends before row
stop; at most kRow. The unnamed arguments: fuel, which bounds the steps, and the d to count from. -/
def blockBits (kRow start stop : Nat) : Nat → Nat → Nat
  | 0, d => d
  | fuel + 1, d =>
    if d < kRow && start % 2 ^ (d + 1) == 0 && start + 2 ^ (d + 1) ≤ stop then
      blockBits kRow start stop fuel (d + 1)
    else d

/-- The blocks of the stretch from row start on, at most fuel of them. See stretchInTheCube. -/
def stretchBlocks (kRow firstRow : Nat) (values : Array E) : Nat → Nat → List Tensor
  | 0, _ => []
  | fuel + 1, start =>
    let stop := firstRow + values.size
    if stop ≤ start then []
    else
      let d := blockBits kRow start stop kRow 0
      let t : Tensor :=
        if d == 0 then
          ({ scalar := values.getD (start - firstRow) zeroE } : Tensor).insertChoice 0 kRow start
        else
          ((({} : Tensor).pushDense d).insertChoice d (kRow - d) (start / 2 ^ d)).setValues values
            (start - firstRow)
      t :: stretchBlocks kRow firstRow values fuel (start + 2 ^ d)

/-- Row weights that are written out on a stretch of rows: values[i] on row firstRow + i, and 0 on
every other row. The stretch is cut into aligned blocks of 2^d rows, at most two of each size. Each
block is one tensor: its written-out factor is a slice of values or, for a block of one row, its
scalar is the value. Nothing if kRow is 63 or more or the stretch is not inside the cube of 2^kRow
rows. The last test asks that the blocks cover the stretch; the bound on their number, 2 kRow + 2,
leaves room for two of each size. Callers use memberWeightsOnRows, which also tests that the stretch
is inside the matrix. -/
def stretchInTheCube (kRow firstRow : Nat) (values : Array E) : Option (List Tensor) :=
  if kRow < 63 && firstRow + values.size ≤ 2 ^ kRow then
    let blocks := stretchBlocks kRow firstRow values (2 * kRow + 2) firstRow
    if (blocks.map fun t => 2 ^ t.denseVars.length).sum == values.size then some blocks else none
  else none

/-- Row weights that are written out on a stretch of rows: values[i] on row firstRow + i, and 0 on
every other row (stretchInTheCube). Nothing unless firstRow + values.size is at most matrixRows.
Why: linDotRow counts no weight from row matrixRows on, and it drops a block that is wholly there
without a refusal. That suits product weights, which cover the whole cube. But a caller that counts
more rows than the shape does would lose its claims on the surplus rows unnoticed. -/
def memberWeightsOnRows (S : LinShape) (firstRow : Nat) (values : Array E) :
    Option (List Tensor) :=
  if firstRow + values.size ≤ S.matrixRows then stretchInTheCube S.kRow firstRow values else none

/-- A pending row, in which a sub-proof hands on its claims on the matrix:
< g (x) eq(psi, .), M > + beta c = v. c is an entry of the index-mask message: a sampled message of
mask rows only that went out in the request's first prover's message (in a proof: ReqShape.atStart)
and is in no link's group (link: a part of the computation with its own sub-proof, Iop/Req.lean). -/
def memberPendingRow (g : List Tensor) (psi : List E) (c : Slot) (beta v : E) : TensorRow :=
  { g := g, psi := psi, masks := [(c, beta)], target := v }

/-- Compares the pending rows and the index-mask message with the shape of the test on the table.
The message is sampled, has mask rows only, and has the mask code of the request's own group. Every
mask entry of every pending row is an entry of it: a row that named another message's entry would
draw that message into the request's own group. There is a pending row, and the matrix has more than
one column. Every row's point has kCol coordinates, and every weight has kRow variables. -/
def memberRowsFit (st : Statement) (S : LinShape) (indexMasks : Nat) (pending : List TensorRow) :
    Bool :=
  match st.oracles[indexMasks]? with
  | none => false
  | some x =>
    let o := x.shape
    o.mainRows == 0 && decide (0 < o.maskRows) && decide (0 < o.answers) &&
    o.maskCode == S.ownMaskCode &&
    !pending.isEmpty && decide (0 < S.kCol) &&
    pending.all fun r =>
      (r.masks.all fun m => m.1.oracle == indexMasks) && r.psi.length == S.kCol &&
        r.g.all (·.vars == S.kRow)

/-- A request's first part: several pending rows are batched into one (a single row is taken as it
is), and that one is the claim of the test's first part. indexMasks: the request's index-mask
message, from which the batching takes its mask entries. Two duties stay with the caller: the
pending rows that come in follow from what the first chain has absorbed before, and the LinFirst
that comes out goes to the second part unchanged. -/
def memberFirstVerify (S : LinShape) (indexMasks : Nat) (pending : List TensorRow) :
    Blk LinFirst := do
  Blk.must (memberRowsFit (← Blk.statement) S indexMasks pending)
  let one ←
    match pending with
    | [r] => pure r
    | _ => do
      let r ← Batt.verify S.kCol pending indexMasks
      Blk.note "BATT: target" r.target
      Blk.note "BATT: gamma_0" (r.psi.headD zeroE)
      Blk.note "BATT: the first weight's scalar" ((r.g.head?.map (·.scalar)).getD zeroE)
      Blk.note "BATT: coefficient of its first mask entry" ((r.masks.head?.map (·.2)).getD zeroE)
      Blk.note "BATT: coefficient of the last mask term" ((r.masks.getLast?.map (·.2)).getD zeroE)
      pure r
  Blk.note "member: the claim's target" one.target
  linFirstVerify S (memberClaim one)

end OnBytes
