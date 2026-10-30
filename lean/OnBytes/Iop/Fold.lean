-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/Fold.lean: single rows, and the block FOLD on the verifier's side.
C++ counterparts: blocks/iop/fold.h (the block), fold_rounds.h and fold_algebra.h (the arithmetic),
single_rows.h (single rows).

FOLD is a sumcheck that folds the rows of a group.
 From: a group of 2^k main rows under one code and 2^h mask rows under the mask code (h ≤ k; rows
       that nobody sent are zero), with one linear claim <c, m> + <d, mu> = target on their
       messages (GroupRow).
 To:   three single rows: the main rows folded at g_1 .. g_k, the mask rows folded at g_1 .. g_h,
       and a fresh mask folded at g_1 .. g_h; and the kept rows as they are; with one linear claim
       on their messages (SingleRows).
The polynomial, the messages and their rounds, the kept rows and the fresh mask are told at the
section "FOLD".

Main definitions: SingleRows, singleRowsOracles, singleRowsSymbols, singleRowsRead, foldLow,
foldMaskWeights, foldMaskForm, FoldShape, foldMaskNotice, foldStartVerify, foldEpsilon,
foldRoundsVerify, foldVerify.

Not tested here: any equation, or any other condition on a value received or drawn. It is left to
the steps after FOLD to test the new claim; that this suffices is the design's aim, and no theorem
here says so. Rules that the types do not enforce, among them: eps must come after the fresh mask
and after the sum of U, and a caller of the pieces (foldStartVerify, foldEpsilon, foldRoundsVerify)
must keep that order itself. Not done here: the C++ channel's comparison of the folded group's codes
and numbers of rows with those from which the plan's errors were computed (require_group). These are
told in full at "FOLD".

Words. An oracle is short for an oracle message (OnBytes/Iop/Ground.lean).
Not claimed here: soundness or hiding. No theorem is stated here.
-/
import OnBytes.Iop.Ground

namespace OnBytes

/-! ## The arithmetic of a fold -/

/-- Folds the first variable at g: entry i becomes v[2i] + g (v[2i+1] - v[2i]). On a table whose
row bits are the low bits of the index this halves the number of rows. -/
def foldLowOnce (v : Array E) (g : E) : Array E :=
  Array.ofFn (n := v.size / 2) fun i =>
    let a := v.getD (2 * i.val) zeroE
    maddE a g (subE (v.getD (2 * i.val + 1) zeroE) a)

/-- Folds one variable after the other at the elements of g. -/
def foldLow (v : Array E) (g : List E) : Array E := g.foldl foldLowOnce v

/-- The inner product of two vectors; entries that one of them lacks count as 0. -/
def inner (a b : Array E) : E :=
  (List.range (min a.size b.size)).foldl (fun s i =>
    maddE s (a.getD i zeroE) (b.getD i zeroE)) zeroE

/-- The number of columns that the table of the hiding polynomial's coefficients fills: the least
message length of the mask code. -/
def foldMaskColumns (k h : Nat) : Nat := 2 * k + 1 - h

/-- The public weights u(g), in the order of the columns of the fresh mask's table: the hiding
polynomial's value at g is the inner product of u(g) with the table folded at g_1 .. g_h.
The polynomial is U(X) = sum_l w_l(X_l) X_(l+1) .. X_k, with l = 1 .. k and w_l(Y) = w_(l,1) Y +
w_(l,2) Y^2, and for l = k also the constant w_(k,0): 2 k + 1 coefficients. The columns of the
table, where ones(l, b) is 1 if the bits l .. h of the row index b, counted from 1, are all 1, and 0
otherwise:
 - column 0: w_(h+1,1) (w_(k,0) if h = k) plus the sum over l = 1 .. h of w_(l,1) ones(l, b);
 - column l = 1 .. h: w_(l,2) ones(l, b);
 - then one column, equal in all rows, for each of (h+1,2), (h+2,1), (h+2,2), .., (k,1), (k,2), and
   last (k,0) if h < k;
 - then zeros.
C++: fold_mask_table and fold_mask_weights in blocks/iop/fold_algebra.h. -/
def foldMaskWeights (k h len : Nat) (g : Array E) : Array E :=
  let behind (l : Nat) : E :=
    (List.range (k - l)).foldl (fun s i => mulE s (g.getD (l + i) zeroE)) oneE
  let first := behind h :: (List.range h).map fun i => mulE (g.getD i zeroE) (behind h)
  let later := (List.range (k - h)).flatMap fun i =>
    let x := g.getD (h + i) zeroE
    let b := behind (h + 1 + i)
    (if i == 0 then [] else [mulE x b]) ++ [mulE (mulE x x) b]
  let u := first ++ later ++ (if h < k then [oneE] else [])
  (u ++ List.replicate (len - u.length) zeroE).toArray

/-- The coefficients on the folded old mask row, from d written out on 2^h rows:
eps g_(h+1) .. g_k d(g_1 .. g_h). -/
def foldMaskForm (h : Nat) (d : Array E) (eps : E) (g : List E) : Array E :=
  let s := (g.drop h).foldl mulE eps
  (foldLow d (g.take h)).map (mulE · s)

/-- The factor of the kept rows' coefficients in the new claim: eps (1 - g_1) .. (1 - g_k). -/
def foldKeptFactor (eps : E) (g : List E) : E := g.foldl (fun s x => mulE s (subE oneE x)) eps

/-- One round of the verifier's running claim. The message is the constant and the quadratic
coefficient. The linear one is the value for which q(0) + q(1) equals the claim. Returns q(g). -/
def foldClaimRound (claim c0 c2 g : E) : E :=
  let c1 := subE (subE claim (addE c0 c0)) c2
  addE (mulE (addE (mulE c2 g) c1) g) c0

/-! ## Single rows -/

/-- A complex of single rows, the statement between the steps of a proximity test. In this order:
the main row and the kept rows, read at a position x; the old mask row and the fresh mask row, read
at x modulo the mask code's length. Main row and mask rows are the folds, at challenges of the
verifier, of rows that were sent: the symbol of such a row at a position is the fold of the column
of their symbols there. With no challenge (k = h = 0) they are rows as they were sent. There is one
linear claim on the rows' messages: <c, main> + (forms on the kept members' main tables) + sum_j
<d[j], mask row j> = target. c stays a structured Form, because the main row may be long; the d[j]
are written out. -/
structure SingleRows where
  /-- the code of the main row -/
  code : Nat := noId
  /-- the code of the mask rows -/
  maskCode : Nat := noId
  /-- the oracle messages whose rows are folded, and where their rows are -/
  layout : GroupLayout := {}
  /-- layout.k challenges; main columns are folded at all, mask columns at the first layout.h -/
  gamma : List E := []
  /-- 0: only the main row; 1: with the old mask row; 2: with old and fresh mask row -/
  masks : Nat := 0
  /-- the oracle that holds the rows of the fresh mask, if masks = 2 -/
  fresh : Nat := noId
  /-- on the main row's message -/
  c : Form := {}
  /-- on the main tables of the kept members that the claim reads -/
  kept : Array KeptForm := #[]
  /-- written out, one for each mask row -/
  d : Array (Array E) := #[]
  target : E := zeroE
  /-- the number of main rows of all kept members of the layout -/
  keptRows : Nat := 0
  deriving Inhabited

/-- The number of rows of the complex. -/
def SingleRows.rows (s : SingleRows) : Nat := 1 + s.keptRows + s.masks

/-- The place of mask row j among the rows. -/
def SingleRows.maskRow (s : SingleRows) (j : Nat) : Nat := 1 + s.keptRows + j

/-- The oracle messages that must be opened to read the complex at a position. -/
def singleRowsOracles (s : SingleRows) : Array Nat :=
  if s.masks == 2 then s.layout.members.push s.fresh else s.layout.members

/-- Writes the symbols col into the table at the rows from first on. Nothing if they do not fit in
the table, or if there are symbols and first is nothing. -/
def putRows (table : Array E) (first : Option Nat) (col : Array E) : Option (Array E) :=
  if col.isEmpty then some table
  else
    match first with
    | none => none
    | some f =>
      if f + col.size ≤ table.size then
        some ((List.range col.size).foldl (fun t b =>
          t.setIfInBounds (f + b) (col.getD b zeroE)) table)
      else none

/-- The symbols of the rows from the opened columns of singleRowsOracles s, which are the first
entries of opened; further entries are not read (BASE adds its masking oracle's columns). Entry i *
s.rows + j of the result is the symbol of row j (main, kept rows by member and row, old mask, fresh
mask) at the i-th listed position (for s.masks ≤ 2, which is not tested here). Nothing if the
columns do not fit the layout. -/
def singleRowsSymbols (s : SingleRows) (opened : Array (Array Column)) (positions : Nat) :
    Option (Array E) := do
  let L := s.layout
  if s.gamma.length != L.k || L.k < L.h then none
  if L.kept.size != L.members.size || L.mainFirst.size != L.members.size ||
      L.maskFirst.size != L.members.size then none
  (List.range positions).foldlM (fun (y : Array E) i => do
    let start : Array E × Array E × Array E :=
      (Array.replicate (2 ^ L.k) zeroE, Array.replicate (2 ^ L.h) zeroE, #[])
    let t ← (List.range L.members.size).foldlM (fun (t : Array E × Array E × Array E) w => do
      let col ← (← opened[w]?)[i]?
      let mask ← putRows t.2.1 (L.maskFirst.getD w none) col.mask
      if L.kept.getD w false then pure (t.1, mask, t.2.2 ++ col.main)
      else pure (← putRows t.1 (L.mainFirst.getD w none) col.main, mask, t.2.2)) start
    if t.2.2.size != s.keptRows then none
    let y1 := (y.push ((foldLow t.1 s.gamma).getD 0 zeroE)) ++ t.2.2
    let low := s.gamma.take L.h
    let y2 := if 1 ≤ s.masks then y1.push ((foldLow t.2.1 low).getD 0 zeroE) else y1
    if s.masks == 2 then
      let fresh ← (← opened[L.members.size]?)[i]?
      if fresh.mask.size != 2 ^ L.h then none
      pure (y2.push ((foldLow fresh.mask low).getD 0 zeroE))
    else pure y2) #[]

/-- Reads the complex at a list of positions. -/
def singleRowsRead (s : SingleRows) (pos : Positions) : Blk (Array E) := do
  let opened ← Blk.readOpened (singleRowsOracles s) pos
  Blk.get (singleRowsSymbols s opened pos.all.size)

/-! ## FOLD

The polynomial. m and mu are the messages of the main rows and of the mask rows. The sumcheck runs
over the k row variables of
   H(X) = U(X) + eps ( <c(X), m(X)> + <d(X_1 .. X_h), mu(X_1 .. X_h)> X_(h+1) .. X_k ),
where c(X), m(X), d(..) and mu(..) are the tables folded at X (kept rows add a term, see below). The
product of the later variables makes the mask term count once in the sum over the cube. So H sums to
(the sum of U) + eps target, and that is the claim with which the rounds start.

Messages.
   prover    the fresh mask, an oracle of 2^h rows under the mask code that hold the coefficients
             of a hiding polynomial U (unless it came with an earlier message); the sum of U over
             the cube
   verifier  eps                                                    round "FOLD epsilon"
   k times:  prover: the constant and the quadratic coefficient of the round's polynomial;
             verifier: g_j                                          round "FOLD round"
The verifier tests no equation here, nor any other condition on a value that it receives or draws:
its conditions are on shapes, on sizes and on the order of the calls. It sets each linear
coefficient so that the round's check holds, and the value of the last polynomial at g_k becomes the
target of the new claim. The design's aim: a prover that departs from the committed rows ends,
except with the rounds' error, with a claim that is false for them, and the steps after FOLD test
that claim. No theorem here says so.

Kept rows are the main rows of a kept member of the group. They are not among the 2^k rows, and the
claim's coefficients on them get the public factor eps (1 - g_1) .. (1 - g_k). The reason: think of
every main row as a bundle of rows side by side, with a copy of kept row j at place j of every
bundle, and with the coefficients c_j on the copy in bundle 0 only. Folding equal copies gives the
row back, and folding (c_j, 0, .., 0) gives (1 - X_1) .. (1 - X_k) c_j. So nothing is copied or
folded: H gets the term eps (1 - X_1) .. (1 - X_k) V, where V is the value of the claim's forms on
the kept rows.

The fresh mask is an oracle with rows of its own. It gets no out-of-domain sample and is never part
of a sampled oracle message: a sample is a claim on all entries of its oracle message, the batching
before FOLD takes that claim in, and FOLD's input would then read FOLD's own mask (foldMaskOk). It
is read only at the positions of the step that follows this FOLD, so its class of leaves must be one
that is read at that list and at no other. One mask serves one fold (Blk.spendAsMask).

Order. eps must come after the fresh mask and after the sum of U: a prover that knows eps first fits
the sum to a false target and is honest from there on. foldVerify keeps this order. FoldStart is an
ordinary structure, so a caller of the pieces (foldStartVerify, foldEpsilon, foldRoundsVerify) must
keep the order itself; in the C++ the types enforce it (blocks/iop/fold.h).

What this file does not do. At eps and at every round the C++ channel compares the codes and the
numbers of rows of the group that is folded with those from which the plan's errors were computed
(require_group). A block is given the plan's entries (Start.entries), and an entry does not hold
these numbers, so no block makes that comparison. Params.configure sizes the shapes from the
configuration files' numbers (Params.sized) and makes the plans from these shapes. No theorem says
that a plan's errors are those of the shapes on which the blocks run. -/

/-- What is public about one FOLD. -/
structure FoldShape where
  /-- the code of the main rows -/
  code : Nat := noId
  /-- the code of the mask rows, old and fresh -/
  maskCode : Nat := noId
  /-- k, h, the members and where their rows are -/
  layout : GroupLayout := {}
  /-- the class of leaves of the fresh mask -/
  maskLeafClass : Nat := 0
  deriving Inhabited

/-- The shape fits the codes, the layout fits the oracle messages that it names, and some member has
a main row to fold. -/
def foldShapeOk (S : Statement) (F : FoldShape) : Bool :=
  let L := F.layout
  let n := L.members.size
  match S.codes.base[F.code]?, S.codes.mask[F.maskCode]? with
  | some c, some zk =>
    decide (1 ≤ L.k) && decide (L.h ≤ L.k) && maskFits c zk &&
    decide (foldMaskColumns L.k L.h ≤ zk.ell) &&
    L.kept.size == n && L.mainFirst.size == n && L.maskFirst.size == n &&
    ((List.range n).all fun i =>
      match S.oracles[L.members.getD i noId]? with
      | none => false
      | some x =>
        let o := x.shape
        let folded := decide (0 < o.mainRows) && !L.kept.getD i false
        (o.mainRows == 0 || o.code == F.code) && (o.maskRows == 0 || o.maskCode == F.maskCode) &&
        (match L.mainFirst.getD i none with
          | some f => folded && decide (f + o.mainRows ≤ 2 ^ L.k)
          | none => !folded) &&
        (match L.maskFirst.getD i none with
          | some f => decide (0 < o.maskRows) && decide (f + o.maskRows ≤ 2 ^ L.h)
          | none => o.maskRows == 0)) &&
    ((List.range n).any fun i =>
      match S.oracles[L.members.getD i noId]? with
      | none => false
      | some x => decide (0 < x.shape.mainRows) && !L.kept.getD i false)
  | _, _ => false

/-- The claim's coefficient vectors have the lengths of the group's tables, and each of its separate
forms is on a kept member of the layout. -/
def foldRowOk (S : Statement) (F : FoldShape) (row : GroupRow) : Bool :=
  let c := S.codes.base.getD F.code default
  let zk := S.codes.mask.getD F.maskCode default
  row.c.fits (F.layout.k + ceilLog2 c.ell) && row.d.size == zk.ell * 2 ^ F.layout.h &&
  row.kept.all fun f =>
    (match F.layout.find f.oracle with
      | some i => F.layout.kept.getD i false
      | none => false) && f.c.fits (S.tableBits f.oracle .main)

/-- The fresh mask as it is announced: 2^h mask rows under the group's mask code, no sample. -/
def foldMaskNotice (F : FoldShape) : OracleNotice :=
  { shape := { maskRows := 2 ^ F.layout.h, maskCode := F.maskCode, answers := 0 },
    leafClass := F.maskLeafClass }

/-- The oracle that was named as the fresh mask has the mask's shape, is not a member of the group
and has no sample. The paragraph "The fresh mask" at the start of this section says why. -/
def foldMaskOk (S : Statement) (F : FoldShape) (fresh : Nat) : Bool :=
  match S.oracles[fresh]? with
  | none => false
  | some o =>
    o.shape.mainRows == 0 && o.shape.maskRows == 2 ^ F.layout.h &&
    o.shape.maskCode == F.maskCode && !o.sampled && o.shape.answers == 0 &&
    !F.layout.members.contains fresh

/-- Mask and sum have been received. -/
structure FoldStart where
  /-- the shape for which the first message was received -/
  shape : FoldShape
  /-- the oracle that holds the fresh mask -/
  mask : Nat
  /-- the sum of the hiding polynomial over the cube -/
  sum : E
  eps : Option E := none
  deriving Inhabited

/-- FOLD's first message. mask: the number of the fresh mask's oracle, if it came in an earlier
message; otherwise its root is received here. The sum is the last item of the message. -/
def foldStartVerify (F : FoldShape) (mask : Option Nat) : Blk FoldStart := do
  Blk.must (foldShapeOk (← Blk.statement) F)
  let id ← match mask with
    | some id => pure id
    | none => do
      let ids ← Blk.receiveOracles #[foldMaskNotice F]
      Blk.get ids[0]?
  Blk.must (foldMaskOk (← Blk.statement) F id)
  Blk.spendAsMask id
  let sum ← Blk.recvE
  pure { shape := F, mask := id, sum := sum }

/-- Draws eps, in a verifier's message of its own. -/
def foldEpsilon (s : FoldStart) : Blk FoldStart := do
  Blk.must s.eps.isNone
  let eps ← Blk.closeOne "FOLD epsilon" .join
  pure { s with eps := some eps }

/-- The new statement after the rounds. -/
def foldOutput (S : Statement) (F : FoldShape) (row : GroupRow) (fresh : Nat) (eps : E)
    (gamma : List E) (claim : E) : SingleRows :=
  let L := F.layout
  let factor := foldKeptFactor eps gamma
  { code := F.code, maskCode := F.maskCode, layout := L, gamma := gamma, masks := 2, fresh := fresh,
    c := row.c.fixLow gamma eps,
    kept := row.kept.map fun f => { f with c := f.c.scale factor },
    keptRows := (List.range L.members.size).foldl (fun n i =>
      if L.kept.getD i false then
        n + ((S.oracles[L.members.getD i noId]?).map (·.shape.mainRows)).getD 0
      else n) 0,
    d := #[foldMaskForm L.h row.d eps gamma,
           foldMaskWeights L.k L.h (S.codes.mask.getD F.maskCode default).ell gamma.toArray],
    target := claim }

/-- The k rounds: returns the challenges and the running claim after the last round. -/
def foldRounds : Nat → E → Blk (List E × E)
  | 0, claim => pure ([], claim)
  | n + 1, claim => do
    let c0 ← Blk.recvE
    let c2 ← Blk.recvE
    let g ← Blk.closeOne "FOLD round"
    let rest ← foldRounds n (foldClaimRound claim c0 c2 g)
    pure (g :: rest.1, rest.2)

/-- FOLD's rounds. Fails if eps has not been drawn. F must agree with the shape for which the first
message was received in the two codes, in k and h and in the members. The other fields of the layout
(which members are kept, where their rows are) and the mask's class of leaves are not compared. -/
def foldRoundsVerify (F : FoldShape) (row : GroupRow) (start : FoldStart) : Blk SingleRows := do
  let eps ← Blk.get start.eps
  let G := start.shape
  Blk.must (F.code == G.code && F.maskCode == G.maskCode && F.layout.k == G.layout.k &&
    F.layout.h == G.layout.h && F.layout.members == G.layout.members)
  let S ← Blk.statement
  Blk.testOnView fun _ => foldRowOk S F row
  let r ← foldRounds F.layout.k (maddE start.sum eps row.target)
  pure (foldOutput S F row start.mask eps r.1 r.2)

/-- FOLD. mask: the number of the fresh mask's oracle, if it came in an earlier message. -/
def foldVerify (F : FoldShape) (row : GroupRow) (mask : Option Nat) : Blk SingleRows := do
  let s ← foldStartVerify F mask
  let s ← foldEpsilon s
  foldRoundsVerify F row s

end OnBytes
