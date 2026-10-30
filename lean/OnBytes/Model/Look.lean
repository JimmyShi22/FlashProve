-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Look.lean: the lookup on hidden values, the part that reads a proof.

All lookup calls of one sub-proof are handled by one argument with product trees. Its public numbers
are in OnBytes/Model/Forest.lean; read the head of that file first. The docstring of Forest.Heard
explains the words, and that of Forest.pad the argument, its messages and what the caller owes. The
page on the argument is docs/format/11-1-machinery.md (section 11.1 of the format).

C++ counterpart: verifier/src/vf_lookup_argument.h (forestDraws, forestTie, forestPad,
forestObjects, forestPaddingLaid, forestJoin, forestPlaneClaims, forestPlaneLins, forestPhiB,
forestPhiP) and verifier/src/vf_lookup_helpers.h (uEnt, HFun, stackRounds, eqLow, eqLowAt). uEnt,
HFun, Stack, stackRounds, eqLow and eqLowAt are not part of the lookup. They are helpers of the
sub-proofs, kept here because the C++ keeps them in vf_lookup_helpers.h.

Main definitions: lookNames, uEnt, HFun, Stack, stackRounds, eqLow, eqLowAt; in the namespace
Forest: Heard, draws, tie, pad, objects, join, paddingLaid, planeClaims, planeLins, planesAdded,
joinAdded, phiB, phiP.

Rules that the types do not enforce.
 - No equation is tested here: the caller must add every claim (Forest.pad, What the caller owes).
 - Some things must be committed, and others fixed by the transcript, before the draws; else a false
   lookup can be accepted (the same place).
 - Only Forest.pad should build a Heard (Forest.Heard).
 - Control flow (what is received, which rounds are closed) depends only on public numbers.

What this file does not claim. It holds no theorem. As read, it differs from the two C++ files in
four places, three of which no input reaches: see Forest.pad (two), Heard and planeClaims. The names
of sections, which serve a report of false claims in tests, the numbering of a sub-proof's arrays,
and the record of the header's word hb and its position (TargetBitsWord) are left out.
-/
import OnBytes.Field.Ext
import OnBytes.Model.Forest
import OnBytes.Model.Hide
import OnBytes.Model.Psc

namespace OnBytes.Model

/-- The names under which this file itself refuses. Three more refusals here have no name of their
own. Forest.pad drops the name that Forest.shape or Forest.pubAsk returns (toOption, toBool), and
Forest.planeClaims drops that of Forest.planeCols. These fail under the word "refused", or under the
name that a caller has given the block (Blk.named, OnBytes/Iop/Ground.lean), where the C++ verifier
prints a name of Forest.names. The routines of OnBytes/Model/Hide.lean and OnBytes/Model/Psc.lean
that are called here have refusals of their own. In the C++ verifier the first four names follow the
sub-proof's prefix, which is left out here. -/
def lookNames : List String :=
  ["internal-L-row", "internal-forest-point", "internal-slot-count", "internal-forest-place",
    "internal-forest-padding-places", "internal-forest-join"]

/-- Entry x of a vector that is stored as array number t of the sub-proof's list of arrays: entry
x mod K of virtual row x / K, where K is the number of the array's columns. This is entry x of the
vector if, for every r, virtual row r of the array has the weight 1 on row r and 0 on all other
rows. The caller must see to that; it is not tested here. Refuses if there is no such array, if it
has no column, or if the row's number does not fit 32 bits: the C++ entry keeps its row in 32 bits,
so a larger number is refused before it would be cut short. Whether the array has virtual row x / K
is tested later, when a claim with this entry is added (Fork.push). -/
def uEnt (t x : Nat) : SubM Aff := do
  let cols := (((← get).trees[t]?).map (·.K)).getD 0
  mustAs "internal-L-row" (cols != 0 && x / cols < 2 ^ 32)
  pure (Aff.ent t (x / cols) (x % cols))

/-- A table of evaluations that a sub-proof keeps in one of its vectors over E (U1 or U3). The rows
of a committed matrix are taken in blocks of len rows. The table has one entry for each block and
column: the column's entries in that block, combined under the weights phi. -/
structure HFun where
  /-- the matrix, by its number in the sub-proof's list of matrices -/
  mat : Nat := 0
  /-- the number of rows in a block, which is the number of weights -/
  len : Nat := 0
  /-- the weights -/
  phi : Array E := #[]
  /-- which vector holds the table: 0 is U1, 2 is U3; it is no index into the sub-proof's list of
  arrays -/
  tree : Nat := 0
  /-- the table's first entry in that vector -/
  start : Nat := 0
  deriving Inhabited

/-- Runs rounds of one form in a row. Each entry of zs gives a round's coordinate of the equality
point and its degree; roundIn (OnBytes/Model/Psc.lean) says which of the two a form reads. Returns
the challenges in the order of the rounds, and the new state of the sumcheck. -/
def roundsIn (form : RoundForm) (p : Psc) (zs : List (E × Nat)) : SubM (Array E × Psc) :=
  zs.foldlM
    (fun (s : Array E × Psc) z => do
      let (r, q) ← roundIn form s.2 z.1 z.2
      pure (s.1.push r, q))
    (#[], p)

/-- The state of a batched sumcheck: lam rounds without an equality factor, and their challenges.
rs[v] is the coordinate of bit v. The caller begins the sumcheck, ends it and takes its claim. -/
structure Stack where
  /-- the number of rounds -/
  lam : Nat := 0
  /-- the challenges, by the bit that each belongs to -/
  rs : Array E := #[]
  /-- the sumcheck -/
  p : Psc
  deriving Inhabited

/-- The lam rounds of degree 2 of a batched sumcheck. The top bit is bound first. -/
def stackRounds (st : Stack) : SubM Stack := do
  let (r, p) ← roundsIn .sum2 st.p (List.replicate st.lam (zeroE, 0))
  pure { st with rs := r.reverse, p := p }

/-- The equality weights over the bits lo to hi - 1, where rs[v] is the coordinate of bit v. The
caller sees to it that lo ≤ hi and that rs has at least hi members; else the table is shorter. -/
def eqLow (rs : Array E) (lo hi : Nat) : Array E := eqTab (rs.extract lo hi).reverse

/-- Entry c of eqLow rs lo hi: bit j of c goes with rs[lo + j]. It is 0 if the table has no entry c;
a caller whose c is not plainly below 2^(hi - lo) tests eqIndexOK first. -/
def eqLowAt (rs : Array E) (lo hi c : Nat) : E := eqOne (rs.extract lo hi).reverse c

namespace Forest

/-- The padding key of call c, moved by the shift. -/
def padKeyOf (h : Shape) (theta : E) (c : Nat) : E :=
  let row : F := ((h.calls[c]?).map fun k => k.tauAt k.t0).getD 0
  addE (ofF row) (scaleE c.toUInt64 theta)

/-- What the verifier holds after the messages of a lookup.

Words. v = dT + rK is the number of bits of a key's index, and d = kT + cK that of a table row's
index (Forest.Shape). The prover does not send a hidden value itself: it sends the value plus a
public factor times one entry of the mask row, a row that it has committed to. The scalars that a
sub-proof sends are numbered, and a scalar's number is its slot. A form is an affine combination of
hidden values, and a claim says that a form is 0 (OnBytes/Model/Hide.lean). Names taken from the C++
call an array of the sub-proof a tree (Fork.trees, Piece.tree); that is not a tree of keys.

The shape (Shape) and what a run leaves (Heard) are two types here. In the C++ they are one record,
which holds pointers to its owed claims (HFork::owe), null until a proof is read, and a null one
is refused (internal-forest-no-proof-read). Here Heard is a plain record that any code can build,
and owedObjects, owedPlanes and owedJoin are indices into Fork.owed, 0 by default. This guards less
than the C++ does: Forest.objects, planesAdded and joinAdded mark whichever entry has that index,
and if there is none, nothing is marked and nothing is refused. Only Forest.pad should build a
Heard; nothing enforces that. -/
structure Heard where
  /-- the public numbers, with the numbers of padding keys -/
  shape : Shape
  /-- the shift; 0 if there is one call -/
  theta : E := zeroE
  /-- the point at which the two products are compared -/
  alpha : E := zeroE
  /-- the product of alpha - key over all padding keys -/
  a : E := oneE
  /-- the claims of the tie, of the key levels, of the table levels and of the bits' sumcheck -/
  rows : Array Aff := #[]
  /-- the sumcheck over the leaves of the table side; planeClaims makes its claim -/
  leaves : Psc
  /-- alpha - 1 - (the table at the leaves' point): the factor of the planes' value there -/
  leavesA : E := zeroE
  /-- the slot of the hidden value of the planes at zb1 -/
  sBit : Nat := 0
  /-- the key side's point: the coordinates of the place in a tree -/
  zx : Array E := #[]
  /-- the key side's point: the coordinates of the tree's number -/
  zy : Array E := #[]
  /-- the weight of call c's trees at zy -/
  e : Array E := #[]
  /-- the hidden value of the key side's leaves at (zx | zy) -/
  cEnd : Aff := Aff.ofConst zeroE
  /-- the point (t | c | j) at which the leaves' sumcheck reads the planes -/
  zb0 : Array E := #[]
  /-- the point (t | c | j) at which the bits' sumcheck reads the planes -/
  zb1 : Array E := #[]
  /-- call c's table at the last k_c of zb0's coordinates of t -/
  tT : Array E := #[]
  /-- the point at which call c's key vector is read: the last iota_c coordinates of zy, then zx. It
  is not a contiguous part of the drawn point (zx, zy). The low bits of a tree's number, which tell
  the call's trees apart, are the top bits of a key's number in its call. -/
  zk : Array (Array E) := #[]
  /-- the number, in the sub-proof's list of owed claims (Fork.owed), of the entry for the claims
  that read only mask entries -/
  owedObjects : Nat := 0
  /-- the number of the entry for the three claims on the planes in the list of owed claims -/
  owedPlanes : Nat := 0
  /-- the number of the entry for the claim on the key vectors in the list of owed claims -/
  owedJoin : Nat := 0
  deriving Inhabited

/-- The first or the second point at which the planes are read. -/
def Heard.zb (g : Heard) (e : Nat) : Array E := if e = 0 then g.zb0 else g.zb1

/-- The padding key of call c, moved by the shift. The trees that hold only padding hold call 0's
padding key. -/
def Heard.padKey (g : Heard) (c : Nat) : E := padKeyOf g.shape g.theta c

/-- The shift, if the group has several calls, then alpha. Returns them with the public factor a.
h.pub must have been filled in and tested by pubAsk. Only Forest.pad calls it. -/
def draws (h : Shape) : SubM (E × E × E) := do
  let theta ← if h.NC > 1 then SubM.answer .lkpShift else pure zeroE
  let alpha ← SubM.answer .lkp
  let a := (List.range h.NT).foldl
    (fun a y =>
      mulE a (powE (subE alpha (padKeyOf h theta (h.callOf.getD y 0))) (h.pub.getD y 0)))
    (powE (subE alpha (padKeyOf h theta 0)) h.emptyKeys)
  pure (theta, alpha, a)

/-- What Forest.tie returns. The tie is the part of the lookup that is meant to show
Z = a G_0 G_1^2 G_2^4 .., where Z is the root of the key side and G_j the root of plane j of the
table side. -/
structure Tie where
  /-- its 31 claims -/
  rows : Array Aff := #[]
  /-- the slot of the key side's root -/
  sZ : Nat := 0
  /-- the point of the table side's top level -/
  rhoT : Array E := #[]
  /-- the start form of the table side's top level -/
  cT : Aff := Aff.ofConst zeroE

/-- The state of the tie's loop: the claims, and the slots of Z, of the last power P and of the
roots G of the planes so far. -/
structure TieStep where
  /-- the claims so far -/
  rows : Array Aff := #[]
  /-- the slot of Z -/
  sZ : Nat := 0
  /-- the slot of the power that was shown last -/
  sP : Nat := 0
  /-- the slots of the planes' roots -/
  sG : Array Nat := #[]

/-- Step j of the tie. Write Z for the product of alpha - key over all keys and G_j for the product
over the leaves of plane j. The tie computes the product of the G_j^(2^j) by squaring: P_31 = G_31
and P_j = P_(j+1)^2 G_j. None of these values is sent as it is: what a step shows is a value plus a
factor times a mask entry (OnBytes/Model/Hide.lean). Step 0 is a sumcheck without a variable for
0 = Z - a P_1^2 G_0; its end values are Z, P_1, G_0. Step j, for j from 1 to 30, is one for
P_j = P_(j+1)^2 G_j; its end values are P_(j+1), G_j. -/
def tieStep (a : E) (s : TieStep) (j : Nat) : SubM TieStep := do
  let p ← pscBegin (if j = 0 then Aff.ofConst zeroE else Aff.slot s.sP)
  let (first, p) ← pscEnds p 3 (if j = 0 then 3 else 2)
  let sZ := if j = 0 then first else s.sZ
  let sP := if j = 0 then first + 1 else first
  let vP ← SubM.shown sP
  let vG ← SubM.shown (sP + 1)
  let power := mulE (mulE vP vP) vG
  let summand ← if j = 0 then do pure (subE (← SubM.shown sZ) (mulE a power)) else pure power
  let (row, _) ← pscRow p summand
  pure { rows := s.rows.push row, sZ := sZ, sP := sP, sG := s.sG.push (sP + 1) }

/-- The tie Z = a G_0 G_1^2 G_2^4 .. of the two sides' roots, and the point that joins the roots of
the planes. These 32 roots are the top level of the table side: one claim on it at a fresh point. -/
def tie (a : E) : SubM Tie := do
  let s ← (List.range 31).foldlM (tieStep a) {}
  let sG := s.sG.push s.sP
  let rhoT := (← SubM.point .lkpPlanes 5).reverse
  let ej := eqTab rhoT
  let cT := (List.range 32).foldl
    (fun (f : Aff) j => Aff.addMul f (Aff.slot (sG.getD j 0)) (ej.getD j zeroE))
    (Aff.ofConst zeroE)
  pure { rows := s.rows, sZ := s.sZ, rhoT := rhoT, cT := cT }

/-- The state of a walk down a product tree: the claims so far, the point and the form of the
level that comes next. -/
structure Descent where
  /-- the claims so far -/
  rows : Array Aff := #[]
  /-- the point of the next level -/
  rho : Array E := #[]
  /-- the hidden value of the next level at that point -/
  form : Aff := Aff.ofConst zeroE

/-- One level of a product tree with mu variables, bound in the given order. -/
def level (s : Descent) (mu : Nat) (order : List Nat) : SubM Descent := do
  let o ← levelIn mu s.rho s.form order
  let (rho, form) := o.handDown
  pure { rows := s.rows.push o.row, rho := rho, form := form }

/-- The weight of call c's trees at the point zy of the trees' numbers. The trees of a call share
the top rK - iota_c bits of their numbers. -/
def callWeight (h : Shape) (zy : Array E) (c : Nat) : E :=
  let hi := h.rK - h.iota.getD c 0
  let pre := h.first.getD c 0 / 2 ^ h.iota.getD c 0
  (List.range hi).foldl
    (fun e i =>
      let z := zy.getD i zeroE
      mulE e (if (pre / 2 ^ (hi - 1 - i)) % 2 = 1 then z else subE oneE z))
    oneE

/-- A call's table as a multilinear polynomial at the point u of k coordinates, the top bit's
first. -/
def tableAt (c : Call) (u : Array E) : E :=
  match c.tau with
  | none =>
    (List.range c.k).foldl
      (fun s i => addE s (scaleE (2 ^ (c.k - 1 - i)).toUInt64 (u.getD i zeroE))) zeroE
  | some rows =>
    let et := eqTab u
    (List.range et.size).foldl
      (fun s t => addE s (scaleE (rows.getD t 0) (et.getD t zeroE))) zeroE

/-- The joined table at the coordinates zc of the call's number: call c's table moved by c theta.
tT[c] is call c's table at the coordinates of the row. The numbers from NC on hold the last call's
table once more, moved by the last call's shift, (NC - 1) theta, not by their own number times
theta. -/
def joinedTableAt (h : Shape) (theta : E) (tT zc : Array E) : E :=
  let ec := eqTab zc
  (List.range (2 ^ h.cK)).foldl
    (fun s c =>
      let c' := min c (h.NC - 1)
      addE s (mulE (ec.getD c zeroE) (addE (tT.getD c' zeroE) (scaleE c'.toUInt64 theta))))
    zeroE

/-- The messages of the lookup. The name is that of the C++ routine, forestPad; nothing is padded
here. pub[y] is the number of padding keys of tree y. lid is the cap on a tree's depth. Where
Forest.shape or Forest.pubAsk refuses, this function fails without a name of its own: the name that
they return is dropped (see lookNames).

The argument. The verifier draws a shift theta (if there are several calls) and a point alpha. Call
c's keys and table rows are moved by c theta. The shift is meant to keep a key of one call from
passing as a row of another call's table, up to the error of the draw; no theorem here says so. The
product of alpha - key over all keys must equal a public factor, the product over the padding keys,
times the product of (alpha - row)^count over all table rows. A row's count is the number of keys,
padding not counted, that hit it. The counts are committed as 32 planes of bits: plane j holds bit j
of every count. Both products are computed by trees of products, and each level of a tree is reduced
to the next by a sumcheck on hidden values.

The messages, in their order (Forest.pad):
  theta, alpha | the tie of the two sides' roots (the check that the two products agree), 31
  sumchecks without a variable | a point of 5 coordinates, which joins the roots of the planes | the
  key side, levels 0 to v - 1 | the table side, levels 0 to d - 1 | the leaves of the table side | a
  point of 5 + d coordinates, and the sumcheck that the bits are bits.

No equation is tested here. Every sumcheck leaves one linear claim on hidden values. The sub-proof
adds all claims to its one equation, after the element that batches them is drawn:
  Forest.objects     the claims that read only mask entries,
  Forest.planeLins   the three claims that read the planes,
  Forest.join        the one claim on the key vectors (the caller adds it).

What the caller owes. Nothing here binds a public number or a commitment. A prover that could choose
one of the following after a draw could get a false lookup accepted.
 1. Before theta is drawn (before alpha, if there is one call) three things must be committed, and
    the out-of-domain samples of their commitments answered: the planes, whatever the key vectors
    are read from, and the mask row on whose entries all claims here are tested. Every sumcheck's
    eps must be drawn after the mask row's sample is answered (blocks/iop/psc.h, under ORDER).
 2. What the transcript holds before that draw must fix every one of the following.
    - The number of the calls and their order. They decide c in c theta, Shape.first and Heard.e,
      which table fills the numbers from NC on, and whether theta is drawn.
    - Of each call: n (it has 2^n keys), k (its table has 2^k rows), t0 (the row that padding keys
      hold) and the table (that it is the range table, or all its rows).
    - lid, the cap on a tree's depth.
    - pub[y] for every tree. It enters the public factor and the target of the counts' sum.
    - lm (the planes' matrix has 2^lm rows), which committed matrix the plane claims read and by
      which map of rows and columns, and that this matrix has no column for a number c from NC on.
    - What each key form (KF in Forest.join) reads.
    - The commitment to the mask row and its length; the lookup's first slot; the number of claims
      that were added before the lookup's first (a claim's weight is the power of the batching
      element that the claim's number gives).
    - The constants that Forest.shape tests (32 planes, no row with a count of its own) and the
      setting (field, hash).
    The plan of the chain does not fix all this. It holds v, d, the number of planes and whether
    there is a shift. Two groups with (dT, rK) = (10, 2) and (11, 1), or with (kT, cK) = (6, 1) and
    (5, 2), have the same rounds in the plan, so a dry run against the plan does not tell them
    apart; yet their rounds bind variables in different orders, and their weights and tables differ.
 3. All claims listed above must be added. Forest.pad enters them in the sub-proof's list of owed
    claims (Fork.owed), and the sub-proof's end (Fork.settle) refuses while one is open. This
    catches a forgotten claim and nothing more: a mark does not see what was added, and Forest.join
    marks its claim when the form is made, not when the caller adds it.

Two differences from the C++ (forestPad). The first is only where a routine stands; no input
reaches the second.

First: the lookup's rounds are entered in a plan by Params.planForest
(OnBytes/Params/SubRounds.lean), not here.

Second: Forest.pad tests internal-forest-place for all calls and then internal-forest-point for all
calls. The C++ tests both call by call, so only the name of a refusal could differ. -/
def pad (calls : Array Call) (pub : Array Nat) (lid : Nat) : SubM Heard := do
  let h0 ← SubM.get (shape calls lid).toOption
  SubM.must (pubAsk h0 pub).toBool
  let h : Shape := { h0 with pub := pub }
  let v := h.v
  let d := h.d
  let m := 5 + d
  let slot0 ← SubM.slot
  let owedObjects ← SubM.owe "look-up-mask-claims"
  let owedPlanes ← SubM.owe "look-up-plane-claims"
  let owedJoin ← SubM.owe "look-up-join"
  let (theta, alpha, a) ← draws h
  let t ← tie a
  -- the key side
  let keys ← (List.range v).foldlM
    (fun (s : Descent) mu =>
      level s mu (if mu + 1 = v then orderForestRange mu h.rK else orderDefault mu))
    { rows := t.rows, rho := #[], form := Aff.slot t.sZ }
  let zx := keys.rho.extract 0 h.dT
  let zy := keys.rho.extract h.dT keys.rho.size
  -- the table side
  let table ← (List.range d).foldlM
    (fun (s : Descent) l => level s (5 + l) (orderDefault (5 + l)))
    { rows := keys.rows, rho := t.rhoT, form := t.cT }
  mustAs "internal-forest-point" (table.rho.size == m)
  -- A leaf of the table side is 1 + b (alpha - 1 - row) for a bit b of a count. This is of degree 1
  -- in the planes, so the sumcheck ends without a shown value. Without the equality factor, a
  -- round's polynomial has degree 2 in a variable of the rows and degree 1 in one of the planes.
  let leaves ← pscBegin table.form
  let (zb0, leaves) ← roundsIn .eq leaves
    ((List.range m).map fun j => (table.rho.getD j zeroE, if j < d then 2 else 1))
  -- Every entry b of the planes is 0 or 1: b^2 - b, weighted by eq at a fresh point, sums to 0.
  let r5 := (← SubM.point .zero m).reverse
  let bits ← pscBegin (Aff.ofConst zeroE)
  let (zb1, bits) ← roundsIn .eq2 bits (r5.toList.map fun z => (z, 0))
  let (sBit, bits) ← pscEnds bits 2 1
  let vBit ← SubM.shown sBit
  let (bitsRow, _) ← pscRow bits (subE (mulE vBit vBit) vBit)
  let rows := table.rows.push bitsRow
  mustAs "internal-slot-count" ((← SubM.slot) == slot0 + elems h && rows.size == lins h)
  -- for each call its weight, its point, and its table at the leaves' point
  mustAs "internal-forest-place" (h.iota.all fun i => decide (i ≤ h.rK))
  let zk := (Array.range h.NC).map fun c => zy.extract (h.rK - h.iota.getD c 0) zy.size ++ zx
  mustAs "internal-forest-point" ((List.range h.NC).all fun c =>
    (zk.getD c #[]).size == ((h.calls[c]?).map (·.n)).getD 0)
  let tT := h.calls.map fun k => tableAt k (zb0.extract (h.kT - k.k) h.kT)
  let row := joinedTableAt h theta tT (zb0.extract h.kT (h.kT + h.cK))
  pure {
    shape := h, theta := theta, alpha := alpha, a := a, rows := rows, leaves := leaves,
    leavesA := subE (subE alpha oneE) row, sBit := sBit, zx := zx, zy := zy,
    e := (Array.range h.NC).map (callWeight h zy), cEnd := keys.form, zb0 := zb0, zb1 := zb1,
    tT := tT, zk := zk, owedObjects := owedObjects, owedPlanes := owedPlanes,
    owedJoin := owedJoin }

/-- Adds the claims that read only mask entries (the tie's, the key levels', the table levels', the
bits') and marks them as added in the list of owed claims. -/
def objects (g : Heard) : SubM Unit := do
  g.rows.forM SubM.lin
  SubM.paid g.owedObjects

/-- Marks the three claims on the planes as added. For a sub-proof that adds them itself, made by
planeClaims or written out by hand. -/
def planesAdded (g : Heard) : SubM Unit := SubM.paid g.owedPlanes

/-- Marks the claim on the key vectors as added. For a sub-proof that writes the claim out by
hand. -/
def joinAdded (g : Heard) : SubM Unit := SubM.paid g.owedJoin

/-- A guard against a slip in the verifier's own code. The padding is described twice: by pub[y],
which enters the public factor and the target of the counts' sum, and by the places that the
sub-proof's key forms treat as padding, which the caller counts in laid[y]. Both are public numbers,
so a difference is a fault of the program, not of a proof. A padding key is a row of its call's
table, so a difference is not expected to let in a key from outside a table; nothing here proves
that. The caller counts next to its key forms, not from them, so a fault inside a form is not seen;
in the layer and the head (joinStart in OnBytes/Model/Layer.lean, keyForm in
OnBytes/Model/HeadForms.lean) both counts come from the same lists of columns, so a fault in a list
is not seen either. Nothing forces a sub-proof to call this function: it has no entry in the list of
owed claims. -/
def paddingLaid (g : Heard) (laid : Array Nat) : SubM Unit := do
  mustAs "internal-forest-padding-places" (laid == g.shape.pub)

/-- The claim on the calls' key vectors. The leaves of the key side are alpha - (key moved by the
shift). So the sum over the calls c of e_c (alpha - c theta - KF_c), plus the sum over the trees y
that hold only padding of eq(zy, y) (alpha - padding key), minus the hidden value at the end of the
key side, is 0. KF[c] is the form of call c's key vector at zk[c]. The caller adds the claim. The
claim is marked as added here, where the form is made: that the caller adds it is not seen. -/
def join (g : Heard) (KF : Array Aff) : SubM Aff := do
  let h := g.shape
  mustAs "internal-forest-join" (KF.size == h.calls.size && g.e.size == h.calls.size)
  joinAdded g
  let onCalls := (List.range KF.size).foldl
    (fun (f : Aff) c =>
      let key := KF.getD c (Aff.ofConst zeroE)
      Aff.addMul f (Aff.ofConst (subE g.alpha (scaleE c.toUInt64 g.theta)) - key)
        (g.e.getD c zeroE))
    (Aff.ofConst zeroE)
  let ey := eqTab g.zy
  let empty := (List.range (2 ^ h.rK - h.NT)).foldl
    (fun s i => addE s (mulE (ey.getD (h.NT + i) zeroE) (subE g.alpha (g.padKey 0)))) zeroE
  pure (onCalls + Aff.ofConst empty - g.cEnd)

/-- The value of the planes at the point zb e, as a form. The planes are a matrix of 2^lm rows: row
(the low lm - 5 bits of t | j), column (c | the other bits of t). bit e col gives the sum over the
rows of phiB g lm e (row) times the matrix's entry in column col. lm must have passed planeCols.
Only Forest.planeClaims calls it. -/
def planesAt (g : Heard) (lm e : Nat) (bit : Nat → Nat → SubM Aff) : SubM Aff := do
  let h := g.shape
  let w := h.kT + 5 - lm
  let ec := eqTab ((g.zb e).extract h.kT (h.kT + h.cK))
  let et := eqTab ((g.zb e).extract 0 w)
  (List.range (h.NC * 2 ^ w)).foldlM
    (fun (f : Aff) col => do
      let x ← bit e col
      pure (Aff.addMul f x (mulE (ec.getD (col / 2 ^ w) zeroE) (et.getD (col % 2 ^ w) zeroE))))
    (Aff.ofConst zeroE)

/-- The three claims that read the planes, in this order. First, the claim of the leaves' sumcheck,
with the planes' value at zb0. Second, the planes' value at zb1 is what the bits' sumcheck has
shown. Third, the counts sum to the number of keys that are not padding. pin col gives the sum over
the rows of phiP lm (row) times the matrix's entry in column col. The caller adds all three and then
calls planesAdded; planeLins does both. Where Forest.planeCols refuses lm, this function fails
without a name of its own: the name forest-planes is dropped (see lookNames).

The C++ marks the claim of the leaves' sumcheck as made and refuses a second making
(internal-psc-order). Forest.planeClaims drops that mark. A second call on one lookup fails all the
same, without a name of its own: pscRow would fill the slots of the hiding polynomial's coefficients
again, and Fork.hide refuses a slot that is filled. -/
def planeClaims (g : Heard) (lm : Nat) (bit : Nat → Nat → SubM Aff) (pin : Nat → SubM Aff) :
    SubM (Array Aff) := do
  let h := g.shape
  SubM.must (planeCols h lm).toBool
  let at0 ← planesAt g lm 0 bit
  let at1 ← planesAt g lm 1 bit
  let count ← (List.range (h.NC * 2 ^ (h.kT + 5 - lm))).foldlM
    (fun (f : Aff) col => do pure (f + (← pin col)))
    (Aff.ofConst (negE (ofF (2 ^ h.v - h.padding).toUInt64)))
  let (leavesRow, _) ← pscRow g.leaves oneE (Aff.scale at0 g.leavesA)
  pure #[leavesRow, Aff.slot g.sBit - at1, count]

/-- Adds the three claims that read the planes. -/
def planeLins (g : Heard) (lm : Nat) (bit : Nat → Nat → SubM Aff) (pin : Nat → SubM Aff) :
    SubM Unit := do
  (← planeClaims g lm bit pin).forM SubM.lin
  planesAdded g

/-- The weights on the 2^lm rows of the planes' matrix under which the planes are read at the point
zb e: the equality weights of (the last lm - 5 coordinates of t | those of j). Returns none if
planeCols refuses lm. -/
def phiB (g : Heard) (lm e : Nat) : Option (Array E) :=
  let h := g.shape
  let z := g.zb e
  if (planeCols h lm).toBool then
    some (eqTab (z.extract (h.kT + 5 - lm) h.kT ++ z.extract (h.kT + h.cK) z.size))
  else none

/-- The weights on the 2^lm rows of the planes' matrix under which the counts are summed: 2^j on a
row of plane j, which is the row's number modulo 32. -/
def phiP (lm : Nat) : Array E := (Array.range (2 ^ lm)).map fun r => ofF (2 ^ (r % 32)).toUInt64

end Forest

end OnBytes.Model
