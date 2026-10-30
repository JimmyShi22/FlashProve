-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/HeadPlan.lean: the plan of the sub-proof of the output head.

The plan holds what is fixed about the sub-proof before a byte of a proof is read: the matrices of
its smallness test, the list of its committed arrays, the number of scalars that it sends, the
length of its vector of reads, and the number of its linear claims. It is computed from public
numbers, which the caller takes from the parameter file. The C++ counterpart is
verifier/src/vf_output_head_plan.inc. A failed test is reported by the name under which cp_verify
refuses, without the prefix "H:" that cp_verify puts before some names that mark a fault of the
program. One name, internal-h-settings, is this file's own.

The head reads one array that it does not commit to: the residual stream that leaves the last group
of layers. The plan builds the shape of that array by itself and compares it with the plan of the
sub-proof that commits to it.

Main definitions: `Plan.names`, `Border`, `Owner`, `HPlanH2`, `matsH`, `slotsH`, `readsLength`,
`readsH`, `claimsH`, `ownerHeld`, `planH2`.
What is not claimed: no theorem is stated here. The C++ plan also lists the sub-proof's rounds. Here
the rounds by which a proof is read come from a dry run of the check (OnBytes/Model/Head.lean). The
list of rounds from which the planner computes a plan's errors is in OnBytes/Model/HeadRounds.lean.
-/
import OnBytes.Model.HeadLayout
import OnBytes.Model.Tsc
import OnBytes.Model.Tail
import OnBytes.Model.Merge
import OnBytes.Model.Tensors

namespace OnBytes.Model.Head

/-- The names of the refusals that this file raises itself. To the last one cp_verify appends the
label of the first field in which two records of one matrix differ. Here the name ends before it. -/
def Plan.names : List String :=
  ["internal-h-settings", "plan-tensor-layout", "hid-vocab-cols", "internal-h-forest",
   "internal-h-owner-TX", "shape-product-layer-H", "internal-h-tree-list",
   "internal-h-owner-shape", "internal-border-count", "hid-h-slots",
   "internal-h-owner-place"]

/-- What the head needs to know, from the layout of the layers' sub-proofs, about a matrix that
holds the residual stream. -/
structure Border where
  /-- the rows of the matrix -/
  mxb : Nat
  /-- its columns -/
  kxb : Nat
  /-- the first feature of the stream's tensor in the matrix -/
  off : Nat
  /-- the limbs of a value -/
  nl : Nat
  /-- the number of layers in the tensor; `Border.cell` reads layer 0 only -/
  cnt : Nat
  /-- the features of one limb of one layer -/
  J : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Where the stream's tensor lies among the features of the matrix. -/
def Border.xb (b : Border) : TenAt := { off := b.off, nl := b.nl, cnt := b.cnt, J := b.J }

/-- The feature of the matrix that holds limb l of the stream's feature j, in layer 0 of the tensor.
-/
def Border.cell (b : Border) (l j : Nat) : Nat := tenCell b.xb l 0 j

/-- What the head's plan reads of the plan of the last group of layers, which commits to the
stream that the head reads. -/
structure Owner where
  /-- the owner's tail -/
  tl : HTailF2
  /-- the owner's arrays: name, rows, columns and virtual rows of each -/
  Fp : Fork
  /-- one record for each of the owner's arrays, in the same order -/
  Tp : Tail2
  /-- the number, in the owner's list of matrices, of the stream that leaves the group -/
  iXO : Nat

/-- The plan of the head's sub-proof. -/
structure HPlanH2 where
  /-- the tail: the smallness test on the sub-proof's matrices -/
  tl : HTailF2
  /-- the arrays that the claims read: name, rows, columns and virtual rows of each -/
  Fp : Fork
  /-- one record for each of these arrays, in the same order -/
  Tp : Tail2
  /-- the lengths of the vectors U1, U2 and U3 over the extension field; the head has U3 alone -/
  nU : Array Nat := #[0, 0, 0]
  /-- the number of scalars that the sub-proof sends -/
  nMsg : Nat := 0
  /-- the number of its linear claims -/
  nLin : Nat := 0
  /-- the number of its claims on the committed weights -/
  NCL : Nat := 1
  /-- the number of rounds over the channels (the d features of an activation, padded to 2^lPd) in
  the last token sumcheck -/
  lamS : Nat := 0
  /-- the column bits of the committed matrix of weights: the rounds of the merge -/
  lkW : Nat := 0
  /-- the number of rows that the last round batches: all claims, and the smallness test's
  equations, which stand under further powers of the same batching element -/
  rows : Nat := 0

/-- The same number as nMsg, under the name that the plans of the other sub-proofs use. That many
entries of the link's mask row are in use. -/
def HPlanH2.ns (P : HPlanH2) : Nat := P.nMsg

/-- The matrices of the head's smallness test. The NHf parts of hf, then hd, hr and bH are its own,
and no other sub-proof reads them. The last one, the stream, belongs to the last group of layers.
gid is the head's number among the sub-proofs. streamId is the owner's label of the stream. -/
def matsH (h : Shape) (L : HL) (b : Border) (gid streamId : Nat) : Array TMat :=
  let own : List (String × Nat × Nat) :=
    ((List.range h.NHf).map fun p => ("hf" ++ toString p, L.m, L.k)) ++
      [("hd", L.mD, L.kD), ("hr", L.mR, L.kR), ("bH", 2 ^ h.lmbH, L.kb)]
  (own.zipIdx.map fun x =>
    ({ name := x.1.1, m := x.1.2.1, k := x.1.2.2, aId := gid * 256 + x.2 } : TMat)).toArray.push
    { name := "xbL", m := b.mxb, k := b.kxb, kind := 1, foreign := some 0, ttOff := 0,
      aId := streamId }

/-- The number of scalars that the sub-proof sends: the lookup of its calls, the smallness test,
the sums of limb products, the product layer of the squares, the row products, the three token
sumchecks and the merge. The check refuses (internal-slot-count) if it receives another number. -/
def slotsH (h : Shape) (L : HL) (tl : HTailF2) (lkW : Nat) : Nat :=
  Forest.elems L.fs + tl.smallElems + ledNS h.XL + layerSlots (h.lPd + h.lt) + ledNP h.XL +
    tscSlots h.lt (ledNO h.XL) 2 + tscSlots h.lt 2 2 + tscSlots h.lt 2 2 h.lPd + wsForkSlots lkW

/-- The length of the vector of reads. hf has two long tables, the stream two, hd two short ones,
hr six, and bH three. -/
def readsLength (h : Shape) (L : HL) (b : Border) : Nat :=
  2 * (L.filled * h.T / 2 ^ h.la) + 2 * (b.kxb * (b.mxb / 2 ^ h.la)) + 2 * L.fillD + 6 * L.fillR +
    3 * L.kb

/-- The number of reads, one for each table and each stretch of rows
(OnBytes/Model/HeadTables.lean). -/
def readsH (h : Shape) (L : HL) (b : Border) : Nat :=
  2 * h.NHf * (L.m / 2 ^ h.la) + 2 * (L.mD / 2 ^ h.lt) + 6 * (L.mR / 2 ^ h.lt) + 3 +
    2 * (b.mxb / 2 ^ h.la)

/-- The number of linear claims, one term for each group: the lookup's claims on mask entries
alone; three of the sum of squares; the norm's ledger; three of the stream times the reciprocal; the
lookup's join; the four lines of the acceptance policy; three on the lookup's planes; two of the
logits; the merge's; and the smallness test's. `walk` in OnBytes/Model/Head.lean adds the claims in
this order, except that it adds the smallness test's before those of the logits. -/
def claimsH (h : Shape) (L : HL) (tl : HTailF2) (reads : Nat) : Nat :=
  Forest.lins L.fs + 3 + (1 + 1 + ledNO h.XL + ledNS h.XL + ledLines h.XL) + 3 + 1 + 4 + 3 + 2 + 1 +
    tl.lins reads

/-- Compares the shape and the place that this plan gives the stream with the owner's plan. NGr is
the number of groups of layers. Returns the tail with the record of where the stream lies. A
difference is a fault of the program, never of a proof. cp_verify counts such comparisons over all
sub-proofs and tests the count. Nothing is counted here: whenever planH2 succeeds it has made
exactly this one comparison, and the caller computes the count from the numbers of plans (publicOf,
OnBytes/Model/VerifyPublic.lean). The test under internal-border-count keeps the two differences
below it from going under 0; in cp_verify borderMeans refuses a negative number under the same name.
-/
def ownerHeld (O : Owner) (NGr : Nat) (tl : HTailF2) (Fp : Fork) (Tp : Tail2) :
    Except String HTailF2 := do
  let last ← match O.tl.ix.TX.back? with
    | some t => pure t
    | none => throw "internal-h-owner-TX"
  let mine := tl.ix.FT.getD 0 0
  needed (t2SameShape (O.Tp.nt.getD last {}) (O.Fp.trees.getD last {}) (Tp.nt.getD mine {})
    (Fp.trees.getD mine {})) "internal-h-owner-shape"
  needed (0 < NGr && 0 < O.tl.pkMat.size + O.tl.ix.TX.size) "internal-border-count"
  let tl ← tl.borderMeans 0 (NGr - 1) (O.tl.pkMat.size + O.tl.ix.TX.size - 1)
  let df := samePlaceF (← O.tl.ownEntry "stream") (tl.plFor.getD 0 {})
  needed df.isEmpty "internal-h-owner-place"
  pure tl

/-- The plan. g: the numbers that the parameter file sets for a run. h, L: the head's public numbers
and the layout made from them. b, O: the matrix of the stream and the plan of the last group of
layers, from the layers' layout and plans. NGr: the number of groups of layers, at least 1. lkW: the
column bits of the committed matrix of weights.

Three tests have no counterpart in vf_output_head_plan.inc. internal-h-settings: lidb and nminH,
in g and in h, agree, and the bits of work g.pow are below the security target g.hb, so that
g.hb - g.pow is the difference that the C++ source takes in 32 bits (cp_verify's reader of the
parameter file has already refused work that reaches the target). plan-tensor-layout: each limb of
the stream's tensor begins at a multiple of S2, as the layers' layout has tested, and has room for d
features. internal-h-owner-TX, at its first use: the owner has a matrix number O.iXO. -/
def planH2 (g : Settings) (h : Shape) (L : HL) (b : Border) (O : Owner) (NGr lkW : Nat) :
    Except String HPlanH2 := do
  needed (g.lidb == h.LIDB && g.nminH == h.NMINH && g.pow < g.hb) "internal-h-settings"
  needed (b.off % h.S2 == 0 && (b.cnt * b.J) % h.S2 == 0 && h.d ≤ b.J) "plan-tensor-layout"
  needed (clog2 h.V ≤ lkW) "hid-vocab-cols"
  needed (L.fs.calls.size == L.calls.size && L.fs.pub.size == L.fs.NT) "internal-h-forest"
  needed ((← Forest.planeCols L.fs h.lmbH) == L.kb) "internal-h-forest"
  let stream ← match O.tl.mats[O.iXO]? with
    | some M => pure M
    | none => throw "internal-h-owner-TX"
  let mats := matsH h L b (1 + NGr) stream.aId
  let fx : T2Foreign := { name := "PXf0", K := b.kxb, a := 2, m := b.mxb, wp := 0 }
  let tl ← ({ tau := g.tau, lidb := g.lidb } : HTailF2).shape mats
    (Array.replicate mats.size none) #[fx] #[false, false, true, false] g.tau
  needed (9 ≤ h.lPd + h.lt) "shape-product-layer-H"
  let msg := slotsH h L tl lkW
  let nU := #[0, 0, readsLength h L b]
  let reads := readsH h L b
  let nLin := claimsH h L tl reads
  let (tl, Fp, Tp) ← tl.addTrees {} {} nU #[] (g.hb - g.pow) g.hb
  -- the list: U3, one array for each own matrix, ZZ, BZ, and the array read from the last layers
  needed (Tp.nt.size == 1 + tl.pkMat.size + 2 + 1) "internal-h-tree-list"
  let Tp ← t2Plan Fp Tp
  let tl ← ownerHeld O NGr tl Fp Tp
  needed (msg < 2 ^ 30) "hid-h-slots"
  pure { tl := tl, Fp := Fp, Tp := Tp, nU := nU, nMsg := msg, nLin := nLin, NCL := 1,
         lamS := h.lPd, lkW := lkW, rows := nLin + tl.equationsF reads }

end OnBytes.Model.Head
