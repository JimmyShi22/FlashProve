-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/LayerPlan.lean: the plans of the layer sub-proofs.

Before a byte of a proof is used, the verifier forms a plan for each sub-proof from public numbers:
the matrices of its smallness test, the arrays that its claims read, the number of its slots (the
scalars that it sends) and the number of its claims. The check of the sub-proof then compares its
own counts with the plan's.

A group's sub-proof commits to the residual stream that leaves the group, and the next group's
sub-proof reads that matrix. The shape and the place that the reader's plan gives it are compared
with the owner's plan here. Attention's sub-proof reads the matrix qa in the same way. That
comparison needs attention's plan and is made in OnBytes/Model/VerifyCross.lean.

This file follows verifier/src/vf_layers_plan.inc as far as it concerns the layer sub-proofs, and
the lines of runStage in verifier/src/cp_verify.cpp that list a group's matrices. The C++ file also
enters the sub-proof's rounds into the plan of the chain. That part is in
OnBytes/Model/VerifySubproofs.lean and OnBytes/Params/SubRounds.lean, not here.

Main definitions: tailsOf, Pub, Pub.of, HPlan2, lamSOf, nclOf, claimsOf, readsCount, slotsOf,
bordersOf, planG, plansG, planNames.

What is not claimed: nothing is proved here.
-/
import OnBytes.Model.LayerForms
import OnBytes.Model.Tsc
import OnBytes.Model.Tail
import OnBytes.Model.Merge

namespace OnBytes.Model.Layer

/-- The matrices of the smallness test of each group, in the order that the format fixes: the parts
of af, the parts of ad, ar, b, qa, the stream that goes out, the stream that comes in. A matrix has
the label 256 (1 + g) + its number. From the second group on, the stream that comes in is the
matrix that the group before has committed to as its stream that goes out. -/
def tailsOf (y : Lay) : Array Tail :=
  let ix := matIx y
  let part (n : String) (m : Nat) : List (String × Nat × Nat) :=
    (List.range (y.parts.getD m 0)).map fun p => (n ++ toString p, y.mrow.getD m 0, y.kcol.getD m 0)
  let asks := part "af" 0 ++ part "ad" 1 ++
    [("ar", y.mrow.getD 2 0, y.kcol.getD 2 0), ("b", 2 ^ y.h.lmb, y.kbm),
     ("qa", y.mrow.getD 3 0, y.kcol.getD 3 0), ("xbO", y.mxb, y.kxb), ("xbI", y.mxb, y.kxb)]
  (Array.range y.NGr).map fun g =>
    { mats := (asks.zipIdx.map fun x =>
        let own : TMat := { name := x.1.1, m := x.1.2.1, k := x.1.2.2, aId := (1 + g) * 256 + x.2 }
        if x.2 == ix.iXI && g != 0 then
          { own with kind := 1, foreign := some 0, aId := g * 256 + ix.iXO }
        else own).toArray }

/-- The public numbers that the plans and the checks of the layer sub-proofs read. -/
structure Pub where
  /-- the layout -/
  y : Lay
  /-- which tables of reads there are -/
  rd : Reads
  /-- the quantization scales -/
  sc : Scales
  /-- the rotary table, as ropeOf gives it -/
  rope : Array Nat
  /-- the layout of the committed matrix of weights -/
  wsLay : WsLay
  /-- the size of the vocabulary -/
  V : Nat
  /-- the request's tokens -/
  tokv : Array Nat
  /-- the matrices of each group's smallness test -/
  tails : Array Tail
  /-- the numbers that the parameter file sets for a run -/
  set : Settings

/-- The public numbers from a layout and from what other parts give. The tables of reads and the
lists of matrices are derived from the layout. Refuses under internal-layout-words if the two
records of the cap on a lookup tree's depth differ, and under shape-product-layer if a product
layer has fewer than 9 variables. -/
def Pub.of (y : Lay) (sc : Scales) (rope : Array Nat) (wsLay : WsLay) (V : Nat) (tokv : Array Nat)
    (set : Settings) : Except String Pub := do
  refuseIf (set.lidb != y.h.lidb) "internal-layout-words"
  pure { y, rd := ← readsOf y, sc, rope, wsLay, V, tokv, tails := tailsOf y, set }

/-- The plan of one layer sub-proof. C++: HPlan2. -/
structure HPlan2 where
  /-- the smallness test -/
  tl : HTailF2
  /-- the arrays that the claims read -/
  Fp : Fork
  /-- the list of the arrays that the claims read -/
  Tp : Tail2
  /-- the lengths of the vectors U1 to U3; a layer sub-proof has only U3, the reads -/
  nU : Array Nat
  /-- the number of entries of the mask row -/
  ns : Nat
  /-- the number of slots that the messages take -/
  used : Nat
  /-- the number of weight claims -/
  NCL : Nat
  /-- the number of claims -/
  nLin : Nat
  /-- the number of claims plus the number of indices that the smallness test's equations take
  (HTailF2.equationsF); they are batched under the next powers of the batching element -/
  nBatched : Nat
  /-- the number of rounds of the batched sumcheck -/
  lamS : Nat

/-- The number of rounds of the batched sumcheck: the logarithm, rounded up, of the number of all
panels' places. A panel is the stretch of the sumcheck's two long vectors that one family of inner
products takes (OnBytes/Model/LayerPanels.lean). It counts with its rows and its columns rounded up
to powers of two. -/
def lamSOf (y : Lay) : Nat :=
  let h := y.h
  let wi := ceilLog2 y.Lam
  let ld := ceilLog2 h.d
  let dense := 4 * 2 ^ (wi + ld) + 2 ^ (wi + ceilLog2 y.dq) + 2 ^ (wi + ceilLog2 h.f) + 2 * 2 ^ wi
  let routed :=
    if h.p3 then
      let wm := ceilLog2 y.LamM
      let le := ceilLog2 h.NE
      2 ^ (wm + ld) + 2 ^ wm + 2 * 2 ^ (wm + le) +
        y.LamM * (2 * 2 ^ (le + ld) + 2 ^ (le + ceilLog2 h.fe))
    else 0
  ceilLog2 (dense + routed)

/-- The number of weight claims of group g. The first group has one more, the embedding's. -/
def nclOf (y : Lay) (g : Nat) : Nat :=
  6 * y.Lam + (if y.h.p3 then 4 * y.LamM else 0) + (if g == 0 then 1 else 0)

/-- The number of values that the second token sumcheck shows; 0 if no call has terms for it. -/
def shownByTerms (y : Lay) (rd : Reads) : Nat :=
  if rd.tscCalls.isEmpty then 0
  else y.NN * y.Lam + (if y.h.p3 then y.LamM * (1 + y.h.NE) else 0)

/-- The number of claims of group g without the smallness test's, in the order of the check: the
lookup's own; the claim of the norms' product layer and two on its end values; the batch of the row
products, their token sumcheck, one for each shown row value, the carries, the ledger's lines; one
for each value that the second token sumcheck shows; three for each of the one or two product
layers of the gated products; the selectors' sums; the lookup's three on the planes; the
embedding's; the batched sumcheck's and one for each of its two shown values; the merge's. -/
def claimsOf (y : Lay) (rd : Reads) (g : Nat) : Nat :=
  let xl := y.h.xl
  let p3 := y.h.p3
  Forest.lins y.fo + 3 + (2 + (ledNO xl + ledNS xl + ledLines xl) * y.NI) + shownByTerms y rd + 3 +
    (if p3 then 3 else 0) + (if p3 then y.LamM else 0) + 3 + (if g == 0 then 1 else 0) + 3 + 1

/-- The number of pairs of a table and a block of rows of its matrix, over all tables of group g.
The first group has one more long table of the stream that comes in, at the embedding's point Z_E.
The last 3 are the three tables of matrix b, each of which sums over all rows. -/
def readsCount (y : Lay) (rd : Reads) (g : Nat) : Nat :=
  let la := y.h.la
  let lt := y.h.lt
  rd.rdAF.length * y.parts.getD 0 0 * (y.mrow.getD 0 0 / 2 ^ la) +
    rd.rdQA.length * (y.mrow.getD 3 0 / 2 ^ la) +
    (rd.rdXI.length + (if g == 0 then 1 else 0) + rd.rdXO.length) * (y.mxb / 2 ^ la) +
    rd.rdAD.length * y.parts.getD 1 0 * (y.mrow.getD 1 0 / 2 ^ lt) +
    rd.rdAR.length * (y.mrow.getD 2 0 / 2 ^ lt) +
    (if y.h.p4 then rd.rdQS.length * (y.mrow.getD 3 0 / 2 ^ lt) else 0) + 3

/-- The number of slots of group g, in the order of the messages: the lookup; the convolution sums
W_s (OnBytes/Model/Ledger.lean); the norms' product layer; the row products; their token sumcheck;
the second token sumcheck; the batched sumcheck; the one or two product layers of the gated
products; the embedding's value; the merge; the smallness test. small: the slots of the smallness
test; lk: the merge's rounds. -/
def slotsOf (y : Lay) (rd : Reads) (g lk small : Nat) : Nat :=
  let xl := y.h.xl
  let p3 := y.h.p3
  let first := if g == 0 then 1 else 0
  Forest.elems y.fo + ledNS xl * y.NI + layerSlots rd.muV + ledNP xl * y.NI +
    tscSlots y.h.lt (ledNO xl * y.NI) 2 +
    (if rd.tscCalls.isEmpty then 0 else tscSlots y.h.lt (shownByTerms y rd) 1) +
    sumcheckSlots .sum2 (lamSOf y) (2 + 1 + (if p3 then y.LamM else 0) + nclOf y g - first) 2 +
    layerSlots rd.muH + (if p3 then layerSlots rd.muH2 else 0) + first + wsForkSlots lk + small

/-- Which matrices of a group have a border array, and which are read from another sub-proof. An
own matrix that another sub-proof reads gets a border array of its own: the stream that goes out
and, at profile 4, qa. A matrix of an earlier sub-proof is read from its owner's border
array, from column 0 on. Returns the matrices, for each the number of its border array, and the
list of foreign arrays. Refuses a matrix of kind 2 under internal-weight-matrix. -/
def bordersOf (y : Lay) (mats : Array TMat) :
    Except String (Array TMat × Array (Option Nat) × Array T2Foreign) := do
  let ix := matIx y
  refuseIf (mats.any fun M => M.kind == 2) "internal-weight-matrix"
  let r := mats.toList.zipIdx.foldl
    (fun (s : Array TMat × Array (Option Nat) × Array T2Foreign × Nat) x =>
      let (M, mu) := x
      let (ms, tx, ft, nTX) := s
      if M.kind == 0 && (mu == ix.iXO || (y.h.p4 && mu == ix.iQA)) then
        (ms.push M, tx.push (some nTX), ft, nTX + 1)
      else if M.kind == 1 then
        (ms.push { M with foreign := some ft.size, ttOff := 0 }, tx.push none,
         ft.push { name := "PXf" ++ toString ft.size, K := M.k, a := 2, m := M.m, wp := M.wp }, nTX)
      else (ms.push M, tx.push none, ft, nTX))
    (#[], #[], #[], 0)
  pure (r.1, r.2.1, r.2.2.1)

/-- The plan of group g. O: the plan of the group before; it must be given exactly when g is not 0.
Refuses under the names of the smallness test's shape and of its list of arrays
(OnBytes/Model/Tail.lean); under internal-weight-matrix (bordersOf); under internal-g-owner-shape,
internal-g-owner-place-.. or internal-border-count if this plan and the owner's differ on the stream
that comes in, or if O is given or missing against the rule; and under hid-g-slots if there are 2^30
slots or more. A name that begins with internal can only come from a fault in the program's own
lists. Some of the other names depend on the parameter file: for instance hid-k-range (a matrix has
no column, or more than 8191) and t2f-columns-range (all matrices together have 2^31 rows or more).
-/
def planG (P : Pub) (g : Nat) (O : Option HPlan2) : Except String HPlan2 := do
  let y := P.y
  let ix := matIx y
  let hb := P.set.hb - P.set.pow
  let (mats, txOf, ft) ← bordersOf y (P.tails.getD g {}).mats
  let aTX := (txOf.filter (·.isSome)).map fun _ => 2
  let tl ← ({ tau := P.set.tau, lidb := P.set.lidb } : HTailF2).shape mats txOf ft
    #[false, false, true, false] y.h.tau
  let nX4 := readsCount y P.rd g
  let nLin := claimsOf y P.rd g + tl.lins nX4
  let msg := slotsOf y P.rd g P.wsLay.lk tl.smallElems
  let xi := mats.getD ix.iXI {}
  -- The first group has one more long table of the stream that comes in, at the point Z_E.
  let nU := #[0, 0, P.rd.nW + (if g == 0 then xi.k * (xi.m / 2 ^ y.h.la) else 0)]
  let (tl, Fp, Tp) ← tl.addTrees {} {} nU aTX hb P.set.hb
  let Tp ← t2Plan Fp Tp
  -- A layer sub-proof reads at most one foreign array: the last border array of the group before.
  refuseIf (tl.ix.FT.size != (if g == 0 then 0 else 1)) "internal-g-owner-shape"
  let tl := tl.ownerIs g
  let tl ← match O with
    | none => do
      refuseIf (g != 0) "internal-g-owner-shape"
      pure tl
    | some O => do
      let last ← match O.tl.ix.TX.back? with
        | some t => pure t
        | none => throw "internal-g-owner-shape"
      let mine := tl.ix.FT.getD 0 0
      refuseIf (!t2SameShape (O.Tp.nt.getD last {}) (O.Fp.trees.getD last {}) (Tp.nt.getD mine {})
        (Fp.trees.getD mine {})) "internal-g-owner-shape"
      refuseIf (g == 0) "internal-border-count"
      let tl ← tl.borderMeans 0 (g - 1) (O.tl.pkMat.size + O.tl.ix.TX.size - 1)
      let df := samePlaceF (← O.tl.ownEntry "stream") (tl.plFor.getD 0 {})
      refuseIf (!df.isEmpty) ("internal-g-owner-place-" ++ df)
      pure tl
  refuseIf (msg ≥ 2 ^ 30) "hid-g-slots"
  pure { tl, Fp := Fp.trimL, Tp, nU, ns := msg, used := msg, NCL := nclOf y g, nLin,
         nBatched := nLin + tl.equationsF nX4, lamS := lamSOf y }

/-- The plans of the groups from g on, n of them. O: the plan of the group before g. -/
def plansFrom (P : Pub) : Nat → Nat → Option HPlan2 → Except String (List HPlan2)
  | 0, _, _ => pure []
  | n + 1, g, O => do
    let p ← planG P g O
    pure (p :: (← plansFrom P n (g + 1) (some p)))

/-- The plans of all layer sub-proofs. For each group but the first, planG compares the group's
record of the stream that comes in with the record of its owner, the group before. -/
def plansG (P : Pub) : Except String (Array HPlan2) := do
  pure (← plansFrom P P.y.NGr 0 none).toArray

/-- All names under which the functions of this file refuse, except the names of what they call in
other files: readsOf (layoutNames), the smallness test (Tail.names), its lookup (Forest.names) and
its list of arrays (Trees.names). -/
def planNames : List String :=
  ["internal-layout-words", "internal-weight-matrix", "internal-g-owner-shape",
   "internal-border-count", "hid-g-slots"] ++
  ["P0", "P1", "P3", "P4", "P5", "P6", "P9"].map ("internal-g-owner-place-" ++ ·)

end OnBytes.Model.Layer
