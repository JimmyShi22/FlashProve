-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysRunZ.lean: the trees of a layer sub-proof's lookup, the calls' points and the
calls' weights, the verifier's against the library's, evaluated.

The lookup of a layer sub-proof lays the keys of its calls into trees of one depth and ends at two
points: one inside a tree and one over the trees' numbers. From them it makes a point and a weight
for each call (Forest.shape in OnBytes/Model/Forest.lean; Forest.pad, callWeight in
OnBytes/Model/Look.lean). The library has one point z for the whole lookup, and reads each call's
point and weight from it (zc, wc in Inst/Model/FF/Objects.lean; the trees in
Inst/Model/FF/Index.lean). This file runs the two against each other.

Every line "#guard" is evaluated when this file is compiled, by Lean's interpreter, and the
compilation fails if the value is not true. It is a run. It is no theorem: nothing that only a guard
shows can be used in a proof. This file holds no theorem.

How the library's side is computed: the library's own definitions are evaluated as they stand, those
over a field over the integers modulo the verifier's prime (KP, valF in
Johnson/Road/FormsKeysRunP.lean). No formula of the library is copied.

The numbers. The made-up shapes hR8 and hR8c with the calls pcR8 of Johnson/Road/FormsKeysRun8.lean,
whose eight lines of calls are the library's; at hR8c the verifier's least number of columns makes
the calls 6 and 7 longer than the library's. The lines of the two shipped examples' parameter files
(linesKS, linesKF in Johnson/Road/FormsKeysRunK.lean), read by the verifier's own polLayout; at the
small one the least number of columns makes the calls 0, 5, 6 and 7 longer. dimP: the library's
sizes for the layout's shape, with the verifier's cap on a tree's depth, and with a made-up
vocabulary of 16 tokens, also at the examples; no number that is run here reads it. The two points
are made up (lookR8), of the lengths dT and rK, and the calls' points are made from them in the
letters of Forest.pad. zP: the point inside a tree, then the point over the trees' numbers.

What is run, and what is compared with what.
 Z1  the numbers of the trees: for each of the eight calls the logarithm of the number of keys
     against aC, of the number of trees against eC, the first tree against firstTree, the prefix
     against pre; the number of trees against NT, the bits of a tree's number against sg, the depth
     of a tree against Dk; the call of each tree against callOf.
 Z2  every coordinate of every call's point against zc at the point zP.
 Z3  every call's weight against wc at the point zP.
 Z4  the verifier's token point against zpos at the point zP.
 Z5  the letters and the two tests of Forest.pad hold together at the made-up lookup.
 Z2 and Z3 also at another point, zAlt, which is zP where the two depths agree.
What came out, and is held by the guards. Where no call is made longer (hR8, the full-size example):
all of it holds, for all eight calls, at the one point zP. At the two shapes where some call is made
longer (hR8c, the small example) no mark of Z1 to Z4 is true at zP. A mark of Z1 speaks of all eight
calls: the numbers of keys agree for the calls that are not made longer, as the guards on the
numbers show. At zAlt the points of the calls that are not made longer are the library's. Their
weights are the library's at hR8c; at the small example no call's weight is. Why the two differ is
not run.
 Controls at hR8: with the two points in the other order Z2 and Z3 fail for every call. With the
 point over the trees' numbers read from its other end Z2 fails for the six calls that have more
 than one tree (the two others do not read that point), and Z3 fails for seven calls: the prefix of
 call 7 is 27, in five bits 11011, which reads the same from both ends.

What stands between the two sides and is this file's own: zP, zAlt, zBad, valF, dimP.

What is not claimed. Nothing is said of any other shape. No proof is made or checked. That no point
at all serves the small example's weights is not run. Forest.pad itself, which reads messages, is
not run: lookR8 copies its line for the calls' points, and Z5 compares the copy with that line
written out again. The numbers of padding keys, the trees' products and the tables are not looked
at. The program does not import this file.
-/
import Johnson.Road.FormsKeysRunK
import Johnson.Road.FormsKeysRunP

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model.Verify (polLayout)
open OnBytes.Model.Layer (Lay Shape Heard layout readsOf)
open Inst.Model.FFSeg (Dim aC eC Dk sg NT firstTree pre zc wc zpos)

/-! ## What is evaluated -/

/-- Z1. The numbers of the lookup's trees, the verifier's against the library's: for each of the
eight calls the logarithm of the number of keys, the logarithm of the number of trees, the first
tree, the prefix; the number of trees, the bits of a tree's number, the depth of a tree; the call of
each tree. -/
def numsZ (y : Lay) (D : Dim) : List Bool :=
  let all8 (f : Fin 8 → Bool) : Bool := (List.finRange 8).all f
  [all8 fun c => ((y.cl[c.val]?).map (·.n)).getD 0 == aC D c,
   all8 fun c => y.fo.iota.getD c.val 0 == eC D c,
   all8 fun c => y.fo.first.getD c.val 0 == firstTree D c,
   all8 fun c => y.fo.first.getD c.val 0 / 2 ^ y.fo.iota.getD c.val 0 == pre D c,
   y.fo.NT == NT D, y.fo.rK == sg D, y.fo.dT == Dk D,
   (List.range y.fo.NT).all fun θ => y.fo.callOf.getD θ 0 == (Inst.Model.FFSeg.callOf D θ).val]

/-- The same numbers, written out: for each call the pairs (verifier, library) of the four numbers;
then the three pairs. -/
def rawZ (y : Lay) (D : Dim) : List (List (ℕ × ℕ)) × List (ℕ × ℕ) :=
  ((List.finRange 8).map fun c =>
    [(((y.cl[c.val]?).map (·.n)).getD 0, aC D c), (y.fo.iota.getD c.val 0, eC D c),
     (y.fo.first.getD c.val 0, firstTree D c)],
   [(y.fo.NT, NT D), (y.fo.rK, sg D), (y.fo.dT, Dk D)])

/-- Z2, call by call. The point of call c, as the lookup makes it, has as many coordinates as the
library's call has bits, and each reads as the library's zc at the point z. -/
def pointsZ (H : Heard) (D : Dim) (z : ℕ → KP) : List Bool :=
  (List.finRange 8).map fun c =>
    let p := H.fo.zk.getD c.val #[]
    p.size == aC D c && (List.range (aC D c)).all fun j => valF (p.getD j zeroE) == zc D z c j

/-- Z3, call by call. The weight of call c, as the lookup computes it from its point over the trees'
numbers, reads as the library's wc at the point z. -/
def weightsZ (y : Lay) (H : Heard) (D : Dim) (z : ℕ → KP) : List Bool :=
  (List.finRange 8).map fun c =>
    valF (Model.Forest.callWeight y.fo H.fo.zy c.val) == wc D z c

/-- Z4. The verifier's token point reads as the library's zpos at the point z. -/
def tokenZ (H : Heard) (D : Dim) (z : ℕ → KP) : Bool :=
  H.ztF.size == D.lT && (List.range D.lT).all fun j => valF (H.ztF.getD j zeroE) == zpos D z j

/-- Z5. The letters and tests of Forest.pad (OnBytes/Model/Look.lean) hold together at the made-up
lookup: the two points have dT and rK coordinates; no call has more trees than there are numbers;
each call's point is the last iota coordinates of the point over the trees' numbers followed by the
point inside a tree; each has as many coordinates as the call's record says. -/
def padZ (y : Lay) (H : Heard) : Bool :=
  let h := y.fo
  H.fo.zx.size == h.dT && H.fo.zy.size == h.rK && (h.iota.all fun i => decide (i ≤ h.rK)) &&
  H.fo.zk == ((Array.range h.NC).map fun c =>
    H.fo.zy.extract (h.rK - h.iota.getD c 0) H.fo.zy.size ++ H.fo.zx) &&
  (List.range h.NC).all fun c =>
    (H.fo.zk.getD c #[]).size == ((h.calls[c]?).map (·.n)).getD 0

/-- Another point for the library, for a layout whose trees are deeper than the library's by
g = dT - Dk: inside a tree the last Dk coordinates of the verifier's point inside a tree; over the
trees' numbers, from the end: the first g coordinates of that point, before them the last
coordinates of the verifier's point over the trees' numbers; 0 where these run out. -/
def zAlt (y : Lay) (H : Heard) (D : Dim) : ℕ → KP := fun t =>
  let g := y.fo.dT - Dk D
  if t < Dk D then valF (H.fo.zx.getD (g + t) zeroE)
  else
    let u := t - Dk D
    if sg D - g ≤ u then valF (H.fo.zx.getD (u - (sg D - g)) zeroE)
    else if sg D - g ≤ y.fo.rK + u then valF (H.fo.zy.getD (y.fo.rK + u - (sg D - g)) zeroE)
    else 0

/-- False variants of the point, for controls: 0: the two points in the other order; 1: the point
over the trees' numbers read from its other end. -/
def zBad (mode : ℕ) (H : Heard) : ℕ → KP := fun t =>
  let zx := H.fo.zx
  let zy := H.fo.zy
  if mode == 0 then
    if t < zy.size then valF (zy.getD t zeroE) else valF (zx.getD (t - zy.size) zeroE)
  else
    if t < zx.size then valF (zx.getD t zeroE)
    else valF (zy.getD (zy.size - 1 - (t - zx.size)) zeroE)

/-- All of it for a layout: Z1; Z2; Z3; Z4 and Z5; then Z2 and Z3 at the point zAlt. -/
def allZ (y : Lay) :
    Option (List Bool × List Bool × List Bool × List Bool × List Bool × List Bool) :=
  match readsOf y with
  | .error _ => none
  | .ok rd =>
    let H := heardR8 y rd 0
    let D := dimP y.h
    some (numsZ y D, pointsZ H D (zP H), weightsZ y H D (zP H), [tokenZ H D (zP H), padZ y H],
      pointsZ H D (zAlt y H D), weightsZ y H D (zAlt y H D))

/-- allZ for a shape and lines of calls. -/
def shapeZ (h : Model.Layer.Shape) (pc : List (List String)) :=
  match layout h pc with
  | .ok y => allZ y
  | .error _ => none

/-- allZ for the lines of a parameter file. -/
def kitZ (pol : ByteArray) :=
  match polLayout pol with
  | .ok x => allZ x.2
  | .error _ => none

/-- rawZ for the lines of a parameter file. -/
def kitRaw (pol : ByteArray) :=
  match polLayout pol with
  | .ok x => some (rawZ x.2 (dimP x.2.h))
  | .error _ => none

/-! ## The run -/

/- no call is made longer: all holds at the one point -/
#guard shapeZ hR8 pcR8 == some (List.replicate 8 true, List.replicate 8 true,
  List.replicate 8 true, [true, true], List.replicate 8 true, List.replicate 8 true)

/- the full-size example: the same -/
#guard kitZ (textK linesKF) == some (List.replicate 8 true, List.replicate 8 true,
  List.replicate 8 true, [true, true], List.replicate 8 true, List.replicate 8 true)

/- its numbers -/
#guard kitRaw (textK linesKF) == some
  ([[(27, 27), (1, 1), (4, 4)], [(27, 27), (1, 1), (6, 6)], [(27, 27), (1, 1), (8, 8)],
    [(28, 28), (2, 2), (0, 0)], [(27, 27), (1, 1), (10, 10)], [(27, 27), (1, 1), (12, 12)],
    [(26, 26), (0, 0), (14, 14)], [(26, 26), (0, 0), (15, 15)]],
   [(16, 16), (4, 4), (26, 26)])

/- the calls 6 and 7 are made longer -/
#guard shapeZ hR8c pcR8 == some (List.replicate 8 false, List.replicate 8 false,
  List.replicate 8 false, [false, true], [true, true, true, true, true, true, false, false],
  [true, true, true, true, true, true, false, false])

#guard (match layout hR8c pcR8 with | .ok y => some (rawZ y (dimP y.h)) | .error _ => none) == some
  ([[(12, 12), (0, 1), (8, 16)], [(12, 12), (0, 1), (9, 18)], [(12, 12), (0, 1), (10, 20)],
    [(15, 15), (3, 4), (0, 0)], [(12, 12), (0, 1), (11, 22)], [(12, 12), (0, 1), (12, 24)],
    [(12, 11), (0, 0), (13, 26)], [(12, 11), (0, 0), (14, 27)]],
   [(15, 28), (4, 5), (12, 11)])

/- the small example: the calls 0, 5, 6 and 7 are made longer -/
#guard kitZ (textK linesKS) == some (List.replicate 8 false, List.replicate 8 false,
  List.replicate 8 false, [false, true], [false, true, true, true, true, false, false, false],
  List.replicate 8 false)

#guard kitRaw (textK linesKS) == some
  ([[(20, 19), (0, 1), (2, 20)], [(20, 20), (0, 2), (3, 8)], [(20, 20), (0, 2), (4, 12)],
    [(21, 21), (1, 3), (0, 0)], [(20, 20), (0, 2), (5, 16)], [(20, 19), (0, 1), (6, 22)],
    [(20, 18), (0, 0), (7, 24)], [(20, 18), (0, 0), (8, 25)]],
   [(9, 26), (4, 5), (20, 18)])

/- the controls -/
#guard (match layout hR8 pcR8, readsOf <$> layout hR8 pcR8 with
  | .ok y, .ok (.ok rd) =>
    let H := heardR8 y rd 0
    some (pointsZ H (dimP y.h) (zBad 0 H), pointsZ H (dimP y.h) (zBad 1 H),
      weightsZ y H (dimP y.h) (zBad 0 H), weightsZ y H (dimP y.h) (zBad 1 H))
  | _, _ => none) == some (List.replicate 8 false,
    [false, false, false, false, false, false, true, true], List.replicate 8 false,
    [false, false, false, false, false, false, false, true])

end OnBytes.Road
