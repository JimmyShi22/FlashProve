-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Shape/HeardOps.lean: the shape of what a lookup's hearing returns,
as code: which slots each row names, in order; the open sumcheck's first slot, degrees and start
form; the key form's slots; the sizes of the points; the numbers of the three owed claims. Made of
the lookup's public numbers, the ledger's count of slots and the length of its list of owed claims.
Definitions; nothing is proved.

Terms. Honest/K3/GLOSSARY.md: see there hearing, heard structure, form, slot, row, sumcheck, tie,
key tree and face. In this file: a form's shape is `AffSh` (Johnson/Desc/First/Shape/Parts.lean).


What is defined. The code mirrors the hearing's text (Johnson/Desc/First/Look/Via/Rounds.lean)
routine by routine, with a form's shape in a form's stead and a size in a point's:
  `sumAt k n C`: a masked sumcheck with end values at the count n, given the form C: the first slot
    of its end values; its row; the count behind.
  `tieSh`, `partsSh`, `turnSh`, `runSh`, `keysSh`, `joinSh`: the pieces.
  `heardVSh f n`: what `messagesV f` returns, from the count n.
  `lookHeardSh h n o`: the shape (`HeardAll`, Johnson/Desc/First/Shape/Tail.lean) of what the seated
    hearing returns at the shape h.
Helpers: `noSh`, `slotSh`, `tieStep`, `HeardVSh`.

Users. Honest/K3/Shape/HeardWalk.lean, Honest/K3/Shape/HeardGuards.lean [not in this library] and
Honest/K3/Law/Thread/LedNumbers.lean import this file.

Limits. That the hearing returns just this is not shown here. Shown in:
Honest/K3/Shape/HeardTop.lean (`hearVia_heard`: of `lookHeardSh`), conditional on the hearing's
return, on the ledger in front having its arrays at their size, and on the parameters making the
shape; and Honest/K3/Shape/HeardWalk.lean (`messagesV_out`: of `heardVSh`), conditional on the
return, on that size, and on the face having a part of keys. Evaluated in: HeardGuards.lean
[not in this library], at synthetic shapes.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Shape.Ops
import Johnson.Desc.First.Shape.Tail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Shape
open OnBytes (zeroE)
open OnBytes.Model (orderDefault)
open VerifiableInference.Desc.First.Shape (AffSh rowFormSh PscSh HeardAll)
open VerifiableInference.Desc.Part (MaskedSum.Call MaskedSum.ownSlots)
open VerifiableInference.Desc.First.ProdV (levelVars levelEnds)
open VerifiableInference.Desc.K3 (Face noVar leafVars bitsCall faceOf)

/-- The shape of a form without a slot. It has the text of the library's `Kinds.Head.Shape.noTerm`
(Johnson/Desc/K6/Shape/Arith.lean); the two are not tied. -/
def noSh : AffSh := AffSh.mk [] []

/-- The shape of the form that names slot j alone. It has the text, and the short name, of the
library's `Kinds.Head.Shape.slotSh` (the same file); the two are not tied. -/
def slotSh (j : Nat) : AffSh := AffSh.mk [] [j]

/-- **A masked sumcheck with end values**, at the count n, given the form C: its end values' first
slot; its row; the count behind. -/
def sumAt (k : MaskedSum.Call) (n : Nat) (C : AffSh) : Nat × AffSh × Nat :=
  (n + MaskedSum.ownSlots k.all, rowFormSh n (MaskedSum.ownSlots k.all) C noSh,
    n + MaskedSum.ownSlots k.all + k.endsN)

/-- One further step of the tie. Here s holds the rows, the slot that is squared on, the planes'
slots and the count. -/
def tieStep (s : List AffSh × Nat × List Nat × Nat) : List AffSh × Nat × List Nat × Nat :=
  let y := sumAt (noVar 3 2) s.2.2.2 (slotSh s.2.1)
  (s.1 ++ [y.2.1], y.1, s.2.2.1 ++ [y.1 + 1], y.2.2)

/-- The tie at w planes, from the count n: the rows; the slot of Z; the planes' slots; the count
behind. -/
def tieSh (w n : Nat) : List AffSh × Nat × List Nat × Nat :=
  let x := sumAt (noVar 3 3) n noSh
  let s := (List.range (w - 2)).foldl (fun s _ => tieStep s) ([x.2.1], x.1 + 1, [x.1 + 2], x.2.2)
  (s.1, x.1, s.2.2.1 ++ [s.2.1], s.2.2.2)

/-- From the product of the parts' roots to each: the rows; the roots' forms; the count behind. -/
def partsSh : Nat → List AffSh → AffSh → Nat → List AffSh × List AffSh × Nat
  | 0, rows, C, n => (rows, [C], n)
  | k + 1, rows, C, n =>
    let w := sumAt (noVar 2 2) n C
    let x := partsSh k (rows ++ [w.2.1]) (slotSh (w.1 + 1)) w.2.2
    (x.1, slotSh w.1 :: x.2.1, x.2.2)

/-- One level and the step down. Here c holds the rows, the point's size and the form. -/
def turnSh (order : List Nat) (m : Nat) (c : List AffSh × Nat × AffSh) (n : Nat) :
    (List AffSh × Nat × AffSh) × Nat :=
  let y := sumAt { lead := 0, vs := levelVars 0 #[] order, ends := some levelEnds } n c.2.2
  ((c.1 ++ [y.2.1], 1 + m, AffSh.mk [] [y.1, y.1 + 1]), y.2.2)

/-- A run of levels. -/
def runSh (m0 : Nat) (orders : Nat → List Nat) (l : List Nat) (c : List AffSh × Nat × AffSh)
    (n : Nat) : (List AffSh × Nat × AffSh) × Nat :=
  l.foldl (fun s i => turnSh (orders (m0 + i)) (m0 + i) s.1 s.2) (c, n)

/-- The parts' key trees: the rows; for each part its last point's size and its form; the count. -/
def keysSh (f : Face) : List (Nat × Nat) → List AffSh → List AffSh → Nat →
    List AffSh × List (Nat × AffSh) × Nat
  | x :: xs, C :: Cs, rows, n =>
    let k := runSh 0 (f.orders x.2) (List.range x.1) (rows, 0, C) n
    let y := keysSh f xs Cs k.1.1 k.2
    (y.1, (k.1.2.1, k.1.2.2) :: y.2.1, y.2.2)
  | _, _, rows, n => (rows, [], n)

/-- The one claim on the planes' roots. -/
def joinSh (f : Face) (sG : List Nat) : AffSh :=
  (List.range (2 ^ f.mu)).foldl
    (fun c j => if j < f.planes then c.append (slotSh (sG.getD j 0)) else c.append noSh) noSh

/-- What the hearing returns, as a shape. -/
structure HeardVSh where
  rows : List AffSh
  /-- The open sumcheck: its first slot; its start form -/
  leavesFirst : Nat
  leavesStart : AffSh
  sBit : Nat
  keys : List (Nat × AffSh)
  deriving Repr, DecidableEq

/-- **What `messagesV f` returns**, from the count n. -/
def heardVSh (f : Face) (n : Nat) : HeardVSh :=
  let t := tieSh f.planes n
  let p := partsSh (f.parts.length - 1) t.1 (slotSh t.2.1) t.2.2.2
  let k := keysSh f f.parts.zipIdx p.2.1 p.1 p.2.2
  let T := runSh f.mu orderDefault (List.range f.d) (k.1, f.mu, joinSh f t.2.2.1) k.2.2
  let n5 := T.2 + MaskedSum.ownSlots (leafVars f #[])
  let b := sumAt (bitsCall (List.replicate (f.mu + f.d) zeroE)) n5 noSh
  { rows := T.1.1 ++ [b.2.1], leavesFirst := T.2, leavesStart := T.1.2.2, sBit := b.1
    keys := k.2.1 }

/-- **The shape of what the seated hearing returns at the shape h**, from the count n and o owed
claims. `headD (0, noSh)` is a pad on public data: the face of a shape has one part of keys, so the
list has one entry; the seated hearing returns at one key alone. The three sizes zx, zy, zk are
written as the library's law on the size of a cut gives them, not simplified. -/
def lookHeardSh (h : OnBytes.Model.Forest.Shape) (n o : Nat) : HeardAll :=
  let f := faceOf h
  let g := heardVSh f n
  let key := g.keys.headD (0, noSh)
  let zx := min h.dT key.1 - 0
  let zy := min key.1 key.1 - h.dT
  { shape := h, rows := g.rows
    leaves := PscSh.mk false true ((List.range (f.mu + f.d)).map fun j => if j < f.d then 3 else 2)
      (f.mu + f.d) g.leavesFirst g.leavesStart false
    sBit := g.sBit, zx := zx, zy := zy, e := h.NC, cEnd := key.2, zb0 := f.mu + f.d
    zb1 := f.mu + f.d, tT := h.calls.size
    zk := (List.range h.NC).map fun c => (min zy zy - (h.rK - h.iota.getD c 0)) + zx
    owedObjects := o, owedPlanes := o + 1, owedJoin := o + 2 }

end ProofFile.Honest.K3.Shape
