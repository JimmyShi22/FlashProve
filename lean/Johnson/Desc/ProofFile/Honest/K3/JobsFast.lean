-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/JobsFast.lean: the honest side of the kind "lookup" (K3): the
summands of its masked sumchecks, computed by folding tables. Definitions with code; no theorem.

Terms. Honest/K3/GLOSSARY.md ("job, summand", "filling", "stage", "points"). In this file:
Honest/K3/Stages.lean has a letter `LookJobs`: for each stage of a lookup's row that is a masked
sumcheck, the three functions that `SumJob` (Honest/Sum.lean) asks of a caller: the summand's round
polynomial, the polynomial in the further variable Y, the true end values. `fastJobs f row` fills
that letter on the program's elements (OnBytes/Field/Ext.lean), with arrays. A round over m
variables costs a small multiple of 2 ^ m products, beside the making of the tables (see "Cost").

What is defined.
  1 `at0`, `bindAt`, `Cube`, `Cube.pos`, `Cube.bind`, `bindAll`, `coord`: a table on a cube; one bit
    bound at a challenge.
  2 `prodRound`, `prodEnds`, `mulY`: one routine for all sumchecks with variables: the summand kappa
    + A B under equality weights, its variables bound in a given order.
  3 `up`, `upN`, `Src`, `srcOf`: the two sides' leaves and the levels of their product trees.
  4 `Src.root`, `Src.rootsFrom`, `powerP`, `sqMulY`: the roots; the tie's powers.
  5 `noJob`, `levelJob`, `stageJob`, `fastJobs`: the stages' jobs.
  6 `cornerOf`, `rowOfFace`, `rowsFit`: the table's rows read off the verifier's own `Face.leaf`.

How indices and points lie. This is read off the verifier's text:
Johnson/Desc/First/Look/Via/Rounds.lean (`messagesV`, `leafVars`, `bitsCall`),
Johnson/Desc/First/ProdV/Level.lean (`levelVars`, `layBack`, `stepDown`),
Johnson/Desc/First/Look/K3LookupGeneral.lean (`eqPairs`).
  A table on m variables has 2 ^ m entries; variable b is bit b of an entry's number, bit 0 the
    lowest. A point lists its coordinates the highest bit first: the coordinate of bit b is z[m - 1
    - b]. An order lists bits: round l binds bit order[l].
  A level of a product tree: entry x of the level with m variables is entry x times entry x + 2 ^ m
    of the level with m + 1 variables: the new bit is the highest. The first end value (the
    verifier's vL, "the level below at (0, r)") belongs to the lower half, the second (vR) to the
    upper half.
  The table side's leaf of row u and plane j has the number u 2 ^ mu + j: the plane's bits are the
    low ones. Its value is 1 + bit (alpha - 1 - row). A plane from `planes` on is not real: its bits
    count as 0 whatever the input says, so its leaves and its root are 1.
  The key side's leaf x of part i is alpha - key.
  The leaves' and the bits' sumchecks bind the highest bit first: round j binds bit mu + d - 1 - j,
    whose coordinate is coordinate j of the point.

What a round polynomial is here. With the bits of the rounds in front at their challenges, the
round's own bit at T, and x over the corners of the bits still free: the sum over x of (the equality
weight of x at the free bits' coordinates of z) times (kappa + A B). No equality factor of the
round's own bit or of an earlier one is in it: the verifier sums a round's polynomial q as (1 - z)
q(0) + z q(1) at the bit's own coordinate z, and goes on from q at the challenge. The weights of the
free bits add up to 1, so kappa enters the constant coefficient as it is.

The tie. Z is the product of all parts' roots; G_j the root of plane j; with w planes P_(w - 1) :=
G_(w - 1) and P_s := P_(s + 1) ^ 2 G_s. Step 0 has the end values Z, P_1, G_0 and the end term Z - a
P_1 ^ 2 G_0, a the face's public factor; step s from 1 on has P_(s + 1), G_s and the end term P_(s +
1) ^ 2 G_s. The parts' step i has part i's root and the product of the later parts' roots. The
polynomial in Y is the end term at (true value + Y times mask entry), all coefficients.

Cost. Nothing is kept from one call to the next: the functions of `SumJob` are handed the input and
the challenges anew at every move, and the tables depend on the shift and on alpha. So every call
makes its side's leaves (2 ^ v reads of a key, or 2 ^ (mu + d) of a bit and 2 ^ d of a row) and the
tree's levels down to the one it needs (fewer products than leaves), binds the rounds in front again
(fewer than 2 ^ (m + 2) folds) and then sums. A tie's call makes both sides' trees. There is one
measure, and a rough one: Honest/K3/JobsFastAtSize.lean [not in this library] compiled in about five
minutes (Lean's evaluator, one thread); it goes five times through all calls of a lookup with 2 ^ 12
keys and 2 ^ 7 rows in 32 planes, each time beside another prover's run: so a minute for a lookup at
most; these calls alone were not timed. By reckoning, not by a run: the cost grows with the number
of keys times the square of the number of their bits, so at a lookup with 2 ^ 22 keys or more this
filling is out of the evaluator's reach. For that the tables would have to be handed on from move to
move, and runs of equal padding keys folded in closed form; neither is done here.

Follows. OnBytes/Model/TestLookProver.lean, a prover for a lookup without masks that goes round by
round through one state: `up` is its `up`; the number of an entry's partner in `at0` and the use of
`eqTab` on the free coordinates are those of its `roundP`. That file is not imported. Other than
there, the coefficients are summed directly (no value at 2, no division by 2), and bits are named,
not coordinates.

Imported. Honest/Sum.lean lies beneath this file.

Limits. Nothing in this file is compared with the verifier's text or with a specification:
Honest/K3/JobsFastGuards.lean [not in this library] and Honest/K3/JobsFastAtSize.lean
[not in this library] test numbers. No function rejects: an entry beyond a table's end, a coordinate
beyond a point's end and a mask entry beyond the list's end count as 0; challenges beyond the
order's length are dropped; an order that names a bit twice, or a bit that is not free, still halves
the tables, and what comes out then means nothing. `prodRound` with as many challenges as variables,
or more, means nothing. At a stage that sends nothing the three functions give the empty list. `row`
is a letter: that it is the table of which `Face.leaf` is the extension is what `rowsFit` tests at
one shift and one alpha, on the corners alone. That keys and bits fit each other is not tested in
this file: at other data the same code runs and the sums are other sums.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Stages

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E addE subE mulE zeroE oneE foldPairE)

namespace Fast

/-! ## 1 A table on a cube -/

/-- Among the entries whose bit at position p is 0: the number of the i-th. Its partner, with that
bit 1, is 2 ^ p further on. -/
def at0 (p i : Nat) : Nat := i / 2 ^ p * 2 ^ (p + 1) + i % 2 ^ p

/-- **One bit bound**: the bit at position p of a table's numbers is set to r: entry i of the result
is a + r (b - a), a the i-th entry with that bit 0, b its partner. Half as many entries; the bits
above p move down by one position. -/
def bindAt (p : Nat) (r : E) (t : Array E) : Array E :=
  let s := 2 ^ p
  (Array.range (t.size / 2)).map fun i =>
    foldPairE (t.getD (at0 p i) zeroE) (t.getD (at0 p i + s) zeroE) r

/-- Tables on the same cube, some of whose bits are bound already. -/
structure Cube where
  /-- the bits that are still free, in rising order -/
  free : List Nat
  tabs : List (Array E)

/-- The position of bit b in the tables' numbers: how many free bits lie below it. -/
def Cube.pos (c : Cube) (b : Nat) : Nat := (c.free.filter (· < b)).length

/-- Bit b bound at r in all tables. -/
def Cube.bind (c : Cube) (b : Nat) (r : E) : Cube :=
  { free := c.free.filter (· != b), tabs := c.tabs.map (bindAt (c.pos b) r) }

/-- Tables on m bits, with the bits of the first rounds bound at their challenges. -/
def bindAll (m : Nat) (order : List Nat) (tabs : List (Array E)) (rs : List E) : Cube :=
  (order.zip rs).foldl (fun c x => c.bind x.1 x.2) ⟨List.range m, tabs⟩

/-- Bit b's coordinate of a point of m coordinates: the highest bit first. -/
def coord (m : Nat) (z : Array E) (b : Nat) : E := z.getD (m - 1 - b) zeroE

/-! ## 2 The summand kappa + A B under equality weights -/

/-- **The round polynomial**, three coefficients, lowest first. Here m is the number of variables;
order gives the bit that each round binds; z is the point of the equality weights; A and B are
tables of 2 ^ m entries; rs are the challenges of the rounds in front. -/
def prodRound (kappa : E) (m : Nat) (order : List Nat) (z A B : Array E) (rs : List E) : List E :=
  let c := bindAll m order [A, B] rs
  let b := order.getD rs.length 0
  let p := c.pos b
  let s := 2 ^ p
  let ta := c.tabs.getD 0 #[]
  let tb := c.tabs.getD 1 #[]
  let w := OnBytes.Model.eqTab ((c.free.filter (· != b)).reverse.map (coord m z)).toArray
  let out := (Array.range w.size).foldl
    (fun (acc : E × E × E) i =>
      let a0 := ta.getD (at0 p i) zeroE
      let a1 := subE (ta.getD (at0 p i + s) zeroE) a0
      let b0 := tb.getD (at0 p i) zeroE
      let b1 := subE (tb.getD (at0 p i + s) zeroE) b0
      let wi := w.getD i zeroE
      (addE acc.1 (mulE wi (addE kappa (mulE a0 b0))),
       addE acc.2.1 (mulE wi (addE (mulE a0 b1) (mulE a1 b0))),
       addE acc.2.2 (mulE wi (mulE a1 b1))))
    (zeroE, zeroE, zeroE)
  [out.1, out.2.1, out.2.2]

/-- The tables' values at the point of all challenges, in the tables' order. -/
def prodEnds (m : Nat) (order : List Nat) (tabs : List (Array E)) (xs : List E) : List E :=
  (bindAll m order tabs xs).tabs.map (·.getD 0 zeroE)

/-- kappa + (a + Y ma) (b + Y mb), three coefficients. -/
def mulY (kappa a b ma mb : E) : List E :=
  [addE kappa (mulE a b), addE (mulE a mb) (mulE ma b), mulE ma mb]

/-! ## 3 Leaves and levels -/

/-- The level above a level of a product tree: entry x is entry x times entry x + half the size. -/
def up (a : Array E) : Array E :=
  let h := a.size / 2
  (Array.range h).map fun x => mulE (a.getD x zeroE) (a.getD (h + x) zeroE)

/-- n levels up. -/
def upN : Nat → Array E → Array E
  | 0, a => a
  | n + 1, a => upN n (up a)

/-- **The tables of a lookup at a shift and an alpha**, each made when it is asked for. -/
structure Src where
  /-- part i's key tree: the level with m variables; m := the part's number of bits: the leaves -/
  keyLvl : Nat → Nat → Array E
  /-- the table side's level number l: mu + l variables; l := d: the leaves -/
  tabLvl : Nat → Array E
  /-- the bits, by the leaf's number -/
  bitTab : Unit → Array E
  /-- alpha - 1 - row, by the leaf's number -/
  facTab : Unit → Array E

/-- These tables, of the face's numbers, the table's rows (of the shift and a row's number), the
input, the shift and alpha. -/
def srcOf (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E) : Src :=
  let pl := 2 ^ f.mu
  let bitTab : Unit → Array E := fun _ =>
    (Array.range (2 ^ (f.mu + f.d))).map fun X =>
      if X % pl < f.planes then w.bit (X / pl) (X % pl) else zeroE
  let facTab : Unit → Array E := fun _ =>
    let R := (Array.range (2 ^ f.d)).map fun u => subE (subE alpha oneE) (row theta u)
    (Array.range (2 ^ (f.mu + f.d))).map fun X => R.getD (X / pl) zeroE
  { keyLvl := fun i m =>
      let v := f.parts.getD i 0
      upN (v - m) ((Array.range (2 ^ v)).map fun x => subE alpha (w.key theta i x))
    tabLvl := fun l =>
      upN (f.d - l) (Array.zipWith (fun b a => addE oneE (mulE b a)) (bitTab ()) (facTab ()))
    bitTab := bitTab
    facTab := facTab }

/-! ## 4 Roots and the tie's powers -/

/-- Part i's root. -/
def Src.root (S : Src) (i : Nat) : E := (S.keyLvl i 0).getD 0 zeroE

/-- The product of the roots of the parts from number i on, of n parts. -/
def Src.rootsFrom (S : Src) (n i : Nat) : E :=
  ((List.range (n - i)).map fun k => S.root (i + k)).foldl mulE oneE

/-- P_s out of the roots g of w planes: P_(w - 1) := g[w - 1]; P_s := P_(s + 1) ^ 2 g[s]. -/
def powerP (g : Array E) (w s : Nat) : E :=
  (List.range (w - 1 - s)).foldl
    (fun p i => mulE (mulE p p) (g.getD (w - 2 - i) zeroE)) (g.getD (w - 1) zeroE)

/-- (p + Y mp) ^ 2 (g + Y mg), four coefficients. -/
def sqMulY (p g mp mg : E) : List E :=
  let pp := mulE p p
  let pm := mulE p mp
  let mm := mulE mp mp
  [mulE pp g, addE (mulE (addE pm pm) g) (mulE pp mg), addE (mulE mm g) (mulE (addE pm pm) mg),
   mulE mm mg]

/-! ## 5 The stages' jobs -/

/-- A stage at which nothing is summed. -/
def noJob : StageJob Hidden :=
  { round := fun _ _ _ => [], inY := fun _ _ _ _ => [], ends := fun _ _ _ => [] }

/-- **A level of a product tree**: m variables; the order; the level below (2 ^ (m + 1) entries);
the point. The summand is lower half times upper half. -/
def levelJob (m : Nat) (order : List Nat) (next : Hidden → Pts → Array E) (z : Pts → Array E) :
    StageJob Hidden :=
  let halves (w : Hidden) (p : Pts) : Array E × Array E :=
    let n := next w p
    (n.extract 0 (2 ^ m), n.extract (2 ^ m) (2 ^ (m + 1)))
  { round := fun w p rs =>
      let h := halves w p
      prodRound zeroE m order (z p) h.1 h.2 rs
    ends := fun w p xs =>
      let h := halves w p
      prodEnds m order [h.1, h.2] xs
    inY := fun w p xs mk =>
      let h := halves w p
      let e := prodEnds m order [h.1, h.2] xs
      mulY zeroE (e.getD 0 zeroE) (e.getD 1 zeroE) (mk.getD 0 zeroE) (mk.getD 1 zeroE) }

/-- **A stage's job.** -/
def stageJob (f : LFace) (row : E → Nat → E) : Stage → StageJob Hidden :=
  let src (w : Hidden) (p : Pts) : Src := srcOf f row w p.theta p.alpha
  let m := f.mu + f.d
  let top := OnBytes.Model.orderDefault m
  fun
  | .tie 0 =>
    let vals (w : Hidden) (p : Pts) : E × E × E :=
      let S := src w p
      let g := S.tabLvl 0
      (S.rootsFrom f.parts.length 0, powerP g f.planes 1, g.getD 0 zeroE)
    { round := fun _ _ _ => []
      ends := fun w p _ =>
        let v := vals w p
        [v.1, v.2.1, v.2.2]
      inY := fun w p _ mk =>
        let v := vals w p
        let a := f.factor p.theta p.alpha
        addL [v.1, mk.getD 0 zeroE]
          ((sqMulY v.2.1 v.2.2 (mk.getD 1 zeroE) (mk.getD 2 zeroE)).map fun x =>
            subE zeroE (mulE a x)) }
  | .tie (s + 1) =>
    let vals (w : Hidden) (p : Pts) : E × E :=
      let g := (src w p).tabLvl 0
      (powerP g f.planes (s + 2), g.getD (s + 1) zeroE)
    { round := fun _ _ _ => []
      ends := fun w p _ =>
        let v := vals w p
        [v.1, v.2]
      inY := fun w p _ mk =>
        let v := vals w p
        sqMulY v.1 v.2 (mk.getD 0 zeroE) (mk.getD 1 zeroE) }
  | .split i =>
    let vals (w : Hidden) (p : Pts) : E × E :=
      let S := src w p
      (S.root i, S.rootsFrom f.parts.length (i + 1))
    { round := fun _ _ _ => []
      ends := fun w p _ =>
        let v := vals w p
        [v.1, v.2]
      inY := fun w p _ mk =>
        let v := vals w p
        mulY zeroE v.1 v.2 (mk.getD 0 zeroE) (mk.getD 1 zeroE) }
  | .key i k =>
    levelJob k (f.orders i k) (fun w p => (src w p).keyLvl i (k + 1)) fun p => p.keyPt i k
  | .tab l =>
    levelJob (f.mu + l) (OnBytes.Model.orderDefault (f.mu + l))
      (fun w p => (src w p).tabLvl (l + 1)) fun p => p.tabPt l
  | .leaves =>
    { round := fun w p rs =>
        let S := src w p
        (prodRound oneE m top (p.tabPt f.d) (S.bitTab ()) (S.facTab ()) rs).take
          (if rs.length < f.d then 3 else 2)
      ends := fun _ _ _ => []
      inY := fun _ _ _ _ => [] }
  | .bits =>
    let tabs (w : Hidden) (p : Pts) : Array E × Array E :=
      let b := (src w p).bitTab ()
      (b, b.map fun x => subE x oneE)
    { round := fun w p rs =>
        let t := tabs w p
        prodRound zeroE m top p.zeroPt t.1 t.2 rs
      ends := fun w p xs => prodEnds m top [(tabs w p).1] xs
      inY := fun w p xs mk =>
        let b := (prodEnds m top [(tabs w p).1] xs).getD 0 zeroE
        mulY zeroE b (subE b oneE) (mk.getD 0 zeroE) (mk.getD 0 zeroE) }
  | _ => noJob

/-! ## 6 The table's rows off the verifier's own text -/

/-- The corner of row u, at plane 0, as a point of the leaves' sumcheck: mu + d coordinates, the
highest bit first. -/
def cornerOf (f : LFace) (u : Nat) : Array E :=
  (Array.range (f.mu + f.d)).map fun j =>
    if (u * 2 ^ f.mu).testBit (f.mu + f.d - 1 - j) then oneE else zeroE

/-- The table's row u at a shift, read off `Face.leaf` at alpha := 0 on that corner: leaf is alpha -
1 - row. It costs as much as `Face.leaf` does, once for each row. -/
def rowOfFace (f : LFace) (theta : E) (u : Nat) : E :=
  subE (subE zeroE oneE) (f.leaf theta zeroE (cornerOf f u))

/-- A test: at this shift and this alpha, on every row's corner, `Face.leaf` is alpha - 1 - row. -/
def rowsFit (f : LFace) (row : E → Nat → E) (theta alpha : E) : Bool :=
  (List.range (2 ^ f.d)).all fun u =>
    f.leaf theta alpha (cornerOf f u) == subE (subE alpha oneE) (row theta u)

end Fast

/-- **The summands of all stages, by folding tables.** Here f holds the lookup's numbers, and row is
the table's row, as a function of the shift and the row's number below 2 ^ d. -/
def fastJobs (f : LFace) (row : E → Nat → E) : LookJobs Hidden := ⟨Fast.stageJob f row⟩

end ProofFile.Honest.K3
