-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K11/Honest/Summand.lean: what an honest prover sums in the merge of the claims on the
committed weights: the summand, its round polynomials and its end value, as functions with code on
plain lists. Definitions alone; no theorem. It hangs on no form of a prover: whoever plays the
merge's masked sumcheck calls these. What the lists read as is proved beside it, in
Johnson/Desc/K11/Honest/Law/: Tables.lean (the rounds' lists against each other), Bind.lean (binding
is the equality-weighted sum), Ends.lean (the two ends against the library's `fmAt`).

The statement that is summed (docs/format/11-5-weights-in-the-table.md, "From a segment's claims to
a row on the table"). The committed matrix has 2 ^ lk columns. A claim names a unit of its rows and
has a factor for each of the unit's index groups. Each factor splits: a weight on the columns and a
weight on the rows. So the claim's value is the sum over the columns c of a(c) b(c):
  a(c)   the claim's weight on column c (`onColumns`): the verifier's own `wsEpsT` at the corner c
  b(c)   the sum over the unit's rows y of (the claim's weight on y) times the entry (y, c)
         (`rowsSummed`): the weights are the verifier's own `wsGamma` of `wsRowPart` at the scalar 1
Claim number i, from 0, is taken times x ^ i, x the element of the round that batches the claims.
The merge's sumcheck runs over the lk column bits, THE HIGHEST FIRST. In each bit a and b are lines,
so a round's polynomial has three coefficients.

  `cornerOf`                      a column as a point: 0 or 1 for each bit, the highest first
  `onColumns`, `onRows`, `rowsSummed`   the two tables of a claim
  `Term`, `termsOf`               a claim's coefficient with its two tables; all claims'
  `bindTop`, `bindAll`            a table with its highest bits at challenges
  `productRound`, `roundAt`       a round's polynomial: of one product; of all terms
  `endAt`                         the summand at all challenges: the true end value
  `claimedSum`                    the sum over all columns: what the claims' values add up to

Limits. A PREMISE ON THE LAYOUT, WHICH NOTHING HERE ASKS: `bindTop` on `onColumns` is `wsEpsT` at
the challenges, and a round's polynomial has three coefficients, only where `wsEpsT` is a line in
each coordinate. It is so at a layout in which the groups of a unit take column bits apart from each
other, all below the unit's `ncb`: then it is a product of factors each of which reads its own bits,
each bit once. (`WsLay.place`, OnBytes/Model/Weights.lean, by which a layout is made, gives each
group the next free bits, and `ncb` is their number.) At a layout in which two groups share a column
bit it need not be so. THE LIBRARY HAS THE PREMISE UNDER A NAME: `OnBytes.Road.UnitOK`
(Johnson/Road/FormsKeysWOk.lean), which asks that the bits lie side by side in the groups' order; a
like test with code is `unitOK` (Johnson/Top/H0/K11Caller/Coef.lean). Every unit of a layout that
the verifier builds has `UnitOK` (`unitOK_of_layout`, Johnson/Road/FormsKeysWLay.lean). Under it,
for a claim whose unit the layout has and which has one factor for each of the unit's groups (the
kind's test `claimFits`, Johnson/Desc/First/Fork/MergeKind.lean, asks both), `eps_multilinear`
(Johnson/Road/FormsKeysMerge.lean) says what is wanted of `wsEpsT`. `cornerOf` is
`OnBytes.Road.bitsOf` (Johnson/Road/FormsKeysWm.lean) letter for letter, typed here so that this
file's one import is the verifier's text. A claim whose unit the layout lacks has the tables 0 and
empty weights. A table whose length is no power of two is cut in the middle as it lies. The tables
have 2 ^ lk entries: these are definitions, not a program for the full size.
Nothing on any property.

-/
import OnBytes.Model.Merge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (WsLay WsClaim wsEpsT wsRowPart wsGamma powers)

/-- Column c of a matrix with 2 ^ lk columns, as a point: coordinate i is bit lk - 1 - i of c. -/
def cornerOf (lk c : Nat) : Array E :=
  Array.ofFn (n := lk) fun i => if c.testBit (lk - 1 - i.val) then oneE else zeroE

/-- A claim's weight on each column. -/
def onColumns (lay : WsLay) (cl : WsClaim) : List E :=
  (List.range (2 ^ lay.lk)).map fun c => wsEpsT lay cl (cornerOf lay.lk c)

/-- A claim's weight on each row of its unit, from the unit's first row on. -/
def onRows (lay : WsLay) (cl : WsClaim) : List E :=
  match lay.U[cl.ui]? with
  | none => []
  | some u => (wsGamma u (wsRowPart lay cl oneE) oneE).toList

/-- Column by column: the unit's rows summed under the claim's weights on them. entry: the committed
matrix, by row and column. -/
def rowsSummed (lay : WsLay) (entry : Nat → Nat → E) (cl : WsClaim) : List E :=
  let off := ((lay.U[cl.ui]?).map (·.off)).getD 0
  (List.range (2 ^ lay.lk)).map fun c =>
    (onRows lay cl).zipIdx.foldl (fun s y => addE s (mulE y.1 (entry (off + y.2) c))) zeroE

/-- One claim in the sum: its coefficient, and its two tables by column. -/
structure Term where
  coef : E
  a : List E
  b : List E

/-- All claims' terms. x: the element that batches them. -/
def termsOf (lay : WsLay) (entry : Nat → Nat → E) (x : E) (cls : List WsClaim) : List Term :=
  (cls.zip (powers x cls.length).toList).map fun y =>
    ⟨y.2, onColumns lay y.1, rowsSummed lay entry y.1⟩

/-- A table with its highest bit at r: entry j is t[j] + r (t[half + j] - t[j]). -/
def bindTop (r : E) (t : List E) : List E :=
  ((t.take (t.length / 2)).zip (t.drop (t.length / 2))).map fun y =>
    addE y.1 (mulE r (subE y.2 y.1))

/-- A table with its highest bits at rs, the first of rs at the highest. -/
def bindAll (rs : List E) (t : List E) : List E := rs.foldl (fun u r => bindTop r u) t

/-- The sum, over the lower bits, of the product of two tables as polynomials in the highest bit:
three coefficients, the lowest first. -/
def productRound (a b : List E) : List E :=
  let ha := (a.take (a.length / 2)).zip (a.drop (a.length / 2))
  let hb := (b.take (b.length / 2)).zip (b.drop (b.length / 2))
  (ha.zip hb).foldl
    (fun g y =>
      let da := subE y.1.2 y.1.1
      let db := subE y.2.2 y.2.1
      [addE (g.getD 0 zeroE) (mulE y.1.1 y.2.1),
       addE (g.getD 1 zeroE) (addE (mulE y.1.1 db) (mulE da y.2.1)),
       addE (g.getD 2 zeroE) (mulE da db)])
    [zeroE, zeroE, zeroE]

/-- **The summand's round polynomial** in the next column bit: rs: the challenges of the bits in
front. -/
def roundAt (ts : List Term) (rs : List E) : List E :=
  ts.foldl
    (fun g t =>
      let q := productRound (bindAll rs t.a) (bindAll rs t.b)
      (List.range 3).map fun i => addE (g.getD i zeroE) (mulE t.coef (q.getD i zeroE)))
    [zeroE, zeroE, zeroE]

/-- **The summand at all challenges.** -/
def endAt (ts : List Term) (rs : List E) : E :=
  ts.foldl
    (fun s t =>
      addE s (mulE t.coef (mulE ((bindAll rs t.a).headD zeroE) ((bindAll rs t.b).headD zeroE))))
    zeroE

/-- The sum of the summand over all columns. -/
def claimedSum (ts : List Term) : E :=
  ts.foldl
    (fun s t => addE s (mulE t.coef ((t.a.zip t.b).foldl (fun u y => addE u (mulE y.1 y.2)) zeroE)))
    zeroE

end Johnson.Desc.First.ForkMerge.Honest
