-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoEnds.lean.
The end values of the sub-proofs' lookup as one record of plain data, made by the flat function from
the rounds.

The byte-level verifier's routine for this lookup (OnBytes.Model.Forest.pad) returns a record of end
values (Heard): the
shift, the point alpha, the public factor of the padding, a list of claims on mask entries, the
state of the sumcheck over
the leaves, and the points, weights and table values from which its callers make four more claims.
This file gives such
values as a function of the public shape and of the rounds read as plain data, over any commutative
ring, on lists.

* `Ends K`: the record. Points are listed as the byte-level verifier lists them: the top coordinate
first.
* `endsOf h lm jLK rs`: the record at the shape h, the lookup's first slot jLK and the rounds rs.
Every field is read off
  the flat trace `Fo.forTrace` and the public numbers `Fo.forN`. (lm enters `Fo.forN` only through
    the places of the
  planes' cells, which no field of this record reads.)
* `Ends.rows`: the claims on mask entries alone, in the order of the run: the tie's steps, the key
levels, the table's
  levels, the bits' sumcheck.
* `ends_r16`: the flat function's rows are this record's rows, each group in the reverse order, with
the three rows on
  the planes around the bits' row: rowEnd before it, rowBitE and rowNum behind it.
  `ends_leaves`: the row of the sumcheck over the leaves, written from the
    record's fields.
* `evalL`, `rowRes`, `muOf`: the value of a sparse form and of a row at given entries.

Not claimed here: that the byte-level routine returns these values (stated in
OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean; its proof is hcOut2,
OnBytes/Tie/Pv/Lookup/Forest/FoPadAll.lean).

-/
import Cb.Pv.Lookup.Forest.FoNat
import OnBytes.Tie.Pv.Lookup.Forest.FoV

set_option autoImplicit false

namespace Fo
open TwV FoNums

/-- The end values of one lookup. -/
structure Ends (K : Type) where
  /-- the shift; 0 if there is one call -/
  theta : K
  /-- the point at which the two products are compared -/
  alpha : K
  /-- the public factor of the padding -/
  a : K
  /-- the claims of the tie's steps, the first step first -/
  tieRows : List (SRow Pl K)
  /-- the claims of the key levels, level 0 first -/
  keyRows : List (SRow Pl K)
  /-- the claims of the table's levels, level 0 first -/
  tabRows : List (SRow Pl K)
  /-- the claim of the bits' sumcheck -/
  bitU : SRow Pl K
  /-- the sumcheck over the leaves: its factor, its last value, its challenges by round -/
  lvEps : K
  lvFin : K
  lvXs : List K
  /-- its variables by round: the coordinate of the equality point, and the degree -/
  lvZs : List K
  lvDg : List ℕ
  /-- the form on mask entries and the public target with which it was entered; its first slot -/
  lvInc : List (Pl × K)
  lvTg : K
  lvFirst : ℕ
  /-- the factor of the planes' value at the leaves' point -/
  leavesA : K
  /-- the slot of the planes' shown value in the bits' sumcheck; that value; the factor of its mask
  entry (the sumcheck's last challenge) -/
  sBit : ℕ
  bitV : K
  bitBe : K
  /-- the key side's point: the place in a tree; the tree's number -/
  zx : List K
  zy : List K
  /-- the weight of each call's trees -/
  e : List K
  /-- the hidden value of the key side's leaves: a form on mask entries and a constant -/
  cEndF : List (Pl × K)
  cEndC : K
  /-- the same form with the other sign: the value is cEndC less cEndInc at the mask row -/
  cEndInc : List (Pl × K)
  /-- the two points at which the planes are read -/
  zb0 : List K
  zb1 : List K
  /-- each call's table at the leaves' point -/
  tT : List K
  /-- the point at which each call's key vector is read -/
  zk : List (List K)

/-- The claims that read mask entries alone, in the order of the run. -/
def Ends.rows {K : Type} (En : Ends K) : List (SRow Pl K) :=
  En.tieRows ++ En.keyRows ++ En.tabRows ++ [En.bitU]

section
variable {K : Type} [CommRing K]

/-- The number of a mask entry's place. -/
def slotNo : Pl → ℕ
  | .mask j => j
  | _ => 0

/-- The end values, off the flat trace. -/
def endsOf (h : Sh) (lm jLK : ℕ) (rs : Rounds K) : Ends K :=
  let N := forN h lm jLK rs
  let t := forTrace h lm jLK rs
  let pnt := pntK N t
  let gam := byVar N.oE t.cls.xs
  { theta := thetaOf h rs
    alpha := t.lam
    a := fac N t.lam
    tieRows := (tieRowsR N t.lam t.tie.reverse).reverse
    keyRows := (lvRowsR N.ledK 0 (fK N t) t.keys.reverse).reverse
    tabRows := (lvRowsR N.ledT N.w (incT0 N t) t.tabl.reverse).reverse
    bitU := rowBitU N t
    lvEps := t.cls.eps
    lvFin := t.cls.fin
    lvXs := t.cls.xs
    lvZs := inRounds N.oE (pntTop N.oT t.join t.tabl.reverse)
    lvDg := dgE N
    lvInc := incTop N.ledT (incT0 N t) t.tabl.reverse
    lvTg := tgTop (tgT0 N t) t.tabl.reverse
    lvFirst := jLK + (S h).fEnd
    leavesA := ((List.range (2 ^ N.d)).map fun r => eqN (gam.drop N.w) r * (t.lam - 1 - N.tab
        r)).sum
    sBit := slotNo (N.ledB.sh 0)
    bitV := t.bits.v 0
    bitBe := t.bits.be
    zx := (pnt.drop h.rK).reverse
    zy := (pnt.take h.rK).reverse
    e := (List.range h.NC).map fun c =>
      (((List.range h.NT).filter fun y => co h y = c).map fun y => eqN (pnt.take h.rK) y).sum
    cEndF := scale (-1) (incTop N.ledK (fK N t) t.keys.reverse)
    cEndC := t.kT
    cEndInc := incTop N.ledK (fK N t) t.keys.reverse
    zb0 := gam.reverse
    zb1 := (byVar N.oB t.bits.xs).reverse
    tT := (List.range h.NC).map fun c =>
      ((List.range (2 ^ h.kT)).map fun r =>
        eqN ((gam.drop (FoNums.w + h.cK)).take h.kT) r * N.tab (r * 2 ^ h.cK + c)).sum -
          (c : K) * thetaOf h rs
    zk := (List.range h.NC).map fun c => (pnt.drop h.rK ++ pnt.take (io h c)).reverse }

/-- The flat function's rows, from the record's. -/
theorem ends_r16 (h : Sh) (lm jLK : ℕ) (rs : Rounds K) :
    r16 (forN h lm jLK rs) (forTrace h lm jLK rs) =
      (endsOf h lm jLK rs).tieRows.reverse ++ ((endsOf h lm jLK rs).keyRows.reverse ++
        (((endsOf h lm jLK rs).tabRows.reverse ++
          [rowEnd (forN h lm jLK rs) (forTrace h lm jLK rs), (endsOf h lm jLK rs).bitU,
            rowBitE (forN h lm jLK rs) (forTrace h lm jLK rs)]) ++ [rowNum (forN h lm jLK rs)])) :=
                by
  unfold endsOf r16
  simp only [List.reverse_reverse]

/-- The row of the sumcheck over the leaves, from the record's fields. -/
theorem ends_leaves (h : Sh) (lm jLK : ℕ) (rs : Rounds K) :
    rowEnd (forN h lm jLK rs) (forTrace h lm jLK rs) =
      ⟨hide (forN h lm jLK rs).ledE (endsOf h lm jLK rs).lvDg (endsOf h lm jLK rs).lvXs ++
          scale (endsOf h lm jLK rs).lvEps (endsOf h lm jLK rs).lvInc ++
          scale ((endsOf h lm jLK rs).lvEps * (endsOf h lm jLK rs).leavesA)
            (bitsForm (forN h lm jLK rs) (endsOf h lm jLK rs).zb0.reverse),
        (endsOf h lm jLK rs).lvFin - (endsOf h lm jLK rs).lvEps * 1⟩ := by
  unfold endsOf rowEnd
  simp only [List.reverse_reverse]

/-- The value of a sparse form at given entries. -/
def evalL {P : Type} (μ : P → K) (cf : List (P × K)) : K := (cf.map fun pc => pc.2 * μ pc.1).sum

/-- The value of a row: its form at the entries, less its target. -/
def rowRes {P : Type} (μ : P → K) (r : SRow P K) : K := evalL μ r.cf - r.tg

/-- The entries in which the mask row is given and every other place reads 0. -/
def muOf (mask : ℕ → K) : Pl → K
  | .mask j => mask j
  | _ => 0

end
end Fo
