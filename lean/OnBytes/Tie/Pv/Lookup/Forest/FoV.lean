-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoV.lean.
The verifier of the sub-proofs' lookup as a flat, computable function on plain data.

The lookup inside a sub-proof (OnBytes.Model.Forest.pad) joins several calls of unequal size by a
drawn shift, cuts their key vectors into trees, and binds the variables of its sumchecks in orders
of its own. This file gives what its verifier hands on as a function of the public shape and of
the rounds (for each round the scalars sent and the elements drawn): a list of sparse linear rows
on the mask row's entries, the cells of the planes' matrix and the calls' keys.

The function is `TwV.traceOfFlat` and the rows of `TwV.rowsOfTrace`, unchanged, at the numbers of
`FoNums`, which reads them off the byte-level verifier's own record `Forest.Shape`. No number is
typed here. New beside TwV:

* The shift's draw stands before the chain (one round, if there are several calls). The table, the
  rows of the padding and the keys' constants depend on it: `numsF h lm jLK θ`.
* A key is an entry plus a constant: key i of call c, plus c θ. `TwV.rowKey` knows an entry or a
  constant. `rowKeyF` is that row with the shift's share moved into the target.
* For a number c from the number of calls on, the planes' matrix has no cell. Such a bit has the
  place `Pl.zero`, which a reading is to take as 0: a premise wherever a statement needs it.
* `Pl`: entry j of the mask row (counted from 0, the lookup's first slot included), a cell of the
  planes' matrix, key i of call c.
* `planF`: how many scalars each round sends and how many elements it draws; `cut` cuts two flat
  lists into rounds.

The places of the mask entries are those of `TwNums`, made total by its clamp: a name that a
sumcheck does not have goes to its constant. No place that is read changes by that.

Main definitions: Pl, ledF, tabF, numsF, rows16, pntK, shiftShare, rowKeyF, scRounds, planF, cut,
thetaOf, afterShift, forN, forTrace, forV. One law: rows_split.

Not claimed here: that the byte-level verifier hands on these rows. No statement in this file or in
what it imports speaks of forV, rowKeyF, shiftShare or cut: what is stated of the typed verifier
(Fo.hcOut1, OnBytes/Tie/Pv/Lookup/Forest/FoRead.lean) speaks of rows16 and of the masked claim on
the keys. Its premise leaves out numsF's two fields on the keys, kAt and kC (`noKey`,
Cb/Pv/Lookup/Forest/FoNat.lean): these two are tied to no verifier either.

-/
import Cb.Pv.Lookup.Out.TwV
import OnBytes.Tie.Pv.Lookup.Port.FoNums

set_option autoImplicit false

namespace Fo
open TwV FoNums TwNums TwNums.Sizes

/-- The places that the lookup's end claims read. -/
inductive Pl where
  /-- entry j of the mask row -/
  | mask (j : ℕ)
  /-- a cell of the planes' matrix -/
  | cell (row col : ℕ)
  /-- key number i of call c -/
  | key (c i : ℕ)
  /-- a place that reads 0 -/
  | zero
  deriving DecidableEq, Repr

/-- A sumcheck's places: the ledger's function for that sumcheck, from the lookup's first slot
on. -/
def ledF (jLK : ℕ) (pl : Ent → ℕ) : Led Pl :=
  ⟨fun r t => .mask (jLK + pl (.coef r t)), .mask (jLK + pl .const),
    fun a => .mask (jLK + pl (.shown a))⟩

/-- Two flat lists, cut into rounds: each pair says how many members of the first and of the
second list a round takes. -/
def cut {α : Type} : List (ℕ × ℕ) → List α → List α → List (List α × List α)
  | [], _, _ => []
  | p :: r, s, d => (s.take p.1, d.take p.2) :: cut r (s.drop p.1) (d.drop p.2)

section
variable {K : Type} [CommRing K]

/-- Row u of the joined table, moved by its call's shift. -/
def tabF (h : Sh) (θ : K) (u : ℕ) : K :=
  ((tauN h (rowOf h u).1 (rowOf h u).2 : ℕ) : K) + ((rowOf h u).1 : K) * θ

/-- The public numbers of TwV's function at a group of calls. lm (the planes' matrix has 2^lm
rows) and jLK (the lookup's first slot) are the caller's; θ is the shift. -/
def numsF (h : Sh) (lm jLK : ℕ) (θ : K) : Nums Pl K where
  v' := FoNums.v' h
  d := h.d
  w := FoNums.w
  n := FoNums.n
  tab := tabF h θ
  pads := pads h
  oK := ordK h
  oT := ordT
  oE := ordE h
  oB := ordB h
  kAt := fun X => (keyOf h X).map fun p => .key p.1 p.2
  kC := fun _ => tabF h θ (padRow h 0)
  bAt := fun u j => match cellOf h u j with
    | some x => .cell (cellRC h lm x).1 (cellRC h lm x).2
    | none => .zero
  ledTie := fun j => ledF jLK ((S h).pTieC j)
  ledK := fun l => ledF jLK ((S h).pKeyC l)
  ledT := fun l => ledF jLK ((S h).pTabC l)
  ledE := ⟨(ledF jLK (S h).pEndC).pw, (ledF jLK (S h).pEndC).c0,
    fun _ => .mask (jLK + (S h).pBit (.shown 0))⟩
  ledB := ledF jLK (S h).pBitC

/-- Every row but the keys', in the order of `TwV.rowsOfTrace`, whose text this is. -/
def rows16 {P : Type} (N : Nums P K) (t : Trace K) : List (SRow P K) :=
  tieRowsR N t.lam t.tie.reverse ++
    (lvRowsR N.ledK 0 (fK N t) t.keys.reverse ++
      ((lvRowsR N.ledT N.w (incT0 N t) t.tabl.reverse ++
          [rowEnd N t, rowBitU N t, rowBitE N t]) ++
        [rowNum N]))

/-- The rows of TwV's function are these and the keys' row. -/
theorem rows_split {P : Type} (N : Nums P K) (t : Trace K) :
    rowsOfTrace N t = rows16 N t ++ [rowKey N t] := rfl

/-- The keys' point, by coordinate. -/
def pntK {P : Type} (N : Nums P K) (t : Trace K) : List K := pntTop N.oK [] t.keys.reverse

/-- The shift's share of the keys' extension at the point: the sum over the keys X that are
entries of eq(point, X) times the call's number times θ. km takes key X to its call and its number
in the call (`FoNums.keyOf h`; an argument so that tests can bend it). -/
def shiftShare (v : ℕ) (km : ℕ → Option (ℕ × ℕ)) (θ : K) (pnt : List K) : K :=
  ((List.range (2 ^ v)).map fun X => match km X with
    | some p => eqN pnt X * ((p.1 : K) * θ)
    | none => 0).sum

/-- The keys' row at a group of calls. -/
def rowKeyF (v : ℕ) (km : ℕ → Option (ℕ × ℕ)) (θ : K) (N : Nums Pl K) (t : Trace K) :
    SRow Pl K :=
  let r := rowKey N t
  ⟨r.cf, r.tg - shiftShare v km θ (pntK N t)⟩

/-! ### The rounds -/

/-- (scalars sent, elements drawn) of a sumcheck's rounds. -/
def scRounds (c : TwNums.Sc) : List (ℕ × ℕ) :=
  (1, 1) :: c.degs.map (fun n => (n, 1)) ++ if c.shown = 0 then [] else [(c.shown, 0)]

/-- (scalars sent, elements drawn) of every round, the shift's first. -/
def planF (h : Sh) : List (ℕ × ℕ) :=
  (if several h then [(0, 1)] else []) ++ [(0, 1)] ++
    (List.range (FoNums.n + 1)).flatMap (fun j => scRounds ((S h).scTie j)) ++ [(0, FoNums.w)] ++
    (List.range h.v).flatMap (fun l => scRounds ((S h).scKey l) ++ [(0, 1)]) ++
    (List.range h.d).flatMap (fun l => scRounds ((S h).scTab l) ++ [(0, 1)]) ++
    scRounds (S h).scEnd ++ [(0, FoNums.w + h.d)] ++ scRounds (S h).scBit

/-! ### The function -/

/-- The shift: the first round's draw, if there are several calls. -/
def thetaOf (h : Sh) (rs : Rounds K) : K :=
  if several h then (rs.headD ([], [])).2.headD 0 else 0

/-- The rounds behind the shift's. -/
def afterShift (h : Sh) (rs : Rounds K) : Rounds K := if several h then rs.tail else rs

/-- The public numbers at the rounds' shift. -/
def forN (h : Sh) (lm jLK : ℕ) (rs : Rounds K) : Nums Pl K := numsF h lm jLK (thetaOf h rs)

/-- What the chain's last state holds. -/
def forTrace (h : Sh) (lm jLK : ℕ) (rs : Rounds K) : Trace K :=
  traceOfFlat (forN h lm jLK rs) (afterShift h rs)

/-- The rows that the verifier hands on, sparse: the tie's (a later step first), the key levels'
(a later level first), the table levels' (likewise), the leaves', the bits' sumcheck's, the bits'
end row, the sum of the counts, and the keys' row. -/
def forV (h : Sh) (lm jLK : ℕ) (rs : Rounds K) : List (SRow Pl K) :=
  rows16 (forN h lm jLK rs) (forTrace h lm jLK rs) ++
    [rowKeyF h.v (keyOf h) (thetaOf h rs) (forN h lm jLK rs) (forTrace h lm jLK rs)]

end
end Fo
