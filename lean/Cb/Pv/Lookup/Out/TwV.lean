-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Out/TwV.lean.
A flat, computable function on plain data, written after the lookup's verifier.

Over the short sumcheck the typed lookup's verifier never refuses (`Tw.baseK₀_out`,
Cb/Pv/Lookup/Out/TwFill.lean): it hands on a list of linear claims on entries. This file is written
to compute that list from plain data: for each round the scalars sent and the challenges drawn. It
names no typed record of the library: lists, numbers, a commutative ring K and a type P of places.
Definitions alone: Lean generates code for all of them.

Main names:
  `SRow`, `dense`: a sparse row: places with coefficients, and a target; its coefficient at a place.
  `Trace`: what the whole run leaves. What one sumcheck leaves (`Sc`), the plain data (`Rounds`) and
    one sumcheck's run (`evalGo`, `runVars`, `takeSc`) are those of Cb/G9/FlatStep.lean.
  `Led`, `Nums`: the places of one sumcheck's mask entries; the public numbers, orders and places.
  `traceOfFlat N`: from the rounds to a Trace. It completes each round's polynomial at the constant
    coefficient, which is not sent, and evaluates it at the challenge.
  `rowsOfTrace N`: from a Trace to the rows, in the order of LkAsmH.rd's rows, then the keys' row.
  `vOf N`: rowsOfTrace N after traceOfFlat N.
  `pointsOf N`: the sumchecks' points by coordinate, read off a Trace, for tests.
The formulas are written after the library's: PscPar.slU, tU, slE (Cb/Ld/LdPsc.lean); hSl
(Cb/Ld/LdHide.lean); TieF.TS, TN, rowsAt, bK, bT; TreeP.T0, rowsAt; LineCube.next; RootP.toIn;
LkAsmH.fK, formT, tgtT, enterT, rd; LkEndM.par, rowB; LkInst.endM, topCl; LkBit.zc, rowA;
LkHeadF.numRowF, fac.
Limits: it holds no theorem. That these are the typed verifier's values, and that the rows stand in
its order, is not said here (see Cb/Pv/Lookup/Out/TwRows.lean and Cb/Pv/Lookup/Out/TwState.lean).
The library's factor hPsi does not stand here: it is 1 where every psi is the constant 1
(`Tw3.hPsi_one`, Cb/Pv/Lookup/Alg/TwGen.lean). Nothing is refused: on data that are too short a
missing element is read as 0; rounds after the last one read are ignored; a variable's round
polynomial is taken at the length of its message, whatever the degree. For a coordinate that an
order o does not hold, byVar reads the challenges' member number o.length (0 if there is none).
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.G9.FlatStep
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.BigOperators.Group.List.Defs

set_option autoImplicit false

namespace TwV

/-! ## 1. The types -/

/-- A sparse row: the sum over the list of coefficient times the entry at the place equals the
target. A place may stand twice. -/
structure SRow (P K : Type) where
  cf : List (P × K)
  tg : K
  deriving Repr

/-- the coefficient of a sparse form at a place -/
def dense {P K : Type} [DecidableEq P] [AddMonoid K] (cf : List (P × K)) (j : P) : K :=
  (cf.map fun pc => if pc.1 = j then pc.2 else 0).sum

/-- What the run leaves. All lists: the oldest first. A level goes with its line's draw. -/
structure Trace (K : Type) where
  lam : K
  tie : List (Sc K)
  join : List K
  keys : List (Sc K × K)
  /-- the target at the keys' top (in the typed state a component of its own; on a run it is the
  last line's target) -/
  kT : K
  tabl : List (Sc K × K)
  cls : Sc K
  zero : List K
  bits : Sc K
  deriving Repr, DecidableEq

/-- The places of one sumcheck's own mask entries: the hiding polynomial's coefficient of power
t + 1 in the variable of round r; its constant; the mask of shown value number a. -/
structure Led (P : Type) where
  pw : ℕ → ℕ → P
  c0 : P
  sh : ℕ → P

/-- The public numbers, as in `LkAsmH` (Cb/Pv/Lookup/Asm/AsmH.lean): 2^(v' + 1) keys, 2^d rows of
the table tab, 2^w planes of which n + 2 count; pads: the public padding (row, how many keys);
bAt u j: the place of bit j of row u's count. Orders as lists: round j binds coordinate o[j]. -/
structure Nums (P K : Type) where
  v' : ℕ
  d : ℕ
  w : ℕ
  n : ℕ
  tab : ℕ → K
  pads : List (ℕ × ℕ)
  oK : ℕ → List ℕ
  oT : ℕ → List ℕ
  oE : List ℕ
  oB : List ℕ
  /-- key number b: an entry, or (none) the public constant kC b -/
  kAt : ℕ → Option P
  kC : ℕ → K
  bAt : ℕ → ℕ → P
  ledTie : ℕ → Led P
  ledK : ℕ → Led P
  ledT : ℕ → Led P
  ledE : Led P
  ledB : Led P

section
variable {P K : Type} [CommRing K]

/-! ## 2. Small functions -/

/-- the empty record, where a list has no such member -/
def Sc.zero : Sc K := ⟨0, [], 0, []⟩

/-- the challenge of the further variable -/
def Sc.be (s : Sc K) : K := s.xs.getLastD 0
/-- shown value number a -/
def Sc.v (s : Sc K) (a : ℕ) : K := s.vals.getD a 0

/-- a form, scaled -/
def scale (c : K) (f : List (P × K)) : List (P × K) := f.map fun pc => (pc.1, c * pc.2)

/-- eq(point, corner number e): coordinate i goes with bit i of e, lowest first -/
def eqN : List K → ℕ → K
  | [], _ => 1
  | x :: xs, e => (if e % 2 = 1 then x else 1 - x) * eqN xs (e / 2)

/-- challenges by round → the point by coordinate: coordinate c is the challenge of the round that
binds it -/
def byVar (o : List ℕ) (xs : List K) : List K := (List.range o.length).map fun c => xs.getD (o.idxOf
    c) 0
/-- a point by coordinate → in the order of the rounds -/
def inRounds (o : List ℕ) (pt : List K) : List K := o.map fun c => pt.getD c 0

/-- the hiding polynomial's value at the point as a form: x_r^(t+1) at the place of (round r,
power t + 1) -/
def hideGo (pw : ℕ → ℕ → P) : ℕ → List ℕ → List K → List (P × K)
  | r, n :: dg, x :: xs => ((List.range n).map fun t => (pw r t, x ^ (t + 1))) ++ hideGo pw (r + 1)
      dg xs
  | _, _, _ => []
def hide (L : Led P) (dg : List ℕ) (xs : List K) : List (P × K) := hideGo L.pw 0 dg xs ++ [(L.c0,
    1)]

/-- The row on the hiding coefficients (slU, tU) of a sumcheck none of whose maps stays
unrevealed. -/
def rowU (L : Led P) (dg : List ℕ) (s : Sc K) (inc : List (P × K)) (S0 : K) : SRow P K :=
  ⟨hide L dg s.xs ++ scale s.eps inc, s.fin - s.eps * S0⟩

/-- the form that a line step hands on: β (1 − ρ) at c₀, β ρ at c₁; its target -/
def lineForm (L : Led P) (s : Sc K) (rho : K) : List (P × K) :=
  [(L.sh 0, s.be * (1 - rho)), (L.sh 1, s.be * rho)]
def lineTg (s : Sc K) (rho : K) : K := (1 - rho) * s.v 0 + rho * s.v 1

/-! ## 3. The tie -/

variable (N : Nums P K)

/-- the public factor -/
def fac (lam : K) : K := (N.pads.map fun e => (lam - N.tab e.1) ^ e.2).prod

/-- `nxAt l`: the number of step l's shown value that the next step takes up. `ptAt l` (below): the
number of the plane's product. -/
def nxAt (l : ℕ) : ℕ := if l = 0 then 1 else 0
def ptAt (l : ℕ) : ℕ := if l = 0 then 2 else 1

/-- the summand at the shown values -/
def tieS0 (lam : K) (l : ℕ) (s : Sc K) : K :=
  if l = 0 then s.v 0 - fac N lam * (s.v 1 ^ 2 * s.v 2) else s.v 0 ^ 2 * s.v 1

/-- the form that comes into step l, from the steps before it (the newest first) -/
def tieInc : List (Sc K) → List (P × K)
  | [] => []
  | s :: rest => [((N.ledTie rest.length).sh (nxAt rest.length), s.be)]

/-- the tie's rows, from its steps the newest first; the newest first -/
def tieRowsR (lam : K) : List (Sc K) → List (SRow P K)
  | [] => []
  | s :: rest =>
    rowU (N.ledTie rest.length) [3] s (tieInc N rest) (tieS0 N lam rest.length s) :: tieRowsR lam
        rest

/-! ## 4. What the tie leaves: the claims on the products -/

/-- form and target of the masked claim on the product of the keys -/
def fK (t : Trace K) : List (P × K) := [((N.ledTie 0).sh 0, (t.tie.getD 0 Sc.zero).be)]
def tK (t : Trace K) : K := (t.tie.getD 0 Sc.zero).v 0

/-- forms and targets of the claims on the table's products -/
def formT (t : Trace K) (th : ℕ) : List (P × K) :=
  if th < N.n + 1 then [((N.ledTie th).sh (ptAt th), (t.tie.getD th Sc.zero).be)]
  else if th = N.n + 1 then [((N.ledTie N.n).sh (nxAt N.n), (t.tie.getD N.n Sc.zero).be)]
  else []
def tgtT (t : Trace K) (th : ℕ) : K :=
  if th < N.n + 1 then (t.tie.getD th Sc.zero).v (ptAt th)
  else if th = N.n + 1 then (t.tie.getD N.n Sc.zero).v (nxAt N.n) else 1

/-- the table's incoming form and target at level 0: the combination at the point -/
def incT0 (t : Trace K) : List (P × K) :=
  (List.range (2 ^ N.w)).flatMap fun th => scale (eqN t.join th) (formT N t th)
def tgT0 (t : Trace K) : K := ((List.range (2 ^ N.w)).map fun th => eqN t.join th * tgtT N t th).sum

/-! ## 5. A tree -/

/-- form, target and point at the top of the levels done (the newest first) -/
def incTop (led : ℕ → Led P) (inc0 : List (P × K)) : List (Sc K × K) → List (P × K)
  | [] => inc0
  | s :: rest => lineForm (led rest.length) s.1 s.2
def tgTop (tg0 : K) : List (Sc K × K) → K
  | [] => tg0
  | s :: _ => lineTg s.1 s.2
def pntTop (o : ℕ → List ℕ) (p0 : List K) : List (Sc K × K) → List K
  | [] => p0
  | s :: rest => byVar (o rest.length) s.1.xs ++ [s.2]

/-- a tree's rows, from its levels the newest first; the newest first. g: the variables of level
0 -/
def lvRowsR (led : ℕ → Led P) (g : ℕ) (inc0 : List (P × K)) : List (Sc K × K) → List (SRow P K)
  | [] => []
  | s :: rest =>
    rowU (led rest.length) (List.replicate (g + rest.length) 2 ++ [2]) s.1 (incTop led inc0 rest)
        (s.1.v 0 * s.1.v 1) ::
      lvRowsR led g inc0 rest

/-! ## 6. The closing, the bits, the pin, the keys -/

/-- the planes' bits at a point, as a form: eq(point, corner e) at the bit of corner e (the low w
bits: the plane) -/
def bitsForm (pt : List K) : List (P × K) :=
  (List.range (2 ^ (N.w + N.d))).map fun e => (N.bAt (e / 2 ^ N.w) (e % 2 ^ N.w), eqN pt e)

/-- the closing's degrees, by round -/
def dgE : List ℕ := N.oE.map fun c => if c < N.w then 1 else 2

/-- the closing's row: S0 = 1; S1 = the extension of (λ − 1 − tab) at the rows' coordinates -/
def rowEnd (t : Trace K) : SRow P K :=
  let gam := byVar N.oE t.cls.xs
  let s1 := ((List.range (2 ^ N.d)).map fun r => eqN (gam.drop N.w) r * (t.lam - 1 - N.tab r)).sum
  ⟨hide N.ledE (dgE N) t.cls.xs ++ scale t.cls.eps (incTop N.ledT (incT0 N t) t.tabl.reverse) ++
      scale (t.cls.eps * s1) (bitsForm N gam),
    t.cls.fin - t.cls.eps * 1⟩

/-- the bits' two rows -/
def rowBitU (t : Trace K) : SRow P K :=
  rowU N.ledB (List.replicate (N.w + N.d) 2 ++ [2]) t.bits [] (t.bits.v 0 * (t.bits.v 0 - 1))
def rowBitE (t : Trace K) : SRow P K :=
  ⟨bitsForm N (byVar N.oB t.bits.xs) ++ [(N.ledB.sh 0, t.bits.be)], t.bits.v 0⟩

/-- The pin: the counts sum to the number of keys that are not padding, as a row (written after
`LkHeadF.numRowF`, Cb/Pv/Lookup/Blocks/HeadF.lean). -/
def rowNum : SRow P K :=
  ⟨(List.range (2 ^ N.d)).flatMap fun u => (List.range (N.n + 2)).map fun j => (N.bAt u j, (2 : K) ^
      j),
    ((2 ^ (N.v' + 1) - (N.pads.map Prod.snd).sum : ℕ) : K)⟩

/-- the keys' row: the extension of the keys at the point, less the masks' form; the public
constants' share in the target -/
def rowKey (t : Trace K) : SRow P K :=
  let pnt := pntTop N.oK [] t.keys.reverse
  ⟨((List.range (2 ^ (N.v' + 1))).flatMap fun b =>
        match N.kAt b with
        | some p => [(p, eqN pnt b)]
        | none => []) ++
      scale (-1) (incTop N.ledK (fK N t) t.keys.reverse),
    t.lam - t.kT -
      ((List.range (2 ^ (N.v' + 1))).map fun b =>
        match N.kAt b with
        | some _ => 0
        | none => eqN pnt b * N.kC b).sum⟩

/-! ## 7. The rows, in the typed verifier's order -/

/-- The tie's rows, the keys' levels', the table's levels', the closing's, the bits' two, the pin
(written after the order of the rows in `LkAsmH.rd`, Cb/Pv/Lookup/Asm/AsmH.lean), then the keys'
row. Among the tie's steps and among a tree's levels: the newest first. -/
def rowsOfTrace (t : Trace K) : List (SRow P K) :=
  (tieRowsR N t.lam t.tie.reverse ++
    (lvRowsR N.ledK 0 (fK N t) t.keys.reverse ++
      ((lvRowsR N.ledT N.w (incT0 N t) t.tabl.reverse ++ [rowEnd N t, rowBitU N t, rowBitE N t]) ++
        [rowNum N]))) ++ [rowKey N t]

/-! ## 8. From plain data to the trace -/

/-- c steps of the tie from step l on -/
def tieGo : ℕ → ℕ → K → Rounds K → List (Sc K) × Rounds K
  | 0, _, _, rs => ([], rs)
  | c + 1, l, tg, rs =>
    let a := takeSc rs tg [0] true
    let b := tieGo c (l + 1) (a.1.v (nxAt l)) a.2
    (a.1 :: b.1, b.2)

/-- c levels of a tree from level l on: sumcheck, line. Returns the levels, then target and point
at the top, and what is left. -/
def lvGo (o : ℕ → List ℕ) : ℕ → ℕ → K → List K → Rounds K → List (Sc K × K) × K × List K × Rounds K
  | 0, _, tg, pt, rs => ([], tg, pt, rs)
  | c + 1, l, tg, pt, rs =>
    let a := takeSc rs tg (inRounds (o l) pt ++ [0]) true
    let rho := (a.2.headD ([], [])).2.headD 0
    let b := lvGo o c (l + 1) (lineTg a.1 rho) (byVar (o l) a.1.xs ++ [rho]) a.2.tail
    ((a.1, rho) :: b.1, b.2)

/-- The rounds are read in this order: the draw of λ; n + 1 steps of the tie; the draw of the
planes' point; v' + 1 levels of the keys' tree; d levels of the table's tree; the closing (no
values' round); the draw of the bits' point; the bits' sumcheck. -/
def traceOfFlat (rs : Rounds K) : Trace K :=
  let lam := (rs.headD ([], [])).2.headD 0
  let ti := tieGo (N.n + 1) 0 0 rs.tail
  let join := (ti.2.headD ([], [])).2
  let t0 : Trace K := ⟨lam, ti.1, join, [], 0, [], Sc.zero, [], Sc.zero⟩
  let ke := lvGo N.oK (N.v' + 1) 0 (tK t0) [] ti.2.tail
  let ta := lvGo N.oT N.d 0 (tgT0 N t0) join ke.2.2.2
  let cl := takeSc ta.2.2.2 ta.2.1 (inRounds N.oE ta.2.2.1) false
  let zero := (cl.2.headD ([], [])).2
  let bi := takeSc cl.2.tail 0 (inRounds N.oB zero ++ [0]) true
  ⟨lam, ti.1, join, ke.1, ke.2.1, ta.1, cl.1, zero, bi.1⟩

/-- From the rounds to the rows: rowsOfTrace N after traceOfFlat N. -/
def vOf (rs : Rounds K) : List (SRow P K) := rowsOfTrace N (traceOfFlat N rs)

/-- the sumchecks' points by coordinate, in the order of the run, read off the trace (for tests) -/
def pointsOf (t : Trace K) : List (List K) :=
  t.tie.map (fun _ => []) ++
    ((List.range t.keys.length).map fun l => byVar (N.oK l) (t.keys.getD l (Sc.zero, 0)).1.xs) ++
    ((List.range t.tabl.length).map fun l => byVar (N.oT l) (t.tabl.getD l (Sc.zero, 0)).1.xs) ++
    [byVar N.oE t.cls.xs, byVar N.oB t.bits.xs]

end
end TwV
