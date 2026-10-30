-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean: the course over the field: OUR OWN TEXT of the
program's lookup verifier, written anew over the field, as plain functions of the flat rounds, cut
at eight seams. It is no routine of the program.

The program's lookup (`Lkp.run`, OnBytes/Iop/Lkp.lean) draws, runs sumchecks and joins claims. Its
pure parts have their texts over the field: `PscF.outOf` (OnBytes/Slice/KeyPscRun.lean), the five
summands (OnBytes/Tie/Pv/KeyLookup/PortSim.lean), `lineF`, `joinF`, `byVarF`
(OnBytes/Tie/Pv/KeyLookup/PortRead.lean). This file puts these parts in a row as `Lkp.run` does: no
state monad, no failure. It is generic in the public record (`Lk6.Pub`,
Cb/Pv/KeyLookup/Letters.lean): several parts; planes that are not real; an order of its own at each
part's last key level, whose two shown values are masked by entries of a second message.

Main names:
  `Dt`: the public record; for each of the two ledgers the mask entries in the order in which it
  gives them out; the public factor as a function of alpha; the table's extension at a point.
  `RowF`: a row: a mask form, terms on the table of bits (a coefficient and a vector of product
  form), a target.
  `Cs`: where a course stands: the rounds left, the mask entries taken of either message, the rows
  so far, alpha, the claims in hand.
  `heardF`, `slots`, `pscC`: one sumcheck: what is read of the next rounds; the fresh mask entries;
  what is handed on, and the stand behind it.
  `cHead`, `cParts`, `cJoin`, `cKeys`, `cTable`, `cClo`, `cZero`, `cBits`: the eight stretches.
  `chnC`: all in a row. `course`: with the last row, on the number of keys.

Limits. Definitions alone: no theorem. That the program's run, read in the field, is this course is
not shown here: it is shown, under conditions on public data, in files that are not in this library
yet. Until then a statement on the course is a statement on our text, and no step from the program.
Where the rounds do not fit, the functions give values without meaning.

-/
import OnBytes.Tie.Pv.KeyLookup.PortRead
import Johnson.Desc.First.Look.KeyLaw.Readings

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid
open Lk6.PortSim

open OnBytes OnBytes.Slice

/-- What a course is told. -/
structure Dt where
  /-- the public record -/
  S : Pub
  /-- the mask entries in the order in which the first ledger gives them out -/
  ms : ℕ → Slot
  /-- the same for the second ledger, which gives the two mask entries of each part's last key
  level -/
  ix : ℕ → Slot
  /-- the public factor, from alpha -/
  fac : GE → GE
  /-- the table's extension at a point of d coordinates -/
  tabAt : List GE → GE

/-- Where a course stands. -/
structure Cs where
  /-- the rounds left -/
  rounds : List (Flat.RV GE)
  /-- the mask entries taken of the first message, and of the second -/
  own : ℕ
  idx : ℕ
  rows : List RowF
  alpha : GE
  /-- on the product of the parts' roots that are left; on the power that is reached; on the level
  of the table's tree that is reached; on the table of bits -/
  (rest pow top bit : PscF.PointClaim)
  /-- on the planes' roots, the parts' roots, the leaves of the parts' trees, by number -/
  (planes roots leaves : ℕ → PscF.PointClaim)
  /-- the zero point -/
  zt : List GE

/-- The first element drawn in the next round. -/
def Cs.draw (s : Cs) : GE := (s.rounds.headD ([], [])).2.headD 0

/-- All elements drawn in the next round. -/
def Cs.draws (s : Cs) : List GE := (s.rounds.headD ([], [])).2

/-- The stand behind the next round. -/
def Cs.next (s : Cs) : Cs := { s with rounds := s.rounds.tail }

/-- What a sumcheck of k variables reads of the next rounds. y: values are shown. -/
def heardF (k : ℕ) (y : Bool) (f : List (Flat.RV GE)) : PscF.Heard :=
  let pr := fun (r : Flat.RV GE) => (r.1, r.2.headD 0)
  ⟨(f.headD ([], [])).1.headD 0, (f.headD ([], [])).2.headD 0,
    ((f.drop 1).take (if y then k + 1 else k)).map pr,
    if y then (f.getD (k + 2) ([], [])).1 else []⟩

/-- The n mask entries that a ledger gives out from its entry number first on. -/
def slots (e : ℕ → Slot) (first n : ℕ) : List Slot := (List.range n).map fun i => e (first + i)

/-- The equality vector at a point, as pairs. -/
def eqPairsF (p : List GE) : List (GE × GE) := p.map fun a => (1 - a, a)

/-- **One sumcheck.** keys: the last two fresh mask entries are the second message's. kept: how many
kept maps the row names. place: puts the point back by variable. -/
def pscC (D : Dt) (c : PscF.Claim) (S : PscF.Summand) (keys : Bool) (kept : ℕ)
    (place : List GE → List GE) (s : Cs) : PscF.Out × Cs :=
  let n := PscF.masksOf c S
  let y := S.shown != 0
  let k := c.vars.length
  let fresh := if keys then slots D.ms s.own (n - 2) ++ slots D.ix s.idx 2 else slots D.ms s.own n
  let o := PscF.outOf c S fresh (heardF k y s.rounds)
  let o' : PscF.Out :=
    { o with point := place o.point, ends := o.ends.map fun e => { e with point := place e.point } }
  (o', { s with
    rounds := s.rounds.drop (if y then k + 3 else k + 1)
    own := s.own + (if keys then n - 2 else n)
    idx := s.idx + (if keys then 2 else 0)
    rows := s.rows ++
      [⟨o'.rowMasks, (o'.rowMaps.take kept).map fun a => (a, eqPairsF o'.point), o'.rowTarget⟩] })

/-- The later steps of the tie: step j hands on the next power and plane j + 1's root. -/
def cTie (D : Dt) : ℕ → ℕ → Cs → Cs
  | 0, _, s => s
  | n + 1, j, s =>
    let (o, s) := pscC D (onValue s.pow) sTie false 0 id s
    cTie D n (j + 1)
      { s with
        pow := o.ends.getD 0 noClaim
        planes := Function.update s.planes (j + 1) (o.ends.getD 1 noClaim) }

/-- STRETCH 1: alpha; the tie's first step; its later steps; the last power is the last plane's
root. f: the rounds; own, idx: the mask entries taken so far. -/
def cHead (D : Dt) (f : List (Flat.RV GE)) (own idx : ℕ) : Cs :=
  let s0 : Cs := ⟨f, own, idx, [], 0, noClaim, noClaim, noClaim, noClaim, fun _ => noClaim,
    fun _ => noClaim, fun _ => noClaim, []⟩
  let s1 : Cs := { s0.next with alpha := s0.draw }
  let (o, s) := pscC D ⟨[], [], 0⟩ (sTie1 (D.fac s1.alpha)) false 0 id s1
  let s := cTie D (D.S.pl - 2) 0
    { s with
      rest := o.ends.getD 0 noClaim
      pow := o.ends.getD 1 noClaim
      planes := Function.update s.planes 0 (o.ends.getD 2 noClaim) }
  { s with planes := Function.update s.planes (D.S.pl - 1) s.pow }

/-- The parts' steps: step j hands on part j's root and the product of the others. -/
def cPart (D : Dt) : ℕ → ℕ → Cs → Cs
  | 0, _, s => s
  | n + 1, j, s =>
    let (o, s) := pscC D (onValue s.rest) sProd false 0 id s
    cPart D n (j + 1)
      { s with
        roots := Function.update s.roots j (o.ends.getD 0 noClaim)
        rest := o.ends.getD 1 noClaim }

/-- STRETCH 2: from the product of the parts' roots to each root. -/
def cParts (D : Dt) (s : Cs) : Cs :=
  let s := cPart D (D.S.m - 1) 0 s
  { s with roots := Function.update s.roots (D.S.m - 1) s.rest }

/-- STRETCH 3: the join point; the planes' claims become one. -/
def cJoin (D : Dt) (s : Cs) : Cs :=
  { s.next with top := joinF D.S.mu s.draws ((List.range D.S.pl).map s.planes) }

/-- The levels of a product tree from level l on, as many as the first number. keys: a key tree,
whose last level has an order and two mask entries of its own. Returns the claim on the leaves. -/
def cLevels (D : Dt) (keys : Bool) (more : ℕ) : ℕ → ℕ → PscF.PointClaim → Cs → PscF.PointClaim × Cs
  | 0, _, c, s => (c, s)
  | n + 1, l, c, s =>
    let last := keys && n == 0
    let order := if last then ordFirst D.S.order (more + l) else ordDown (more + l)
    let (o, s) := pscC D
      ⟨order.map fun t => PscF.Weight.equality (c.point.getD t 0) 3, c.masks, c.value⟩ sProd last 0
      (byVarF · order) s
    cLevels D keys more n (l + 1)
      (lineF s.draw (o.ends.getD 0 noClaim) (o.ends.getD 1 noClaim)) s.next

/-- The key trees from part i on, as many as the first number. -/
def cKey (D : Dt) : ℕ → ℕ → Cs → Cs
  | 0, _, s => s
  | n + 1, i, s =>
    let (c, s) := cLevels D true 0 (D.S.v i) 0 (s.roots i) s
    cKey D n (i + 1) { s with leaves := Function.update s.leaves i c }

/-- STRETCH 4: the key trees of all parts. -/
def cKeys (D : Dt) (s : Cs) : Cs := cKey D D.S.m 0 s

/-- STRETCH 5: the table's tree. -/
def cTable (D : Dt) (s : Cs) : Cs :=
  let (c, s) := cLevels D false D.S.mu D.S.d 0 s.top s
  { s with top := c }

/-- STRETCH 6: the leaves of the table's tree, affine in the bits. -/
def cClo (D : Dt) (s : Cs) : Cs :=
  let order := ordDown (D.S.mu + D.S.d)
  (pscC D
    ⟨order.map fun t =>
        PscF.Weight.equality (s.top.point.getD t 0) (if t < D.S.mu then 2 else 3),
      s.top.masks, s.top.value⟩
    (sLeaves fun p => s.alpha - 1 - D.tabAt ((byVarF p order).drop D.S.mu)) false 1
    (byVarF · order) s).2

/-- STRETCH 7: the zero point. -/
def cZero (_ : Dt) (s : Cs) : Cs := { s.next with zt := s.draws }

/-- STRETCH 8: the bits are bits; the claim on the table of bits at the end point becomes a row. -/
def cBits (D : Dt) (s : Cs) : Cs :=
  let order := ordDown (D.S.mu + D.S.d)
  let (o, s) := pscC D ⟨order.map fun t => PscF.Weight.equality (s.zt.getD t 0) 3, [], 0⟩ sBits
    false 0 (byVarF · order) s
  let b := o.ends.getD 0 noClaim
  { s with bit := b, rows := s.rows ++ [⟨b.masks, [(1, eqPairsF b.point)], b.value⟩] }

/-- The row on the number of keys that are no padding. -/
def cntRowF (D : Dt) : RowF :=
  ⟨[], [(1, ((List.range D.S.mu).map fun t => ((1 : GE), (2 : GE) ^ 2 ^ t)) ++
    List.replicate D.S.d (1, 1))], ((D.S.allKeys - D.S.padCount : ℕ) : GE)⟩

/-- The eight stretches in a row. -/
def chnC (D : Dt) (f : List (Flat.RV GE)) (own idx : ℕ) : Cs :=
  cBits D (cZero D (cClo D (cTable D (cKeys D (cJoin D (cParts D (cHead D f own idx)))))))

/-- **The whole course**: the eight stretches, then the row on the number of keys. -/
def course (D : Dt) (f : List (Flat.RV GE)) (own idx : ℕ) : Cs :=
  { chnC D f own idx with rows := (chnC D f own idx).rows ++ [cntRowF D] }

end Lk6.Mid

#print axioms Lk6.Mid.course
