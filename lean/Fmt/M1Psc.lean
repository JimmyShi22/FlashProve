-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1Psc.lean: the verifier's part in the zero-check ("ZERO") and in the sum-check with a hiding
polynomial ("PSC") of the first toy (a product test): the claim that is moved, the left-out
coefficients got back, the three rows that are handed on.

Definitions that compute, total, generic in the number K of variables; tests (#guard) against a
prover of this library's own at small sizes. No Mathlib. After: the programs' description of the
toy's protocol
(the programs: the C++ implementation that comes with this Lean code), Part 2 (sections 0 to 3),
with Part 1's section 0 for the table's indices.
The first toy is a small test protocol of the programs. In a sum-check the running claim R is the
value that the remaining sum is said to have. A row (`GRow`, Fmt/M1Types.lean) is a linear equation
on the message behind a sent oracle message: coefficient vectors c (on the main table) and d (on the
mask table) and a target t. a~(x) is the multilinear extension of the row a at the point x: the sum
over i of eq(x, i) a_i, where eq(x, i) is the entry i of `eqTab` (Fmt/M1Types.lean).

The claim: a_i b_i = c_i for all i below 2^K, for the rows 0, 1, 2 of one oracle message.
ZERO (Part 2, 1): the prover sends nothing; K elements zeta are drawn. The claim becomes: the sum
over i of eq(zeta, i) (a_i b_i - c_i) is T = 0. Nothing is tested.
PSC (Part 2, 2): a sum-check in K + 1 variables: X_j is summed as
g ↦ (1 - zeta_j) g(0) + zeta_j g(1), one further variable Y as g ↦ g(0). Every round polynomial has
three coefficients, and the constant one is never sent: the equation that a sum-check would test is
used to get it back. So nothing is tested here either.

Main names:
  `PscMsg`, `PscDraw`: what the prover sends: mu'; K pairs (q_1, q_2); (p_1, p_2); (v_1, v_2); what
    is drawn: eps; gamma_0 .. gamma_(K-1); beta (never 0: the drawing's rule, not tested here).
  `pscFits` K ..: the lists have K members (the reader's matter; here so that the functions' results
    mean something).
  `constX`, `stepX`: one round in X: q_0 := R - zeta (q_1 + q_2); the next
    R := q_0 + q_1 gamma + q_2 gamma^2.
  `pscR`: R_0 := mu' + eps T; K rounds in X; the round in Y: p_0 := R_K,
    R_(K+1) := p_0 + p_1 beta + p_2 beta^2.
  `leftOut`: the K + 1 constants that were got back (for tests).
  `pscRows f K lzk o` (o: a `PscOut`): the three rows, written out, in the order in which they are
    batched: c on the main table of 2^(K + 2) entries (entry (row r, place i) at r + 4 i), d on the
    lzk entries of the mask row. With m_t the mask row's entry number first + t:
      (U)    sum over l < K of (gamma_l m_(2l) + gamma_l^2 m_(2l+1)) + m_(2K) + beta m_(2K+1)
             + beta^2 m_(2K+2) - eps c~(gamma)  =  R_(K+1) - eps v_1 v_2
      (E_1)  a~(gamma) + beta m_(2K+3) = v_1;          (E_2)  b~(gamma) + beta m_(2K+4) = v_2
  `pscBlock`: the same on plain arguments, as a list: the form in which the string of all blocks
    (Fmt/M1Dec.lean: `Blocks.psc`) takes it.
  `pscTakes K`: 2 K + 5 scalars are sent and 2 K + 5 mask entries are used, each once
    (at K = 12: 29).

A prover of this library's own (namespace `Fmt.M1.PscHon`), written from the definition of the
polynomial on which the honest prover runs the sum-check,
H(X, Y) = U(X, Y) + eps ((a~(X) + c_1 Y)(b~(X) + c_2 Y) - c~(X)) (`PscHon.poly`; U is `PscHon.hid`,
c_1 = m_(2K+3), c_2 = m_(2K+4)), round polynomials by sums over the cube, coefficients from the
values at 0, 1, -1: for tests, and for whoever strings a whole prover together. Tested, at K = 2 and
K = 3 in field 2 and K = 2 in field 1: every constant got back is the honest one; the three rows
hold; with one entry of c made false row (U) fails, the two others hold.

Limits: this file does not say that these formulas are what the programs compute: they follow that
description, which is one reading of the code (by one writer), and their sources include no file of
the programs. The programs' own proof files of this toy have gone through the whole decision, of
which this block is a part: the verdicts on honest, altered and false files (Fmt/M1FullProg*.lean,
Run/M1Engine*.lean) and the nineteen intermediate values that the programs print
(Fmt/M1Targets.lean; compared in Fmt/M1FullProgPTv.lean, Fmt/M1FullProgPRv.lean,
Fmt/M1FullProgPFv.lean) agree: tests when these files compile, no theorem. In Fmt/ and Run/ no
altered file of the programs is shown to reach the decision: in Fmt/M1FullProg*.lean the reader
refuses each of them, before the decision is run (`whoF`, Fmt/M1Full.lean), and an outcome in
Run/M1Engine*.lean does not tell which check of the compiled verifier failed. None of the nineteen
values is this block's own: the first is the target of the row into which this block's three rows
and the sample row are combined (Fmt/M1Targets.lean: `targets`). This file says nothing on
soundness. It says nothing on canonical form, missing items, "never 0": the reader's and the
drawing's rules. It does not say that lzk leaves room for 2 K + 5 entries and the pad: `pscRoom` is
that condition; nobody asks it here.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1Types

set_option autoImplicit false

namespace Fmt.M1

/-! ## The verifier in PSC -/

/-- what the prover sends -/
structure PscMsg where
  mu : E
  q  : List (E × E)
  p  : E × E
  v  : E × E

/-- what is drawn -/
structure PscDraw where
  eps   : E
  gamma : List E
  beta  : E

def pscFits (K : Nat) (zeta : List E) (m : PscMsg) (d : PscDraw) : Bool :=
  zeta.length == K && m.q.length == K && d.gamma.length == K

/-- the constant that is left out of a round in X -/
def constX (f : Fld) (R zeta : E) (q : E × E) : E := f.subE R (f.mulE zeta (f.addE q.1 q.2))

/-- a polynomial of three coefficients at a point -/
def at3 (f : Fld) (c0 c1 c2 x : E) : E := f.addE c0 (f.addE (f.mulE c1 x) (f.mulE c2 (f.mulE x x)))

/-- One round in X: from the claim R to the next claim. -/
def stepX (f : Fld) (R zeta : E) (q : E × E) (gamma : E) : E :=
  at3 f (constX f R zeta q) q.1 q.2 gamma

/-- the rounds in X; it ends where one of the three lists ends -/
def runX (f : Fld) : E → List E → List (E × E) → List E → E
  | R, z :: zs, q :: qs, g :: gs => runX f (stepX f R z q g) zs qs gs
  | R, _, _, _ => R

/-- the constants got back in the rounds in X -/
def constsX (f : Fld) : E → List E → List (E × E) → List E → List E
  | R, z :: zs, q :: qs, g :: gs => constX f R z q :: constsX f (stepX f R z q g) zs qs gs
  | _, _, _, _ => []

/-- the claim at the start -/
def pscR0 (f : Fld) (T : E) (m : PscMsg) (d : PscDraw) : E := f.addE m.mu (f.mulE d.eps T)

/-- the claim after the rounds in X: it is the constant of the round in Y -/
def pscRK (f : Fld) (T : E) (zeta : List E) (m : PscMsg) (d : PscDraw) : E :=
  runX f (pscR0 f T m d) zeta m.q d.gamma

/-- the claim at the end -/
def pscR (f : Fld) (T : E) (zeta : List E) (m : PscMsg) (d : PscDraw) : E :=
  at3 f (pscRK f T zeta m d) m.p.1 m.p.2 d.beta

/-- all constants that were got back: K in X, one in Y -/
def leftOut (f : Fld) (T : E) (zeta : List E) (m : PscMsg) (d : PscDraw) : List E :=
  constsX f (pscR0 f T m d) zeta m.q d.gamma ++ [pscRK f T zeta m d]

/-- What the verifier keeps. -/
structure PscOut where
  gamma : List E
  beta  : E
  eps   : E
  R     : E
  v1    : E
  v2    : E

/-- ZERO's claim (target 0) taken through PSC: what the verifier keeps. -/
def pscStep (f : Fld) (zeta : List E) (m : PscMsg) (d : PscDraw) : PscOut :=
  ⟨d.gamma, d.beta, d.eps, pscR f Fld.zeroE zeta m d, m.v.1, m.v.2⟩

/-- how many mask entries are taken; as many scalars are sent -/
def pscTakes (K : Nat) : Nat := 2 * K + 5

/-- the mask row has room for what is taken and for the pad at its last place -/
def pscRoom (K lzk first : Nat) : Bool := decide (first + pscTakes K + 1 ≤ lzk)

/-- the coefficient of row (U) on the t-th of the entries that are taken -/
def maskU (f : Fld) (K : Nat) (o : PscOut) (t : Nat) : E :=
  if t < 2 * K then
    (if t % 2 = 0 then o.gamma.getD (t / 2) Fld.zeroE
      else f.mulE (o.gamma.getD (t / 2) Fld.zeroE) (o.gamma.getD (t / 2) Fld.zeroE))
  else if t = 2 * K then Fld.oneE
  else if t = 2 * K + 1 then o.beta
  else if t = 2 * K + 2 then f.mulE o.beta o.beta
  else Fld.zeroE

/-- a vector on the mask row's lzk entries from the coefficients on the entries that are taken -/
def onMask (lzk first : Nat) (g : Nat → E) : Array E :=
  Array.ofFn (n := lzk) fun i => if first ≤ i.val then g (i.val - first) else Fld.zeroE

/-- Row (U): the hiding polynomial and c. -/
def rowU (f : Fld) (K lzk : Nat) (o : PscOut) (first : Nat := 0) : GRow :=
  ⟨pv f (f.negE o.eps) (bitsE 2 2 ++ o.gamma),
    onMask lzk first (maskU f K o),
    f.subE o.R (f.mulE o.eps (f.mulE o.v1 o.v2))⟩

/-- Row (E_1): a at the point. -/
def rowE1 (f : Fld) (K lzk : Nat) (o : PscOut) (first : Nat := 0) : GRow :=
  ⟨pv f Fld.oneE (bitsE 2 0 ++ o.gamma),
    onMask lzk first (fun t => if t = 2 * K + 3 then o.beta else Fld.zeroE),
    o.v1⟩

/-- Row (E_2): b at the point. -/
def rowE2 (f : Fld) (K lzk : Nat) (o : PscOut) (first : Nat := 0) : GRow :=
  ⟨pv f Fld.oneE (bitsE 2 1 ++ o.gamma),
    onMask lzk first (fun t => if t = 2 * K + 4 then o.beta else Fld.zeroE),
    o.v2⟩

/-- The three rows, in the order in which they are batched. -/
def pscRows (f : Fld) (K lzk : Nat) (o : PscOut) (first : Nat := 0) : GRow × GRow × GRow :=
  (rowU f K lzk o first, rowE1 f K lzk o first, rowE2 f K lzk o first)

/-- The block on plain arguments: K, the mask row's length; zeta; mu'; the K pairs; (p_1, p_2);
(v_1, v_2); eps; gamma; beta: the three rows in the order in which they are batched. -/
def pscBlock (f : Fld) (K lzk : Nat) (zeta : List E) (mu : E) (qs : List (E × E)) (p v : E × E)
    (eps : E) (gamma : List E) (beta : E) : List GRow :=
  let r := pscRows f K lzk (pscStep f zeta ⟨mu, qs, p, v⟩ ⟨eps, gamma, beta⟩)
  [r.1, r.2.1, r.2.2]

/-- a row holds at a main table and a mask table that are written out -/
def GRow.holdsAt (f : Fld) (r : GRow) (table mask : Array E) : Bool :=
  f.addE (dot f r.c table) (dot f r.d mask) == r.t

/-! ## A prover of this library's own, from the definition -/

namespace PscHon

/-- the multilinear extension of a vector at a point -/
def mle (f : Fld) (u : Array E) (x : List E) : E := dot f (eqTab f x) u

/-- what the prover holds: three vectors of 2^K entries; the mask row's entries -/
structure Wit where
  a : Array E
  b : Array E
  c : Array E
  m : Array E

/-- the part of the hiding polynomial in the variables X -/
def hidX (f : Fld) (w : Wit) : Nat → List E → E
  | _, [] => Fld.zeroE
  | t, x :: xs =>
    f.addE (f.addE (f.mulE (ent w.m t) x) (f.mulE (ent w.m (t + 1)) (f.mulE x x)))
      (hidX f w (t + 2) xs)

/-- the hiding polynomial -/
def hid (f : Fld) (w : Wit) (K : Nat) (x : List E) (y : E) : E :=
  f.addE (hidX f w 0 x) (at3 f (ent w.m (2 * K)) (ent w.m (2 * K + 1)) (ent w.m (2 * K + 2)) y)

/-- the polynomial on which the sum-check runs -/
def poly (f : Fld) (w : Wit) (K : Nat) (eps : E) (x : List E) (y : E) : E :=
  f.addE (hid f w K x y)
    (f.mulE eps
      (f.subE (f.mulE (f.addE (mle f w.a x) (f.mulE (ent w.m (2 * K + 3)) y))
          (f.addE (mle f w.b x) (f.mulE (ent w.m (2 * K + 4)) y))) (mle f w.c x)))

/-- the way of summing over variables X with their zetas -/
def sumW (f : Fld) : List E → (List E → E) → E
  | [], g => g []
  | z :: zs, g =>
    f.addE (f.mulE (f.subE Fld.oneE z) (sumW f zs fun xs => g (Fld.zeroE :: xs)))
      (f.mulE z (sumW f zs fun xs => g (Fld.oneE :: xs)))

/-- the three coefficients of a polynomial of degree at most 2, from its values at 0, 1, -1 -/
def coef3 (f : Fld) (g : E → E) : E × E × E :=
  let g0 := g Fld.zeroE
  let g1 := g Fld.oneE
  let gm := g (f.negE Fld.oneE)
  let half := f.inv 2
  (g0, f.scaleE half (f.subE g1 gm), f.subE (f.scaleE half (f.addE g1 gm)) g0)

/-- the round polynomials in X; gone: the challenges so far -/
def roundsX (f : Fld) (w : Wit) (K : Nat) (eps : E) : List E → List E → List E → List (E × E × E)
  | _, [], _ => []
  | _, _ :: _, [] => []
  | gone, _ :: zs, g :: gs =>
    coef3 f (fun t => sumW f zs fun xs => poly f w K eps (gone ++ t :: xs) Fld.zeroE) ::
      roundsX f w K eps (gone ++ [g]) zs gs

/-- The honest messages, with all three coefficients of every round. -/
def full (f : Fld) (w : Wit) (K : Nat) (zeta : List E) (d : PscDraw) :
    E × List (E × E × E) × (E × E × E) × (E × E) :=
  (sumW f zeta fun xs => hid f w K xs Fld.zeroE,
    roundsX f w K d.eps [] zeta d.gamma,
    coef3 f fun t => poly f w K d.eps d.gamma t,
    (f.addE (mle f w.a d.gamma) (f.mulE d.beta (ent w.m (2 * K + 3))),
      f.addE (mle f w.b d.gamma) (f.mulE d.beta (ent w.m (2 * K + 4)))))

/-- what is sent of them -/
def msg (f : Fld) (w : Wit) (K : Nat) (zeta : List E) (d : PscDraw) : PscMsg :=
  let x := full f w K zeta d
  ⟨x.1, x.2.1.map fun c => (c.2.1, c.2.2), (x.2.2.1.2.1, x.2.2.1.2.2), x.2.2.2⟩

/-- the constants that are not sent -/
def consts (f : Fld) (w : Wit) (K : Nat) (zeta : List E) (d : PscDraw) : List E :=
  let x := full f w K zeta d
  x.2.1.map (·.1) ++ [x.2.2.1.1]

/-- the main table: entry (row r, place i) at r + 4 i; row 3 is 0 -/
def table (w : Wit) : Array E := Array.ofFn (n := 4 * w.a.size) fun j =>
  if j.val % 4 = 0 then ent w.a (j.val / 4)
  else if j.val % 4 = 1 then ent w.b (j.val / 4)
  else if j.val % 4 = 2 then ent w.c (j.val / 4)
  else Fld.zeroE

/-- made-up elements: no randomness, only values that are no special cases -/
def el (f : Fld) (s : Nat) : E :=
  (f.red (s * s * 1000003 + 7 * s + 11), f.red (s * 998244353 + 5), f.red (s * s * s + 13))

/-- a witness with a b = c; rows over the base field; a mask row of lzk entries -/
def wit (f : Fld) (K lzk s : Nat) : Wit where
  a := Array.ofFn (n := 2 ^ K) fun i => Fld.ofF (el f (s + i.val)).1
  b := Array.ofFn (n := 2 ^ K) fun i => Fld.ofF (el f (s + 100 + i.val)).1
  c :=
    Array.ofFn (n := 2 ^ K) fun i => Fld.ofF (f.mul (el f (s + i.val)).1 (el f (s + 100 + i.val)).1)
  m := Array.ofFn (n := lzk) fun t => el f (s + 200 + t.val)

/-- the same with one entry of c made false -/
def bad (f : Fld) (w : Wit) (i : Nat) : Wit :=
  { w with c := w.c.setIfInBounds i (f.addE (ent w.c i) Fld.oneE) }

def zetas (f : Fld) (K s : Nat) : List E := (List.range K).map fun j => el f (s + 300 + j)
def draws (f : Fld) (K s : Nat) : PscDraw :=
  ⟨el f (s + 400), (List.range K).map fun j => el f (s + 500 + j), el f (s + 600)⟩

/-- one trial: the lists fit; the constants got back are the honest ones; which of the three rows
hold -/
def trial (f : Fld) (K s : Nat) (w : Wit) : Bool × Bool × List Bool :=
  let z := zetas f K s
  let d := draws f K s
  let m := msg f w K z d
  let r := pscRows f K w.m.size (pscStep f z m d)
  (pscFits K z m d,
    leftOut f Fld.zeroE z m d == consts f w K z d,
    [r.1.holdsAt f (table w) w.m, r.2.1.holdsAt f (table w) w.m, r.2.2.holdsAt f (table w) w.m])

end PscHon

/-! ## Tests -/

-- the numbers of the text: 29 scalars, 29 mask entries at K = 12; a mask row of 32 entries has room
-- for them and the pad, one of 29 has not
#guard pscTakes 12 == 29 && pscRoom 12 32 0 && pscRoom 12 30 0 && !pscRoom 12 29 0
-- the sizes of the rows; at K = 12: 2^14 and 32
#guard (let r := pscRows .two 12 32 (pscStep .two (PscHon.zetas .two 12 1) ⟨Fld.zeroE, [], (Fld.zeroE, Fld.zeroE), (Fld.zeroE, Fld.zeroE)⟩ (PscHon.draws .two 12 1)); [r.1.c.size, r.2.1.c.size, r.2.2.c.size, r.1.d.size, r.2.1.d.size, r.2.2.d.size]) == [16384, 16384, 16384, 32, 32, 32]
-- each of the 29 entries is used by exactly one of the three rows; the three last places, the pad's
-- among them, by none
#guard (let r := pscRows .two 12 32 (pscStep .two (PscHon.zetas .two 12 1) ⟨Fld.zeroE, [], (Fld.zeroE, Fld.zeroE), (Fld.zeroE, Fld.zeroE)⟩ (PscHon.draws .two 12 1)); (List.range 32).map fun t => ([r.1.d, r.2.1.d, r.2.2.d].filter fun d => ent d t != Fld.zeroE).length) == List.replicate 29 1 ++ [0, 0, 0]
-- a row's coefficients on the main table stand on its own row of the table alone
#guard (let r := pscRows .two 2 16 (pscStep .two (PscHon.zetas .two 2 1) ⟨Fld.zeroE, [], (Fld.zeroE, Fld.zeroE), (Fld.zeroE, Fld.zeroE)⟩ (PscHon.draws .two 2 1)); (List.range 16).all fun j => (ent r.1.c j != Fld.zeroE) == (j % 4 == 2) && (ent r.2.1.c j != Fld.zeroE) == (j % 4 == 0) && (ent r.2.2.c j != Fld.zeroE) == (j % 4 == 1))
-- a ledger that starts later (first = 3): row (U)'s coefficients d stand three places later
#guard (let o := pscStep .two (PscHon.zetas .two 2 1) ⟨Fld.zeroE, [], (Fld.zeroE, Fld.zeroE), (Fld.zeroE, Fld.zeroE)⟩ (PscHon.draws .two 2 1); (List.range 13).all fun t => ent (rowU .two 2 16 o 3).d (t + 3) == ent (rowU .two 2 16 o).d t)
-- an honest run: the constants come back; the three rows hold
#guard PscHon.trial .two 2 1 (PscHon.wit .two 2 16 1) == (true, true, [true, true, true])
#guard PscHon.trial .two 3 7 (PscHon.wit .two 3 16 7) == (true, true, [true, true, true])
#guard PscHon.trial .one 2 3 (PscHon.wit .one 2 16 3) == (true, true, [true, true, true])
-- the block on plain arguments: its three rows hold in the honest run
#guard (let z := PscHon.zetas .two 2 1; let d := PscHon.draws .two 2 1; let m := PscHon.msg .two (PscHon.wit .two 2 16 1) 2 z d
  (pscBlock .two 2 16 z m.mu m.q m.p m.v d.eps d.gamma d.beta).map fun r => r.holdsAt .two (PscHon.table (PscHon.wit .two 2 16 1)) (PscHon.wit .two 2 16 1).m) == [true, true, true]
-- one entry of c false, the prover going on by the same rules: row (U) fails, the two others hold
#guard (PscHon.trial .two 2 1 (PscHon.bad .two (PscHon.wit .two 2 16 1) 2)).2.2 == [false, true, true]
#guard (PscHon.trial .two 3 7 (PscHon.bad .two (PscHon.wit .two 3 16 7) 5)).2.2 == [false, true, true]
#guard (PscHon.trial .one 2 3 (PscHon.bad .one (PscHon.wit .one 2 16 3) 0)).2.2 == [false, true, true]

end Fmt.M1
