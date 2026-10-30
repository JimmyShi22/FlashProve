-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/LookDefs.lean

The prover's side of a lookup argument as plain data: for each round the scalars sent and the
elements drawn, as one term of the public numbers, the keys, the bits of the counts, the mask
entries and the challenges. Definitions alone, all but the propositions with code. No theorem.

What it is written against. Cb/Pv/Lookup/Out/TwV.lean has a function on plain data, written after
the lookup's verifier: TwV.traceOfFlat reads a list of rounds (TwV.Rounds), TwV.rowsOfTrace makes of
it a list of linear claims on entries (rows). OnBytes/Tie/Pv/Lookup/Forest/FoClaims.lean makes of
these the list Fo.claimsOf of a sub-proof's lookup. This file defines rounds that are meant to make
all these claims hold, at the caller's values that belong to them. That they do is for the files
that import this one to state and prove.

The parts.
1. One sumcheck on lists: "evalP", "wsum", "Chained" (a run of round polynomials), "scRounds".
2. The polynomial H of the mask entries (TwV.hide) over such a run: "wCoef", "hTail", "maskedGo";
   what is sent: "sentGo", "honSc".
3. "Job": what a caller of the masked sumcheck knows of its summand: the points, the degrees, the
   true sum, the round polynomials, the end values, the polynomial in the further variable Y.
   "Job.Lawful": the run from the true sum to the summand at the shown values.
4. The cube: "ext" (the multilinear extension, coordinate i with bit i, as TwV.eqN), "setBit",
   "fixAt", "foldN", "wtN", "pjRound", and "pj": the job of κ + A B under equality weights, for any
   order of the variables.
5. "Data": TwV's public numbers N, a joint key vector, bits, and the point of comparison al; its
   values "Z", "G", "Pc", "a", "kLvl", "tLvl"; the jobs "tieJob", "keyJob", "tabJob", "leavesJob",
   "bitsJob".
6. "Chal": every other draw, as an argument. "rsT": the rounds. "trT": the value of TwV.Trace that
   TwV.traceOfFlat is meant to read off them. "PremT": the premises of the statements on them.
7. "dataF", "rsF", "PremF": the same at the numbers Fo.numsF h lm jLK θ of a sub-proof's lookup.
In the names, the ending T is for "over TwV.Nums", the ending F for "at Fo.numsF". Further
definitions, which the files that import this one cite: "runJob" (a job's masked rounds), "scJob",
"shownOf", "masksOf", "keyPt", "tabPt" (the points), "tieShown", "gShown" (shown values), "tieTg",
"keyTg", "tabTg" (the targets).

Notation. 2^v keys, v = N.v' + 1; 2^d rows of the joint table; 2^w planes, of which n + 2 count. A
list of a sumcheck's challenges is by round, that of Y last. An order o is a list of coordinates:
round j takes coordinate o[j]. μ and ν read places; the mask entries are what they read at the
places of TwV.Led.

Limits. These are specifications, not programs for real sizes: behind l rounds "pjRound" costs about
2^m times 2^l steps. The mask entries and all challenges are arguments: nothing is drawn. Lists that
are too short are read with defaults, as in TwV.lean. The terms are written for n + 2 = 2^w
(PremT.planes): for j > n + 1 "gShown" repeats plane n + 1. The correspondence with the byte
format's page docs/format/11-1-machinery.md is by reading; no statement of this file compares a term
with a program.

Not claimed: anything. In particular not that a prover's program sends these scalars, that a
verifier accepts them, or anything on what they show of the keys.

-/
import Johnson.HonestTrace.CountsProducts

set_option autoImplicit false

namespace OnBytes.HonestTrace.Look

open Finset TwV
open OnBytes.Model
open Cb.Lkp

section
variable {K : Type} [Field K] {P : Type}

/-! ## 1 · One sumcheck on plain lists, without a word on masks -/

/-- The value at x of the polynomial with the coefficients q, lowest first. -/
def evalP (q : List K) (x : K) : K := q.headD 0 + evalGo x 0 q.tail

/-- (1 - z) q(0) + z q(1): the sum of q in an equality round at z; at z = 0: q(0), Y's round. -/
def wsum (z : K) (q : List K) : K := q.headD 0 + z * q.tail.sum

/-- A run of round polynomials: the first sums to σ, each later one to the value of the one in front
at its challenge, and the last one's value at its challenge is fin. "Sums" is wsum at the round's z.
Lists of unequal lengths: False. -/
def Chained : K → List K → List (List K) → List K → K → Prop
  | σ, [], [], [], fin => fin = σ
  | σ, z :: zs, q :: qs, x :: xs, fin => wsum z q = σ ∧ Chained (evalP q x) zs qs xs fin
  | _, _, _, _, _ => False

/-- The rounds of one sumcheck as TwV.takeSc reads them: (hs, eps); for each variable all
coefficients but the constant, and its challenge; the values' round if there is one. -/
def scRounds (hs eps : K) (qs : List (List K)) (xs : List K) (vals : Option (List K)) : Rounds K :=
  ([hs], [eps]) :: List.zipWith (fun q x => (q.tail, [x])) qs xs ++
    (match vals with
     | some v => [(v, [])]
     | none => [])

/-! ## 2 · The mask entries' polynomial H laid over a chained run -/

/-- The coefficients of the powers 1 .. n of H's part in round r. -/
def wCoef (L : Led P) (μ : P → K) (r n : ℕ) : List K := (List.range n).map fun t => μ (L.pw r t)

/-- The parts of the rounds from r on, each summed under its weights (z times the sum of its
coefficients), added up. -/
def hTail (L : Led P) (μ : P → K) : ℕ → List ℕ → List K → K
  | r, n :: dg, z :: zs => z * (wCoef L μ r n).sum + hTail L μ (r + 1) dg zs
  | _, _, _ => 0

/-- The sum of two polynomials. -/
def addP : List K → List K → List K
  | [], b => b
  | a, [] => a
  | x :: a, y :: b => (x + y) :: addP a b

/-- The masked round polynomials: H's round polynomial plus eps (g + c), c the shown target less the
true sum. acc: H's constant and its parts at the challenges in front. -/
def maskedGo (L : Led P) (μ : P → K) (eps c : K) :
    ℕ → K → List ℕ → List K → List (List K) → List K → List (List K)
  | r, acc, n :: dg, _ :: zs, g :: gs, x :: xs =>
    addP ((acc + hTail L μ (r + 1) dg zs) :: wCoef L μ r n)
        ((eps * (g.headD 0 + c)) :: g.tail.map (eps * ·)) ::
      maskedGo L μ eps c (r + 1) (acc + evalGo x 0 (wCoef L μ r n)) dg zs gs xs
  | _, _, _, _, _, _ => []

/-- What is sent in the variables' rounds: of H's part plus eps g all coefficients but the constant.
No target and no sum is read. -/
def sentGo (L : Led P) (μ : P → K) (eps : K) : ℕ → List ℕ → List (List K) → List K → Rounds K
  | r, n :: dg, g :: gs, x :: xs =>
    (addP (wCoef L μ r n) (g.tail.map (eps * ·)), [x]) :: sentGo L μ eps (r + 1) dg gs xs
  | _, _, _, _ => []

/-- **One masked sumcheck's rounds**: of the mask entries μ at L's places, the summand's round
polynomials gs, and the challenges: (the sum of H, eps); the variables' rounds; the values'. -/
def honSc (L : Led P) (μ : P → K) (dg : List ℕ) (zs : List K) (eps : K)
    (gs : List (List K)) (xs : List K) (vals : Option (List K)) : Rounds K :=
  ([μ L.c0 + hTail L μ 0 dg zs], [eps]) :: sentGo L μ eps 0 dg gs xs ++
    (match vals with
     | some v => [(v, [])]
     | none => [])

/-! ## 3 · What a caller of the masked sumcheck knows of its summand -/

/-- What a caller of the masked sumcheck knows of its summand. All lists of challenges are by
round. -/
structure Job (K : Type) where
  /-- the equality coordinate of each variable, by round (Y not among them) -/
  zs : List K
  /-- the degree of each variable's round -/
  dg : List ℕ
  /-- the degree in Y; none: no end values -/
  dY : Option ℕ
  /-- the true sum (at tie step 0: written as 0, see tieJob) -/
  sum : K
  /-- the summand's round polynomial in the next variable, all coefficients, of the challenges in
  front -/
  round : List K → List K
  /-- the summand at the point of all challenges -/
  fin : List K → K
  /-- the true end values, of all variables' challenges -/
  ends : List K → List K
  /-- the polynomial in Y, of all variables' challenges and the end values' mask entries -/
  inY : List K → List K → List K
  /-- the summand at shown values -/
  S0 : List K → K

/-- The round polynomials along given challenges. -/
def Job.gs (J : Job K) (xs : List K) : List (List K) :=
  (List.range J.zs.length).map fun l => J.round (xs.take l)

/-- v + β m, entry by entry. -/
def shownL (β : K) (v m : List K) : List K := List.zipWith (fun a b => a + β * b) v m

/-- For all challenges xs, one a variable: the round polynomials are Chained from the true sum to
the summand at the point. And, where there are end values, for all lists m of their number and all
β: the polynomial in Y is the summand at the point at 0, and at β the summand at the end values plus
β m. -/
def Job.Lawful (J : Job K) : Prop :=
  (∀ xs : List K, xs.length = J.zs.length → Chained J.sum J.zs (J.gs xs) xs (J.fin xs)) ∧
  (J.dY.isSome → ∀ (xs m : List K) (β : K), xs.length = J.zs.length →
    m.length = (J.ends xs).length →
    wsum 0 (J.inY xs m) = J.fin xs ∧ evalP (J.inY xs m) β = J.S0 (shownL β (J.ends xs) m))

/-! ## 4 · The cube -/

/-- The multilinear extension of the first 2^m entries of f at pt, coordinate i with bit i, for pt
of m coordinates. -/
def ext (m : ℕ) (f : ℕ → K) (pt : List K) : K := ∑ X ∈ range (2 ^ m), eqN pt X * f X

/-- x with bit c put to b. -/
def setBit : ℕ → Bool → ℕ → ℕ
  | 0, b, x => 2 * (x / 2) + b.toNat
  | c + 1, b, x => 2 * setBit c b (x / 2) + x % 2

/-- f with coordinate c taken at r: a function that no longer reads bit c. -/
def fixAt (c : ℕ) (r : K) (f : ℕ → K) : ℕ → K := fun X =>
  (1 - r) * f (setBit c false X) + r * f (setBit c true X)

/-- f behind l rounds: coordinate o[i] taken at rs[i], for i below l. o: round j takes coordinate
o[j]. -/
def foldN (o : List ℕ) (rs : List K) (f : ℕ → K) : ℕ → ℕ → K
  | 0 => f
  | l + 1 => fixAt (o.getD l 0) (rs.getD l 0) (foldN o rs f l)

/-- The equality weights behind l rounds: 0 at the coordinates taken, so that one corner of them
counts. -/
def wtN (o : List ℕ) (z : List K) : ℕ → List K
  | 0 => z
  | l + 1 => (wtN o z l).set (o.getD l 0) 0

/-- The round polynomial of κ + A B under equality weights, behind the rounds with the challenges
rs: three coefficients. The weight of the round's own coordinate is not in it: wsum at that
coordinate is its sum. -/
def pjRound (m : ℕ) (κ : K) (A B : ℕ → K) (o : List ℕ) (z rs : List K) : List K :=
  let c := o.getD rs.length 0
  let w := fun X => eqN (wtN o z (rs.length + 1)) X
  let a0 := fun X => foldN o rs A rs.length (setBit c false X)
  let a1 := fun X => foldN o rs A rs.length (setBit c true X) -
    foldN o rs A rs.length (setBit c false X)
  let b0 := fun X => foldN o rs B rs.length (setBit c false X)
  let b1 := fun X => foldN o rs B rs.length (setBit c true X) -
    foldN o rs B rs.length (setBit c false X)
  [∑ X ∈ range (2 ^ m), w X * (κ + a0 X * b0 X),
   ∑ X ∈ range (2 ^ m), w X * (a0 X * b1 X + a1 X * b0 X),
   ∑ X ∈ range (2 ^ m), w X * (a1 X * b1 X)]

/-- The sumcheck of κ + A B over m variables under equality weights at z, taken in the order o, with
the end values A and B at the point. -/
def pj (m : ℕ) (κ : K) (A B : ℕ → K) (o : List ℕ) (z : List K) : Job K where
  zs := inRounds o z
  dg := List.replicate m 2
  dY := some 2
  sum := ∑ X ∈ range (2 ^ m), eqN z X * (κ + A X * B X)
  round := pjRound m κ A B o z
  fin := fun xs => κ + ext m A (byVar o xs) * ext m B (byVar o xs)
  ends := fun xs => [ext m A (byVar o xs), ext m B (byVar o xs)]
  inY := fun xs mk =>
    let a := ext m A (byVar o xs)
    let b := ext m B (byVar o xs)
    [κ + a * b, a * mk.getD 1 0 + mk.getD 0 0 * b, mk.getD 0 0 * mk.getD 1 0]
  S0 := fun v => κ + v.getD 0 0 * v.getD 1 0

/-! ## 5 · The lookup's sumchecks, as jobs, over TwV.Nums -/

/-- What a lookup is about: the public numbers of TwV's function; the joint key vector (2^(v' + 1)
keys); the bits (row u of the joint table, plane j); the point of comparison. -/
structure Data (P K : Type) where
  N : Nums P K
  key : ℕ → K
  bits : ℕ → ℕ → K
  al : K

namespace Data
variable (D : Data P K)

/-- The number of bits of a key's index. -/
def v : ℕ := D.N.v' + 1
/-- Z, the key side's root. -/
def Z : K := keyProd D.v D.key D.al
/-- G_j, the root of plane j. -/
def G (j : ℕ) : K := tabProd D.N.d D.N.tab D.bits D.al j
/-- P_s: G_(n+1) for s = n + 1; P_(s+1)^2 G_s below; above n + 1 it is G_s. -/
def Pc (s : ℕ) : K := Alg.Lookup.chainFrom D.G (D.N.n + 1 - s) s
/-- The public factor of the padding: the product of (al - tab row)^count over the pairs (row,
count) of N.pads. -/
def a : K := padFac D.N.tab D.N.pads D.al
/-- Level m of the key side's tree, m ≤ v. -/
def kLvl (m X : ℕ) : K := Blocks.lvl 0 D.v (facK D.key D.al) m X
/-- Level l of the table side's tree, l ≤ d: w + l variables. -/
def tLvl (l X : ℕ) : K := Blocks.lvl D.N.w D.N.d (facT D.N.w D.N.tab D.bits D.al) l X
/-- The bit at the leaf (u | j). -/
def bitAt (X : ℕ) : K := D.bits (X / 2 ^ D.N.w) (X % 2 ^ D.N.w)
/-- al - 1 - the row's value, at the leaf (u | j). -/
def rowAt (X : ℕ) : K := D.al - 1 - D.N.tab (X / 2 ^ D.N.w)
/-- The relation after the challenge, Cb.Lkp.MidP: every bit is 0 or 1; weighted by 2^j the bits add
up to 2^v less the number of padding keys; the product of (al - key) over the keys is the padding's
factor times the product of the G_j^(2^j). -/
def Mid : Prop := MidP D.v D.N.d D.N.w (D.N.n + 2) D.key D.N.tab D.N.pads D.bits D.al

end Data

/-- (p + Y m1)^2 (g + Y m2), four coefficients. -/
def sqMul (p g m1 m2 : K) : List K :=
  [p ^ 2 * g, 2 * p * m1 * g + p ^ 2 * m2, m1 ^ 2 * g + 2 * p * m1 * m2, m1 ^ 2 * m2]

/-- Tie step s ≤ n: no variable but Y. Step 0: end values Z, P_1, G_0, summand Z - a P_1^2 G_0, sum
written as 0 (what it is under Data.Mid). Step s > 0: end values P_(s+1), G_s, summand P_(s+1)^2
G_s, sum P_s. -/
def tieJob (D : Data P K) (s : ℕ) : Job K where
  zs := []
  dg := []
  dY := some 3
  sum := if s = 0 then 0 else D.Pc s
  round := fun _ => []
  fin := fun _ => if s = 0 then 0 else D.Pc s
  ends := fun _ => if s = 0 then [D.Z, D.Pc 1, D.G 0] else [D.Pc (s + 1), D.G s]
  inY := fun _ m =>
    if s = 0 then
      addP [D.Z, m.getD 0 0] ((sqMul (D.Pc 1) (D.G 0) (m.getD 1 0) (m.getD 2 0)).map (-D.a * ·))
    else sqMul (D.Pc (s + 1)) (D.G s) (m.getD 0 0) (m.getD 1 0)
  S0 := fun x =>
    if s = 0 then x.getD 0 0 - D.a * (x.getD 1 0 ^ 2 * x.getD 2 0) else x.getD 0 0 ^ 2 * x.getD 1 0

/-- Key level l, at the point z of l coordinates. -/
def keyJob (D : Data P K) (l : ℕ) (z : List K) : Job K :=
  pj l 0 (D.kLvl (l + 1)) (fun X => D.kLvl (l + 1) (X + 2 ^ l)) (D.N.oK l) z

/-- Table level l, at the point z of w + l coordinates. -/
def tabJob (D : Data P K) (l : ℕ) (z : List K) : Job K :=
  pj (D.N.w + l) 0 (D.tLvl (l + 1)) (fun X => D.tLvl (l + 1) (X + 2 ^ (D.N.w + l))) (D.N.oT l) z

/-- The leaves: 1 + b (al - 1 - row); no end value; degree 1 in the plane's coordinates. -/
def leavesJob (D : Data P K) (z : List K) : Job K :=
  { pj (D.N.w + D.N.d) 1 D.bitAt D.rowAt D.N.oE z with
    dg := dgE D.N
    dY := none
    round := fun rs =>
      (pjRound (D.N.w + D.N.d) 1 D.bitAt D.rowAt D.N.oE z rs).take
        (if D.N.oE.getD rs.length 0 < D.N.w then 2 else 3)
    ends := fun _ => []
    inY := fun _ _ => [] }

/-- The bits: b (b - 1); one end value, the planes at the point. -/
def bitsJob (D : Data P K) (z : List K) : Job K :=
  { pj (D.N.w + D.N.d) 0 D.bitAt (fun X => D.bitAt X - 1) D.N.oB z with
    ends := fun xs => [ext (D.N.w + D.N.d) D.bitAt (byVar D.N.oB xs)]
    inY := fun xs m =>
      let b := ext (D.N.w + D.N.d) D.bitAt (byVar D.N.oB xs)
      [b * (b - 1), m.getD 0 0 * (2 * b - 1), m.getD 0 0 ^ 2]
    S0 := fun x => x.getD 0 0 * (x.getD 0 0 - 1) }

/-! ## 6 · The challenges as arguments; the rounds and the trace -/

/-- All that is drawn in a lookup but the shift and al. Lists of a sumcheck's challenges are by
round, Y's last. -/
structure Chal (K : Type) where
  /-- eps of tie step s -/
  tieE : ℕ → K
  /-- Y's challenge of tie step s -/
  tieB : ℕ → K
  /-- the point at which the planes' roots are joined: w coordinates, bit 0's first -/
  join : List K
  /-- eps of key level l -/
  keyE : ℕ → K
  /-- the challenges of key level l, by round, Y's last -/
  keyX : ℕ → List K
  /-- the line's draw behind key level l -/
  keyR : ℕ → K
  /-- eps of table level l -/
  tabE : ℕ → K
  /-- the challenges of table level l, by round, Y's last -/
  tabX : ℕ → List K
  /-- the line's draw behind table level l -/
  tabR : ℕ → K
  /-- eps of the leaves' sumcheck -/
  clsE : K
  /-- its challenges, by round -/
  clsX : List K
  /-- the point of the bits' sumcheck: w + d coordinates, bit 0's first -/
  zero : List K
  /-- eps of the bits' sumcheck -/
  bitE : K
  /-- its challenges, by round, Y's last -/
  bitX : List K

/-- The lists have one entry for each coordinate of their point, or for each round of their sumcheck
(Y's among them). -/
structure Chal.Fits (C : Chal K) (v d w : ℕ) : Prop where
  join : C.join.length = w
  keyX : ∀ l < v, (C.keyX l).length = l + 1
  tabX : ∀ l < d, (C.tabX l).length = w + l + 1
  clsX : C.clsX.length = w + d
  zero : C.zero.length = w + d
  bitX : C.bitX.length = w + d + 1

/-- The mask entries of n shown values. -/
def masksOf (L : Led P) (μ : P → K) (n : ℕ) : List K := (List.range n).map fun i => μ (L.sh i)

/-- The shown values of a job at challenges xs (Y's last). -/
def shownOf (L : Led P) (μ : P → K) (J : Job K) (xs : List K) : List K :=
  shownL (xs.getLastD 0) (J.ends xs.dropLast) (masksOf L μ (J.ends xs.dropLast).length)

/-- A job's masked rounds. xs: all its challenges, Y's last where it has end values. -/
def runJob (L : Led P) (μ : P → K) (J : Job K) (eps : K) (xs : List K) : Rounds K :=
  match J.dY with
  | some dY =>
    honSc L μ (J.dg ++ [dY]) (J.zs ++ [0]) eps
      (J.gs xs.dropLast ++ [J.inY xs.dropLast (masksOf L μ (J.ends xs.dropLast).length)]) xs
      (some (shownOf L μ J xs))
  | none => honSc L μ J.dg J.zs eps (J.gs xs) xs none

/-- What TwV.takeSc, handed the target tg, is meant to leave of runJob's rounds (shown for a lawful
job with as many degrees as points, at the right number of challenges, in
Johnson/HonestTrace/LookSum.lean, takeSc_job). -/
def scJob (L : Led P) (μ : P → K) (J : Job K) (eps tg : K) (xs : List K) : Sc K :=
  match J.dY with
  | some dY =>
    ⟨eps, xs, _root_.Fo.valS (hide L (J.dg ++ [dY]) xs) μ +
      eps * (J.S0 (shownOf L μ J xs) + (tg - J.sum)), shownOf L μ J xs⟩
  | none => ⟨eps, xs, _root_.Fo.valS (hide L J.dg xs) μ + eps * (J.fin xs + (tg - J.sum)), []⟩

variable (D : Data P K) (μ : P → K) (C : Chal K)

/-- The key side's points. Level l + 1's point: the challenges of level l by coordinate, then its
line's draw as the new highest coordinate. -/
def keyPt : ℕ → List K
  | 0 => []
  | l + 1 => byVar (D.N.oK l) (C.keyX l) ++ [C.keyR l]

/-- The table side's points. Level 0's point: the join's draw. Level l + 1's: the challenges of
level l by coordinate, then its line's draw as the new highest coordinate. -/
def tabPt : ℕ → List K
  | 0 => C.join
  | l + 1 => byVar (D.N.oT l) (C.tabX l) ++ [C.tabR l]

/-- Shown value i of tie step s. -/
def tieShown (s i : ℕ) : K := (shownOf (D.N.ledTie s) μ (tieJob D s) [C.tieB s]).getD i 0

/-- The shown target of tie step s. -/
def tieTg (s : ℕ) : K := if s = 0 then 0 else tieShown D μ C (s - 1) (nxAt (s - 1))

/-- The shown target of key level l. -/
def keyTg : ℕ → K
  | 0 => tieShown D μ C 0 0
  | l + 1 =>
    (1 - C.keyR l) * (shownOf (D.N.ledK l) μ (keyJob D l (keyPt D C l)) (C.keyX l)).getD 0 0 +
      C.keyR l * (shownOf (D.N.ledK l) μ (keyJob D l (keyPt D C l)) (C.keyX l)).getD 1 0

/-- The shown root of plane j, for j ≤ n + 1; for j > n + 1 it repeats plane n + 1. -/
def gShown (j : ℕ) : K :=
  if j < D.N.n + 1 then tieShown D μ C j (TwV.ptAt j) else tieShown D μ C D.N.n (nxAt D.N.n)

/-- The shown target of table level l. -/
def tabTg : ℕ → K
  | 0 => ((List.range (2 ^ D.N.w)).map fun j => eqN C.join j * gShown D μ C j).sum
  | l + 1 =>
    (1 - C.tabR l) * (shownOf (D.N.ledT l) μ (tabJob D l (tabPt D C l)) (C.tabX l)).getD 0 0 +
      C.tabR l * (shownOf (D.N.ledT l) μ (tabJob D l (tabPt D C l)) (C.tabX l)).getD 1 0

/-- **The rounds of a lookup behind the shift's**, as plain data: scalars sent and elements
drawn, round by round, in the order in which TwV.traceOfFlat reads them. -/
def rsT : Rounds K :=
  [([], [D.al])] ++
    (List.range (D.N.n + 1)).flatMap (fun s =>
      runJob (D.N.ledTie s) μ (tieJob D s) (C.tieE s) [C.tieB s]) ++
    [([], C.join)] ++
    (List.range D.v).flatMap (fun l =>
      runJob (D.N.ledK l) μ (keyJob D l (keyPt D C l)) (C.keyE l) (C.keyX l) ++
        [([], [C.keyR l])]) ++
    (List.range D.N.d).flatMap (fun l =>
      runJob (D.N.ledT l) μ (tabJob D l (tabPt D C l)) (C.tabE l) (C.tabX l) ++
        [([], [C.tabR l])]) ++
    runJob D.N.ledE μ (leavesJob D (tabPt D C D.N.d)) C.clsE C.clsX ++
    [([], C.zero)] ++
    runJob D.N.ledB μ (bitsJob D C.zero) C.bitE C.bitX

/-- **The trace**: what TwV.traceOfFlat is meant to read off rsT. -/
def trT : Trace K where
  lam := D.al
  tie := (List.range (D.N.n + 1)).map fun s =>
    scJob (D.N.ledTie s) μ (tieJob D s) (C.tieE s) (tieTg D μ C s) [C.tieB s]
  join := C.join
  keys := (List.range D.v).map fun l =>
    (scJob (D.N.ledK l) μ (keyJob D l (keyPt D C l)) (C.keyE l) (keyTg D μ C l) (C.keyX l),
      C.keyR l)
  kT := keyTg D μ C D.v
  tabl := (List.range D.N.d).map fun l =>
    (scJob (D.N.ledT l) μ (tabJob D l (tabPt D C l)) (C.tabE l) (tabTg D μ C l) (C.tabX l),
      C.tabR l)
  cls := scJob D.N.ledE μ (leavesJob D (tabPt D C D.N.d)) C.clsE (tabTg D μ C D.N.d) C.clsX
  zero := C.zero
  bits := scJob D.N.ledB μ (bitsJob D C.zero) C.bitE 0 C.bitX

/-- The premises of the statements on rsT and trT. premT_of_premF
(Johnson/HonestTrace/LookClaims.lean) gets them from PremF. -/
structure PremT : Prop where
  /-- every plane counts -/
  planes : D.N.n + 2 = 2 ^ D.N.w
  /-- the order of key level l lists its l coordinates once each -/
  oK : ∀ l < D.v, (D.N.oK l).Perm (List.range l)
  /-- the order of table level l lists its w + l coordinates once each -/
  oT : ∀ l < D.N.d, (D.N.oT l).Perm (List.range (D.N.w + l))
  /-- the order of the leaves' sumcheck lists its w + d coordinates once each -/
  oE : D.N.oE.Perm (List.range (D.N.w + D.N.d))
  /-- the order of the bits' sumcheck lists its w + d coordinates once each -/
  oB : D.N.oB.Perm (List.range (D.N.w + D.N.d))
  /-- the relation on keys, table, padding and bits at al -/
  mid : D.Mid
  /-- μ reads D's bits at the planes' places -/
  bits : ∀ u < 2 ^ D.N.d, ∀ j < 2 ^ D.N.w, μ (D.N.bAt u j) = D.bits u j
  /-- the lists of challenges have the right lengths -/
  chal : C.Fits D.v D.N.d D.N.w

end

/-! ## 7 · At the numbers of a sub-proof's lookup -/

section
variable {K : Type} [Field K]
variable (h : Forest.Shape) (lm jLK : ℕ) (kv : ℕ → ℕ → K) (θ al : K) (ν : _root_.Fo.Pl → K)
  (C : Chal K)

/-- Data at a sub-proof's lookup: the bits are what ν reads at the planes' places. -/
def dataF : Data _root_.Fo.Pl K where
  N := _root_.Fo.numsF h lm jLK θ
  key := Ends.jointKey h kv θ
  bits := fun u j => ν ((_root_.Fo.numsF h lm jLK θ).bAt u j)
  al := al

/-- The rounds, the shift's first where there are several calls. -/
def rsF : Rounds K :=
  (if FoNums.several h then [([], [θ])] else []) ++ rsT (dataF h lm jLK kv θ al ν) ν C

/-- The premises of the statements on rsF. The first three are on public numbers; where a
sub-proof's layout returns (attention: where shapeHid returns) they are theorems (ok_of_layout, ok_A
with lmb_A, ok_H, in Johnson/HonestTrace/CountsLayers.lean, CountsAttention.lean, CountsHead.lean).
-/
structure PremF : Prop where
  /-- the test on the lookup's public numbers says true -/
  ok : FoNums.ok h = true
  /-- the planes' matrix has at least 2^5 rows -/
  lm5 : 5 ≤ lm
  /-- and at most 2^(kT + 5) -/
  lmT : lm ≤ h.kT + 5
  /-- where there is one call no θ is drawn, and Fo.thetaOf reads 0 for it; where there are several
  calls, as at the two example sets' shapes, this asks nothing -/
  one : FoNums.several h = false → θ = 0
  /-- ν reads 0 at the place that stands for "no cell" -/
  zero : ν .zero = 0
  /-- the relation on the joint key vector, the joint table, the padding and the bits that ν reads
  at the planes' places, at θ and al (law_bits, Johnson/HonestTrace/CountsLaw.lean, concludes it
  under the four premises of midP_joint, every key in its call's table among them, for bits that are
  the cells of plane at hitsOf of these keys) -/
  mid : MidP h.v h.d 5 32 (Ends.jointKey h kv θ) (Ends.jointTab h θ) (FoNums.pads h)
    (fun u j => ν ((_root_.Fo.numsF h lm jLK θ).bAt u j)) al
  /-- the lists of challenges have the right lengths -/
  chal : C.Fits h.v h.d 5

end

end OnBytes.HonestTrace.Look
