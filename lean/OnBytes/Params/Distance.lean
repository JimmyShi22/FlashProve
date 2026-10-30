-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Distance.lean: from a code and a distance to the quantities of which round errors
are made, and to the number of positions.

 - the list size: how many code words can lie within the distance of one word;
 - the count: how many challenges z can make u + z v close to the code where u and v are not
   jointly close. The error of mutual correlated agreement is the count over the size of the
   extension field;
 - the positions: the least t with agree ^ t, and what else the round's error holds, at most
   2 ^ -bits.
The file renders blocks/numbers/codes.h, formula for formula and in the same order of operations,
for plain Reed-Solomon codes. That header names the sources of the counts.

On what the count rests (`CountSource`): within a third of the code's distance, on a lemma. Everywhere
else: on Theorem 4.6 of IACR ePrint 2025/2055, taken with M = 1. That theorem is an assumption here: the report
states it, and no proof of it has been verified for this program.

The rate in the formulas is k / n for the code of polynomials of degree at most k. A code of
dimension d enters with k = d - 1.

Main definitions: `CodeSize`, `Word`, `Proximity`, `johnson`, `atDistance`, `mcaError`,
`positions`, `largestM`, `sampleError`.
What is not claimed: that these formulas bound what their names say. No theorem is stated here.
-/
import OnBytes.Params.Setting

namespace OnBytes.Params

/-- A code as the sizing sees it. -/
structure CodeSize where
  /-- the length is 2 ^ logN -/
  logN : Nat := 0
  /-- the entries of a message -/
  ell : Nat := 0
  /-- the random entries of a row's tail -/
  r : Nat := 0
  /-- symbols, messages and random entries are in the extension field -/
  overE : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace CodeSize

/-- The length. -/
def n (c : CodeSize) : Nat := 2 ^ c.logN

/-- The dimension of the code that holds all encodings. -/
def dim (c : CodeSize) : Nat := c.ell + c.r

/-- The k of the formulas' rate: the dimension less 1. The C++ computes it in 64 bits, where 0 - 1
is 2 ^ 64 - 1. That k is at least every length below 2 ^ 64, so `johnson` and
`atDistance`, which test n ≤ k, give a bad result. `rhoOf` and `johnsonCount` do
not test it. -/
def k (c : CodeSize) : Nat := if c.dim == 0 then 2 ^ 64 - 1 else c.dim - 1

end CodeSize

/-- The random entries that the sizing gives a row which is opened at t positions. -/
def tailFor (t : Nat) : Nat := t

/-- A code as the formulas read it: a length 2 ^ logN and the k of the rate. -/
structure Word where
  logN : Nat
  k : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The length. -/
def Word.n (c : Word) : Nat := 2 ^ c.logN

/-- The `Word` of a code at its own length. -/
def wordOf (c : CodeSize) : Word := ⟨c.logN, c.k⟩

/-- A code repeated to the length 2 ^ logN: every word written 2 ^ (logN - c.logN) times. It has the
same rate and relative distance. It is the code that applies to a prover who commits to a short
row's symbols by copies in the leaves of a longer tree, because no test forces the copies to agree.
It is meant for distances, list sizes and counts only. The product is taken modulo 2 ^ 64, as the
C++ shift does. A logN that is not above the code's own gives the code itself. -/
def repeated (c : CodeSize) (logN : Nat) : Word :=
  if logN ≤ c.logN then wordOf c else ⟨logN, c.k * 2 ^ (logN - c.logN) % 2 ^ 64⟩

/-- The rate. -/
def rhoOf (c : Word) : Bound := Bound.ratio c.k c.n

/-- A code at a distance. One that nobody has filled is bad, and what is planned with it is
refused. -/
structure Proximity where
  /-- 1 - delta -/
  agree : Bound := Bound.failed
  delta : Bound := Bound.failed
  /-- where the source is `.johnson`: the slack 1 - sqrt rho - delta -/
  eta : Bound := {}
  /-- where the source is `.johnson`: the integer m of the assumed theorem (`johnsonCount`), in the
  reading that the setting names (`Setting.printed`) -/
  m : Nat := 0
  /-- the distance was made from m, so sqrt rho / eta is exactly m (or 2 m) -/
  fromM : Bool := false
  source : CountSource := .johnson
  count : Bound := Bound.failed
  /-- an integer bound on the list size -/
  list : Nat := 1
  deriving DecidableEq, Repr, Inhabited

/-- True if `agree`, `delta` or `count` is bad. `eta` is not read. -/
def Proximity.bad (x : Proximity) : Bool := x.agree.bad || x.delta.bad || x.count.bad

/-- The counting form of the Johnson bound: a word has at most (a - lambda) / (a ^ 2 - lambda) code
words that agree with it on a fraction a of the positions, if a ^ 2 > lambda. Here lambda is 1 minus
the code's relative distance. The bound uses the minimum distance only, so it also holds for
interleaved codes, and for a main and a mask code read at the same positions with the smaller of
their two distances. Returns the bound, rounded down because a list size is an integer, and whether
the formula was asked outside its range; the list size is then 1. -/
def johnsonList (agree lambda : Bound) : Nat × Bool :=
  let l := (agree - lambda) / (agree * agree - lambda)
  (if l.bad then 1 else l.hi.floor, l.bad)

/-- The count up to the Johnson radius, by Theorem 4.6 of IACR ePrint 2025/2055 with M = 1:
(2 (m + 1/2) ^ 5 + 3 (m + 1/2) delta rho) / (3 rho ^ (3/2)) n + (m + 1/2) / sqrt rho.
The theorem is assumed: no proof of it has been verified for this program. -/
def johnsonCount (c : Word) (rho delta : Bound) (m : Nat) : Bound :=
  let M := Bound.ratio (2 * m + 1) 2
  let root := Bound.sqrt rho
  (Bound.ofWord 2 * Bound.pow M 5 + Bound.ofWord 3 * M * delta * rho) /
    (Bound.ofWord 3 * rho * root) * Bound.ofNat c.n + M / root

/-- The distance that belongs to m: 1 - delta = sqrt rho (1 + 1 / m) as the assumed theorem prints
m, and sqrt rho (1 + 1 / (2 m)) in the other reading (`Setting.printed`). The count is bad if m < 3,
if n ≤ k, or if a formula was asked outside its range. -/
def johnson (c : Word) (m : Nat) (printed : Bool) : Proximity :=
  let rho := rhoOf c
  let root := Bound.sqrt rho
  let eta := root / Bound.ofNat (if printed then m else 2 * m)
  let agree := root + eta
  let delta := Bound.ofWord 1 - agree
  let l := johnsonList agree rho
  let bad := decide (m < 3) || decide (c.n ≤ c.k) || l.2
  { agree := agree, delta := delta, eta := eta, m := m, fromM := true, source := .johnson,
    count := if bad then Bound.failed else johnsonCount c rho delta m,
    list := l.1 }

/-- The code at a given distance, by the best source that applies there. `.third` if
3 floor (delta n) is below the code's distance. Else `.johnson`, with m = max (ceil (sqrt rho / eta)) 3, or with
2 eta for eta in the other reading. The list size is 1 within unique decoding. A distance outside
every range comes back bad. -/
def atDistance (s : Setting) (c : Word) (agree : Bound) : Proximity :=
  if agree.bad || decide (c.n ≤ c.k) then {}
  else
    let n := Bound.ofNat c.n
    let d := Bound.ofNat (c.n - c.k)
    let rho := rhoOf c
    let delta := Bound.ofWord 1 - agree
    let x : Proximity := { agree := agree, delta := delta }
    if delta.bad then x
    else
      let errors := (delta * n).hi.floor
      if 3 * errors < c.n - c.k then
        { x with source := .third, count := Bound.ofNat (errors + 1) }
      else
        let root := Bound.sqrt rho
        let eta := agree - root
        let q := root / (if s.printed then eta else Bound.ofWord 2 * eta)
        let x : Proximity := { x with source := .johnson, eta := eta }
        if q.bad || decide (2 ^ 64 ≤ q.hi.ceil) then x
        else
          let m := max q.hi.ceil 3
          let l : Nat × Bool :=
            if !surelyLt (Bound.ofWord 2 * delta * n) d then johnsonList agree rho else (1, false)
          { x with
            m := m, list := l.1,
            count := if l.2 then Bound.failed else johnsonCount c rho delta m }

/-- The error of mutual correlated agreement for a line through two words of the code interleaved
`rows` times. -/
def mcaError (s : Setting) (x : Proximity) (rows : Nat) : Bound :=
  let a := if s.rowsFactor && x.source != .third then x.count * Bound.ofNat rows else x.count
  a / Bound.ofNat s.cardE

/-- Doubles hi until ok holds. Nothing if it does not hold up to 2 ^ 32. -/
def firstOk (ok : Nat → Bool) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, hi =>
    if ok hi then some hi
    else if 2 ^ 32 < 2 * hi then none
    else firstOk ok fuel (2 * hi)

/-- The least number above lo at which ok holds, given that ok holds at hi and, once it holds, at
every larger number. -/
def leastOk (ok : Nat → Bool) : Nat → Nat → Nat → Nat
  | 0, _, hi => hi
  | fuel + 1, lo, hi =>
    if 1 < hi - lo then
      let mid := lo + (hi - lo) / 2
      if ok mid then leastOk ok fuel lo mid else leastOk ok fuel mid hi
    else hi

/-- The least t with factor (agree ^ t + extra) ≤ 2 ^ -bits; 0 if there is none up to 2 ^ 32.
`extra` is what else the round's error holds, `factor` the number of instances that share the
round. The comparison is made at the upper ends of the bounds, and the t that is returned is one at
which it held. Rounding up can make t larger than the exact numbers' least t. The search is a
bisection: it finds the least t if the comparison, once it holds, holds at every larger t. Also 0
for a factor of 0 or a bad bound. -/
def positions (agree : Bound) (bits : Nat) (extra : Bound := Bound.ofWord 0) (factor : Nat := 1) :
    Nat :=
  if factor == 0 then 0
  else
    let goal := (Binary.twoTo (-(bits : Int))).div (.ofNat factor) .down
    if agree.bad || extra.bad || !(agree.hi.lt (.ofNat 1)) || !(extra.hi.lt goal) then 0
    else
      let ok := fun t => ((agree.hi.pow t .up).add extra.hi .up).le goal
      match firstOk ok 40 1 with
      | none => 0
      | some hi => leastOk ok 40 (hi / 2) hi

/-- The first number from lo on, below 67, at which good holds; 67 if there is none. -/
def firstGood (good : Nat → Bool) : Nat → Nat → Nat
  | 0, lo => lo
  | fuel + 1, lo => if lo < 67 && !good lo then firstGood good fuel (lo + 1) else lo

/-- Doubles hi while it is below the limit and good holds there. Returns the last good number and
the first number that was not taken. -/
def growGood (good : Nat → Bool) (limit : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, lo, hi => (lo, hi)
  | fuel + 1, lo, hi =>
    if hi < limit && good hi then growGood good limit fuel hi (2 * hi) else (lo, hi)

/-- A good number from a good lo to below hi, by bisection. It is the last good number below hi if
good holds on one stretch of integers from lo on and not at hi. -/
def lastGood (good : Nat → Bool) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if 1 < hi - lo then
      let mid := lo + (hi - lo) / 2
      if good mid then lastGood good fuel mid hi else lastGood good fuel lo mid
    else lo

/-- An m from 3 to the limit at which good holds: the largest, if good holds on one stretch of
integers that begins below 67. 0 if good holds at no m below 67. (With m read as printed, at a rate
above 9/16 the smallest m give a distance below 0, so the stretch can begin above 3.) Whatever good
is like, the m that is returned is one at which good was evaluated and was true. -/
def largestM (good : Nat → Bool) (limit : Nat := 2 ^ 40) : Nat :=
  let lo := firstGood good 64 3
  if lo == 67 then 0
  else
    let x := growGood good limit 64 lo (lo + 1)
    if limit ≤ x.2 then
      if good limit then limit else lastGood good 64 x.1 limit
    else lastGood good 64 x.1 x.2

/-- The error of a combination of rows by the powers of one element. -/
def powersError (s : Setting) (rows : Nat) : Bound := Bound.ratio (rows - 1) s.cardE

/-- degree / |E|: a bound on the chance that a polynomial of at most this total degree, not zero,
vanishes at a random element, or point, of the extension field E. -/
def fieldError (s : Setting) (degree : Nat) : Bound := Bound.ratio degree s.cardE

/-- degree / (|E| - 1): the bound of `fieldError` for a random element of E other than 0. -/
def fieldErrorNonzero (s : Setting) (degree : Nat) : Bound := Bound.ratio degree (s.cardE - 1)

/-- A bound on the chance that two members of a list of `list` code words have the same
out-of-domain sample. The seed is a point z of a cube with `cubeBits` variables and a pad factor
beta other than 0. The protocol's argument: two messages that differ in the pad agree for at most
one beta at each z; two that differ elsewhere agree only for z on a hypersurface of degree cubeBits.
So a pair and one answer have the error max (cubeBits / |E|) (1 / (|E| - 1)). Further answers have
independent seeds and pads of their own, so the pair's error is that to the power `answers`. The
number of pairs is at most list ^ 2 / 2. -/
def sampleError (s : Setting) (list cubeBits answers : Nat) : Bound :=
  Bound.ofNat (list * list) / Bound.ofWord 2 *
    Bound.pow (if 2 ≤ cubeBits then fieldError s cubeBits else fieldErrorNonzero s 1) answers

end OnBytes.Params
