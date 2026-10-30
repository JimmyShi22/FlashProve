-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Real.lean: the arithmetic in which sizes are derived from the parameter file.

A number of positions is a ceiling, the slack of a code is the last integer for which an error
stays under a target, and "this round holds" is a comparison. A rounding error of floating-point
arithmetic can move each of them by one, and prover and verifier must derive the same numbers on
every machine. So the C++ programs derive them with integers only (blocks/numbers/real.h), and this
file renders that arithmetic operation for operation; the square root value for value: the C++
finds the place of the last kept digit first.

 - `Binary` is a number m * 2 ^ e with a natural number m. An operation that cannot be exact
   takes a direction, down or up, and its result lies on that side of the true value. A result
   that would be longer is cut to 192 bits (193 where rounding up carries).
 - `Bound` is a pair lo, hi of such numbers around a true value that is not negative. It is marked
   bad if a formula was used outside its range. Every result inherits the mark.
A decision is an exact comparison at the safe end of a bound. Where 192 bits cannot tell on which
side of a threshold the true value lies, the decision is meant to fall on the safe side: one more
position, a smaller slack, "does not hold".

The C++ type of integers of any size is `Nat` here.

Main definitions: `Dir`, `Binary`, `Bound`, with their operations; `surelyLe`, `surelyLt`.
What is not claimed: no theorem is stated here. In particular it is not shown that lo and hi enclose
the true value. Outside their stated ranges `Binary.sub` (a < b) and `Binary.div` (b = 0) return a
number, by the rules of `Nat`, where the C++ ends the process. `Bound.sub` and `Bound.div` test the
range first and return `failed` outside it, so they do not call the two functions there (a bound
whose ends have crossed is marked bad by `Bound.ends`). Two functions call `Binary.div` themselves:
`positions` (OnBytes/Params/Distance.lean), after a test that the divisor is not 0, and `goalOf`
(OnBytes/Params/Group.lean), with `Setting.instances`, which `settingOf` leaves at 1.
-/

namespace OnBytes.Params

/-- The number of binary digits of n; 0 for 0. -/
def bitsOf (n : Nat) : Nat := if n == 0 then 0 else Nat.log2 n + 1

/-- True if one of the lowest k binary digits of n is 1. -/
def anyBelow (n k : Nat) : Bool := n % 2 ^ k != 0

/-- One step after another of Newton's iteration for a square root, from above. -/
def isqrtFrom (a : Nat) : Nat → Nat → Nat
  | 0, x => x
  | fuel + 1, x =>
    let y := (x + a / x) / 2
    if x ≤ y then x else isqrtFrom a fuel y

/-- The square root of a, rounded down. The iteration falls until it has reached the root. The C++
loop has no bound. Here the fuel bounds it: 8 more steps than a has digits. That the fuel is never
used up is not proved here. -/
def isqrt (a : Nat) : Nat :=
  if a == 0 then 0 else isqrtFrom a (bitsOf a + 8) (2 ^ ((bitsOf a + 1) / 2))

/-- The side of the true value on which a result lies. -/
inductive Dir where
  | down
  | up
  deriving DecidableEq, Repr, Inhabited

/-- The digits to which a result is cut. -/
def realBits : Nat := 192

/-- The number m * 2 ^ e. -/
structure Binary where
  m : Nat := 0
  e : Int := 0
  deriving DecidableEq, Repr, Inhabited

namespace Binary

/-- A natural number, exactly. -/
def ofNat (x : Nat) : Binary := ⟨x, 0⟩

/-- The number 2 ^ n. -/
def twoTo (n : Int) : Binary := ⟨1, n⟩

/-- True for the number 0. -/
def isZero (a : Binary) : Bool := a.m == 0

/-- The place of the top digit: 2 ^ (top - 1) ≤ the value < 2 ^ top, for a value other than 0. -/
def top (a : Binary) : Int := (bitsOf a.m : Int) + a.e

/-- Cuts a number to 192 digits, toward the side d. Rounding up can carry: then m = 2 ^ 192, which
has 193 digits. -/
def cut (a : Binary) (d : Dir) : Binary :=
  let b := bitsOf a.m
  if b ≤ realBits then a
  else
    let s := b - realBits
    let m := a.m / 2 ^ s
    ⟨if d == .up && anyBelow a.m s then m + 1 else m, a.e + s⟩

/-- The order of two numbers. -/
def cmp (a b : Binary) : Ordering :=
  if a.isZero || b.isZero then
    (if a.isZero then (if b.isZero then .eq else .lt) else .gt)
  else if a.top != b.top then (if a.top < b.top then .lt else .gt)
  else if b.e ≤ a.e then compare (a.m * 2 ^ (a.e - b.e).toNat) b.m
  else compare a.m (b.m * 2 ^ (b.e - a.e).toNat)

/-- a ≤ b. -/
def le (a b : Binary) : Bool := cmp a b != .gt

/-- a < b. -/
def lt (a b : Binary) : Bool := cmp a b == .lt

/-- The sum. -/
def add (a b : Binary) (d : Dir) : Binary :=
  if a.isZero then b
  else if b.isZero then a
  else
    let e := min a.e b.e
    cut ⟨a.m * 2 ^ (a.e - e).toNat + b.m * 2 ^ (b.e - e).toNat, e⟩ d

/-- The difference a - b, for a ≥ b. For a < b: 0, where the C++ ends the process. -/
def sub (a b : Binary) (d : Dir) : Binary :=
  if b.isZero then a
  else
    let e := min a.e b.e
    cut ⟨a.m * 2 ^ (a.e - e).toNat - b.m * 2 ^ (b.e - e).toNat, e⟩ d

/-- The product. -/
def mul (a b : Binary) (d : Dir) : Binary := cut ⟨a.m * b.m, a.e + b.e⟩ d

/-- The quotient a / b, for b other than 0. For b = 0 the C++ ends the process; the number that is
returned here means nothing. -/
def div (a b : Binary) (d : Dir) : Binary :=
  if a.isZero then a
  else
    let s := realBits + 2 + bitsOf b.m
    let x := a.m * 2 ^ s
    let q := x / b.m
    cut ⟨if d == .up && x % b.m != 0 then q + 1 else q, a.e - s - b.e⟩ d

/-- The square root, rounded to 192 digits toward the side d: the root of the number shifted up by
some 388 digits, rounded toward d, and then cut toward d. -/
def sqrt (a : Binary) (d : Dir) : Binary :=
  if a.isZero then a
  else
    let s0 : Nat := 2 * realBits + 4
    let s : Nat := if (a.e - s0) % 2 != 0 then s0 + 1 else s0
    let x := a.m * 2 ^ s
    let r := isqrt x
    cut ⟨if d == .up && r * r != x then r + 1 else r, (a.e - s) / 2⟩ d

/-- The steps of a power by squaring. `r` is the product so far. -/
def powFrom (d : Dir) : Nat → Binary → Binary → Nat → Binary
  | 0, r, _, _ => r
  | fuel + 1, r, a, n =>
    if n == 0 then r
    else
      let r' := if n % 2 == 1 then mul r a d else r
      let a' := if 1 < n then mul a a d else a
      powFrom d fuel r' a' (n / 2)

/-- The power a ^ n. -/
def pow (a : Binary) (n : Nat) (d : Dir) : Binary := powFrom d (bitsOf n) (ofNat 1) a n

/-- The value rounded down to an integer. -/
def floor (a : Binary) : Nat :=
  if 0 ≤ a.e then a.m * 2 ^ a.e.toNat else a.m / 2 ^ (-a.e).toNat

/-- The value rounded up to an integer. -/
def ceil (a : Binary) : Nat :=
  if 0 ≤ a.e then a.m * 2 ^ a.e.toNat
  else
    let k := (-a.e).toNat
    if anyBelow a.m k then a.m / 2 ^ k + 1 else a.m / 2 ^ k

end Binary

/-- Meant: lo ≤ the true value ≤ hi. `bad`: a formula was used outside its range (a difference that
must be positive is not certainly so, a divisor may be 0). Every result inherits the mark. Whoever
turns a `Bound` into a decision is to treat a bad one as a failure, as `error`, `surelyLe` and
`surelyLt` do. -/
structure Bound where
  lo : Binary := {}
  hi : Binary := {}
  bad : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace Bound

/-- A number that needs no cut, exactly. -/
def exact (x : Binary) : Bound := ⟨x, x, false⟩

/-- A natural number below 2 ^ 64, exactly. -/
def ofWord (x : Nat) : Bound := exact (.ofNat x)

/-- A natural number of any size. -/
def ofNat (x : Nat) : Bound := ⟨(Binary.ofNat x).cut .down, (Binary.ofNat x).cut .up, false⟩

/-- Two ends. Ends that have crossed are no interval. -/
def ends (l h : Binary) : Bound := ⟨l, h, h.lt l⟩

/-- The result of a formula that was used outside its range. -/
def failed : Bound := ⟨.ofNat 1, .ofNat 1, true⟩

/-- The mark of a and b, handed on to r. -/
def inherit (r a b : Bound) : Bound := { r with bad := r.bad || a.bad || b.bad }

/-- The sum. -/
def add (a b : Bound) : Bound :=
  (ends (a.lo.add b.lo .down) (a.hi.add b.hi .up)).inherit a b

/-- The difference a - b, where the formula needs it to be positive. -/
def sub (a b : Bound) : Bound :=
  if a.bad || b.bad || !(b.hi.lt a.lo) then failed
  else ends (a.lo.sub b.hi .down) (a.hi.sub b.lo .up)

/-- The product. -/
def mul (a b : Bound) : Bound :=
  (ends (a.lo.mul b.lo .down) (a.hi.mul b.hi .up)).inherit a b

/-- The quotient. -/
def div (a b : Bound) : Bound :=
  if a.bad || b.bad || b.lo.isZero then failed
  else ends (a.lo.div b.hi .down) (a.hi.div b.lo .up)

/-- `a + b` is the sum. -/
instance : Add Bound := ⟨add⟩
/-- `a - b` is the difference where the formula needs it to be positive. -/
instance : Sub Bound := ⟨sub⟩
/-- `a * b` is the product. -/
instance : Mul Bound := ⟨mul⟩
/-- `a / b` is the quotient. -/
instance : Div Bound := ⟨div⟩

/-- The quotient of two natural numbers. -/
def ratio (a b : Nat) : Bound := (ofNat a).div (ofNat b)

/-- The square root. -/
def sqrt (a : Bound) : Bound := (ends (a.lo.sqrt .down) (a.hi.sqrt .up)).inherit a a

/-- The power a ^ n. -/
def pow (a : Bound) (n : Nat) : Bound := (ends (a.lo.pow n .down) (a.hi.pow n .up)).inherit a a

/-- The value as the chance of an error, from above. A bad one counts as 1. -/
def error (a : Bound) : Binary := if a.bad then .ofNat 1 else a.hi

end Bound

/-- Certainly a ≤ b. -/
def surelyLe (a b : Bound) : Bool := !a.bad && !b.bad && a.hi.le b.lo

/-- Certainly a < b. -/
def surelyLt (a b : Bound) : Bool := !a.bad && !b.bad && a.hi.lt b.lo

end OnBytes.Params
