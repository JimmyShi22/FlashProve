-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Ledger.lean: the ledger of a norm: its counts, and its lines when a value of the
residual stream has five limbs (signed digits to the base 256).

It follows the C++ verifier's header verifier/src/vf_norm_digit_rows.h, routine by routine. A type
or routine has the name of its C++ counterpart. The constants ledNE, exc, ledG and bigH are LEDNE,
EXC, LEDG and BIGH in the C++. The C++ global residualStreamLimbs is an argument here, XL. ledDig is
the local function dig of the C++ routine row5. The C++ header calls the ledger a digit
row and a line an equation. This ledger is not the ledger of a message's mask entries
(OnBytes/Iop/Ground.lean).

A norm needs sigma = isqrt(V + eps), where V is the sum of the squares of a token's stream values,
and R = floor((2^M + floor(sigma / 2)) / sigma). Here isqrt is the square root of a whole number,
rounded down, and eps and M are public numbers of the norm. The prover writes sigma and R, with
everything that shows them correct, as byte digits into one row for each token: the ledger. A lookup
tests the range of every digit. The lines in this file are linear in the digits and in a few hidden
products. A line is an identity in the field, so it says something about whole numbers only while
the sum of its terms stays below the field's prime in absolute value. With five limbs V can reach
2^78 and sigma 2^39. So V exists only as its digits, and sigma is split in two, sigma = a + 2^24 b
with a < 2^24 and b < 2^15. Then every product stays below 2^48. How large the terms of a line can
get, and on which conditions, is stated in the docstrings of ledCarry5 and ledLines5.

The functions work on any type T of values that can be added, subtracted and multiplied by a field
element (LedK). The sub-proofs use them on affine forms in hidden values. A test can use them on
field elements made from whole numbers.

Main definitions: the counts ledNS to ledLines, ledMu, ledG, LedK, Row5, row5,
ledCarry5, ledLines5, ledProducts5.

What this file does not do: it reads no message and tests nothing. The sub-proofs of the layers and
of the head claim that the lines vanish. Of the ledger for four limbs it holds the counts and the
multipliers alone. The row and the lines for four limbs are in the sub-proofs' files: rowAt in
LayerForms.lean and HeadForms.lean, claimsLedger4 in Layer.lean, claimLedger4 in Head.lean. The
conditions on public numbers under which a line speaks of whole numbers are tested in
OnBytes/Model/LayerLayout.lean and OnBytes/Model/HeadLayout.lean. No theorem is stated here.
-/
import OnBytes.Model.Hide

namespace OnBytes.Model

/-! ## Counts

XL is the number of limbs of a stream value: 4, or 5 if the parameter file has the line "xl 5". No
other value occurs, and the functions here treat every value but 5 as 4, except ledNS.
An instance is one norm of one layer, or the final norm. -/

/-- The number of convolution sums W_s of an instance. A stream value is the sum of 256^i times its
limb i. W_s is the sum, over a token's stream values, of all products of limb i and limb j with
i + j = s, so the sum of the squares is the sum of 256^s W_s. This W is not the committed matrix of
OnBytes/Model/Weights.lean. -/
def ledNS (XL : Nat) : Nat := 2 * XL - 1

/-- The number of digits of a row. -/
def ledNR (XL : Nat) : Nat := if XL == 5 then 99 else 74

/-- The number of hidden products of an instance. -/
def ledNP (XL : Nat) : Nat := if XL == 5 then 7 else 3

/-- The number of values that are opened at the end of the products' sumcheck. -/
def ledNO (XL : Nat) : Nat := if XL == 5 then 4 else 3

/-- The number of lines of an instance after the carries' lines. -/
def ledLines (XL : Nat) : Nat := if XL == 5 then 8 else 5

/-- Four limbs: the multiplier of digit idx in the lookup that tests the row's ranges. The key is
the multiplier times the digit, and a key is a byte. So the digit is below 256 / multiplier, given
the bound on a cell that the smallness test is meant to give, which keeps the key below the field's
prime. -/
def ledMu4 (idx : Nat) : Nat :=
  if idx == 7 then 32 else if idx == 44 then 2 else if idx == 45 then 128
  else if idx == 48 then 4 else 1

/-- Five limbs: the multiplier of digit idx. -/
def ledMu5 (idx : Nat) : Nat :=
  if idx == 9 then 4 else if idx == 58 then 2 else if idx == 59 then 128
  else if idx == 63 then 2 else if idx == 76 then 2 else if idx == 79 then 32 else 1

/-- The multiplier of digit idx. -/
def ledMu (XL idx : Nat) : Nat := if XL == 5 then ledMu5 idx else ledMu4 idx

/-- The head's row has this many more digits, after the final norm's. They spell six numbers of a
position whose token the request asks to be checked; the prover commits to them and does not show
them. Each number has its low digit first, and each digit is tested as a whole byte, so each number
is at least 0. The six numbers:
  c   the position's cost, if that is at most the policy's clip C;
  b   above 0 if the cost is above C;
  u   slack: over all these positions, c + C b + u sums to a public bound;
  k   C - c, which keeps c at most C;
  z   slack: over all these positions, b + z sums to another public bound;
  zs  2^F minus the sum of the position's values of the table of exponentials, where 2^F is the
      public scale of that table. -/
def ledNE : Nat := 21

/-- The number of cells of a value of the table of exponentials. zs has as many digits. -/
def exc : Nat := 3

/-- For each of the head's six numbers c, b, u, k, z, zs (see ledNE): its first digit, counted from
the end of the norm's digits, and its number of digits. -/
def ledG : List (Nat × Nat) := [(0, 5), (5, 1), (6, 5), (11, 5), (16, 2), (18, exc)]

/-- The weight of b next to c: where the head compares logits, a position counts with c + b bigH. -/
def bigH : Nat := 2 ^ 37

/-- The number of digits of the head's row. -/
def ledNRH (XL : Nat) : Nat := ledNR XL + ledNE

/-! ## Values -/

/-- A type of values on which the ledger's lines can be formed. -/
class LedK (T : Type) where
  /-- a constant as a value -/
  c : E → T
  /-- the sum -/
  add : T → T → T
  /-- the difference -/
  sub : T → T → T
  /-- the product with a field element -/
  mul : T → E → T

/-- Field elements are values. Only tests use this instance. -/
instance : LedK E where
  c := id
  add := addE
  sub := subE
  mul := mulE

/-- Affine forms in hidden values are values. -/
instance : LedK Aff where
  c := Aff.ofConst
  add := fun a b => a + b
  sub := fun a b => a - b
  mul := Aff.scale

/-! ## The row of five limbs -/

/-- The row of five limbs: its 99 digits (a cell holds its digit - 128) and the numbers composed
from them, low byte first.
  0 ..  9  v_0 .. v_9, the bytes of V; v_9 < 64.
 10 .. 57  c_1 .. c_8: the carry into byte s, plus 2^47, six bytes each.
 58 .. 63  sigma: g0 < 128, s0 < 2, sg_1 .. sg_4 (sg_4 < 128).
 64 .. 68  l1.          69 .. 73  h1.
 74 .. 76  Blo (its top byte < 128).            77, 78    Bhi.
 79        kappa + 4, below 8.
 80 .. 82  Rlo.   83 .. 85  Rhi.   86 .. 88  q1.
 89 .. 93  rr.          94 .. 98  rq. -/
structure Row5 (T : Type) where
  /-- the 99 digits -/
  Dg : Array T
  /-- the ten carries c_0 to c_9, without the 2^47; c_0 = 0 and c_9 = v_9 -/
  c : Array T
  /-- the low 48 bits of V: v_0 .. v_5 -/
  Vlo : T
  /-- the high bits of V: v_6 .. v_9 -/
  Vhi : T
  /-- the low 24 bits of sigma: 2 g0 + s0 + 2^8 sg_1 + 2^16 sg_2 -/
  a : T
  /-- the high bits of sigma: sg_3 + 2^8 sg_4 -/
  b : T
  /-- sigma = a + 2^24 b -/
  sig : T
  /-- the lowest bit of sigma -/
  s0 : T
  /-- V + eps - sigma^2 -/
  l1 : T
  /-- 2 sigma - l1 -/
  h1 : T
  /-- (a b) mod 2^23 -/
  Blo : T
  /-- (a b) / 2^23 -/
  Bhi : T
  /-- kappa itself: the carry from the low 48 bits of the square root's line into the high ones -/
  kap : T
  /-- R mod 2^24 -/
  Rlo : T
  /-- R / 2^24 -/
  Rhi : T
  /-- R = Rlo + 2^24 Rhi -/
  R : T
  /-- Rlo b + Rhi a -/
  q1 : T
  /-- 2^M + floor(sigma / 2) - R sigma -/
  rr : T
  /-- sigma - 1 - rr -/
  rq : T

section
variable {T : Type} [LedK T]

/-- The number that n digits spell from digit number first on, low digit first. A digit beyond the
end of Dg counts as 0; row5 asks for none. -/
def ledDig (Dg : Array T) (first n : Nat) : T :=
  (List.range n).foldl
    (fun s j => LedK.add s (LedK.mul (Dg.getD (first + j) (LedK.c zeroE)) (ofNat (256 ^ j))))
    (LedK.c zeroE)

/-- The row, from its cells. cell j is the row's cell j as a value, for j from 0 to 98. -/
def row5 (cell : Nat → T) : Row5 T :=
  let K : E → T := LedK.c
  let add : T → T → T := LedK.add
  let sub : T → T → T := LedK.sub
  let mul : T → E → T := LedK.mul
  let Dg : Array T := Array.ofFn (n := 99) fun j => add (cell j.val) (K (ofNat 128))
  let D := fun j => Dg.getD j (K zeroE)
  let dig := ledDig Dg
  let a := add (add (add (mul (D 58) (ofNat 2)) (D 59)) (mul (D 60) (ofNat 256)))
    (mul (D 61) (ofNat 65536))
  let b := add (D 62) (mul (D 63) (ofNat 256))
  let Rlo := dig 80 3
  let Rhi := dig 83 3
  { Dg := Dg
    c := Array.ofFn (n := 10) fun s =>
      if s.val == 0 then K zeroE
      else if s.val == 9 then D 9
      else sub (dig (10 + 6 * (s.val - 1)) 6) (K (ofNat (2 ^ 47)))
    Vlo := dig 0 6
    Vhi := dig 6 4
    a := a
    b := b
    sig := add a (mul b (ofNat (2 ^ 24)))
    s0 := D 59
    l1 := dig 64 5
    h1 := dig 69 5
    Blo := dig 74 3
    Bhi := dig 77 2
    kap := sub (D 79) (K (ofNat 4))
    Rlo := Rlo
    Rhi := Rhi
    R := add Rlo (mul Rhi (ofNat (2 ^ 24)))
    q1 := dig 86 3
    rr := dig 89 5
    rq := dig 94 5 }

/-- The carries' line s, for s from 0 to 8: W_s + c_s - v_s - 256 c_(s+1), which must vanish. The
nine lines together say that V is the sum of 256^s W_s, the sum of the squares.
Sizes. The largest term is 256 c_(s+1), at most 2^55 in size by the digits' ranges. Given the bound
on a cell that the smallness test is meant to give, the condition on public numbers that the C++
verifier names "no-wrap-ledger" keeps every W_s below 2^53 in size.
For s above 8 there is no such line, and the result is the constant 1, which does not vanish. -/
def ledCarry5 (r : Row5 T) (s : Nat) (Ws : T) : T :=
  let z : T := LedK.c zeroE
  if 8 < s then LedK.c oneE
  else
    LedK.sub (LedK.sub (LedK.add Ws (r.c.getD s z)) (r.Dg.getD s z))
      (LedK.mul (r.c.getD (s + 1) z) (ofNat 256))

/-- The eight lines of an instance, each of which must vanish, in the order in which they are
claimed. P holds the seven hidden products P0 = a^2, P1 = a b, P2 = b^2, P3 = Rlo a, P4 = Rlo b,
P5 = Rhi a, P6 = Rhi b. two is 2^(M + 1).
  E0  P1 = Blo + 2^23 Bhi
  E1  Vlo + eps - P0 - 2^25 Blo - l1 + 2^48 kappa = 0
  E2  Vhi - Bhi - P2 - kappa = 0
      Since sigma^2 = a^2 + 2^25 a b + 2^48 b^2, E1 + 2^48 E2 with E0 is V + eps - sigma^2 = l1.
  E3  l1 + h1 = 2 sigma. With l1, h1 >= 0: sigma^2 <= V + eps <= sigma^2 + 2 sigma.
  R1  P4 + P5 = q1          R2  P6 = 0
      R sigma = P3 + 2^24 (P4 + P5) + 2^48 P6.
  R3  2^(M+1) + sigma - s0 - 2 P3 - 2^25 q1 - 2 rr = 0
      Since sigma - s0 = 2 floor(sigma / 2), with R1 and R2 this is twice
      2^M + floor(sigma / 2) = R sigma + rr.
  R4  rr + rq = sigma - 1. With rr, rq >= 0: 0 <= rr < sigma.
Sizes. By the digits' ranges (ledMu5; on what a range rests: see ledMu4) a, Rlo and Rhi are below
2^24 and b is below 2^15, so every product is below 2^48. If also eps < 2^48 and M <= 47, no line
has a term of 2^51 or more. The C++ verifier names these conditions on public numbers
"no-wrap-ledger-eps", and "KL-norm" (a layer's norms) and "policy-norm-F" (the final norm). An
honest row meets R2, since R sigma <= 2^M + sigma / 2 < 2^48. If P does not have exactly seven
members, the result is eight times the constant 1, which does not vanish. -/
def ledLines5 (r : Row5 T) (P : Array T) (eps : E) (two : T) : Array T :=
  let K : E → T := LedK.c
  let add : T → T → T := LedK.add
  let sub : T → T → T := LedK.sub
  let mul : T → E → T := LedK.mul
  let p := fun i => P.getD i (K zeroE)
  if P.size != 7 then Array.replicate 8 (K oneE)
  else
  #[sub (sub (p 1) r.Blo) (mul r.Bhi (ofNat (2 ^ 23))),
    add (sub (sub (sub (add r.Vlo (K eps)) (p 0)) (mul r.Blo (ofNat (2 ^ 25)))) r.l1)
      (mul r.kap (ofNat (2 ^ 48))),
    sub (sub (sub r.Vhi r.Bhi) (p 2)) r.kap,
    sub (add r.l1 r.h1) (mul r.sig (ofNat 2)),
    sub (add (p 4) (p 5)) r.q1,
    p 6,
    sub (sub (sub (sub (add two r.sig) r.s0) (mul (p 3) (ofNat 2))) (mul r.q1 (ofNat (2 ^ 25))))
      (mul r.rr (ofNat 2)),
    add (sub (add r.rr r.rq) r.sig) (K oneE)]

end

/-- The sum of the seven products of an instance (see ledLines5), product i times om[first + i],
from the four values that are opened: a, b, Rlo, Rhi. The caller must make sure that om has these
seven members: a member beyond the end of om counts as 0. -/
def ledProducts5 (om : Array E) (first : Nat) (a b lo hi : E) : E :=
  let w := fun i => om.getD (first + i) zeroE
  [mulE (mulE (w 1) a) b, mulE (mulE (w 2) b) b, mulE (mulE (w 3) lo) a, mulE (mulE (w 4) lo) b,
    mulE (mulE (w 5) hi) a, mulE (mulE (w 6) hi) b].foldl addE (mulE (mulE (w 0) a) a)

end OnBytes.Model
