-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestLedger.lean: tests of OnBytes/Model/Ledger.lean, run when this file compiles.

The program does not import this file.

An honest row of five limbs is made here from whole numbers. From nine convolution sums W_s, eps
and M, the function honest computes V, the carries, sigma = isqrt(V + eps), R and all the rest by
plain arithmetic and spells them in bytes. What is tested:
 1. On an honest row the nine carries' lines and the eight lines vanish.
 2. If one digit is raised by 1, some line does not vanish. This holds for every digit but the six
    of Rlo and Rhi (80 to 85). No line reads these six, so all lines still vanish: Rlo and Rhi enter
    through the products.
 3. The lines formed on affine forms, evaluated at the row's cells, are the lines formed on field
    elements.
 4. ledProducts5 is the weighted sum of the seven products: on two honest rows, and at a, b, Rlo,
    Rhi = 3, 5, 7, 11. These are made up, since on an honest row the seventh product, Rhi b, is 0
    and its term does not show. If any one of the seven products of an honest row is raised by 1,
    some line does not vanish (for Rhi b: the line R2).
 5. The members a, b, sig, s0, Rlo, Rhi, R of the row are the honest numbers.
 6. The counts, the multipliers and the places of the head's six numbers are those of
    verifier/src/vf_norm_digit_rows.h, copied here by hand.
 7. Where there is no line (a tenth carry, a list of six products) the result is 1, not 0.
All sums W_s that are tried are at least 0 and below 2^33, so no carry is negative.
-/
import OnBytes.Model.Ledger

namespace OnBytes.Model.TestLedger

/-- The n bytes of x, the lowest first. -/
def bytes (x n : Nat) : List Nat := (List.range n).map fun j => x / 256 ^ j % 256

/-- The carries c_0 to c_9 and the bytes v_0 to v_8, from the sums W_0 to W_8. -/
def carry : List Nat → Nat → List Nat × List Nat
  | [], c => ([c], [])
  | w :: ws, c =>
    let r := carry ws ((w + c) / 256)
    (c :: r.1, (w + c) % 256 :: r.2)

/-- The largest x from lo to hi - 1 with x^2 ≤ n, by halving. It is assumed that lo^2 ≤ n < hi^2.
The first argument bounds the number of steps. -/
def isqrtLoop : Nat → Nat → Nat → Nat → Nat
  | 0, lo, _, _ => lo
  | k + 1, lo, hi, n =>
    if hi ≤ lo + 1 then lo
    else
      let mid := (lo + hi) / 2
      if mid * mid ≤ n then isqrtLoop k mid hi n else isqrtLoop k lo mid n

/-- The whole part of the square root of a number below 2^128. -/
def isqrt (n : Nat) : Nat := isqrtLoop 70 0 (2 ^ 64) n

#guard [0, 1, 3, 4, 24, 25, 26, 10 ^ 30].map isqrt == [0, 1, 1, 2, 4, 5, 5, 10 ^ 15]

/-- An honest instance: the row's 99 digits, the seven products, and the two halves of sigma (a, b)
and of R (lo, hi). -/
structure Honest where
  digits : Array Nat
  products : Array Nat
  a : Nat
  b : Nat
  lo : Nat
  hi : Nat

/-- The honest instance for the sums W, eps and M. -/
def honest (W : List Nat) (eps M : Nat) : Honest :=
  let V := (W.zipIdx.map fun (w, s) => 256 ^ s * w).sum
  let cv := carry W 0
  let sigma := isqrt (V + eps)
  let a := sigma % 2 ^ 24
  let b := sigma / 2 ^ 24
  let l1 := V + eps - sigma ^ 2
  let h1 := 2 * sigma - l1
  let blo := a * b % 2 ^ 23
  let bhi := a * b / 2 ^ 23
  let over : Int := ((a ^ 2 + 2 ^ 25 * blo + l1 : Nat) : Int) - ((V % 2 ^ 48 + eps : Nat) : Int)
  let kappa4 : Int := over / 2 ^ 48 + 4
  let R := (2 ^ M + sigma / 2) / sigma
  let lo := R % 2 ^ 24
  let hi := R / 2 ^ 24
  let rr := 2 ^ M + sigma / 2 - R * sigma
  { digits :=
      (cv.2 ++ [cv.1.getD 9 0] ++
        ((List.range 8).flatMap fun s => bytes (cv.1.getD (s + 1) 0 + 2 ^ 47) 6) ++
        [a % 256 / 2, a % 2, a / 256 % 256, a / 65536, b % 256, b / 256] ++
        bytes l1 5 ++ bytes h1 5 ++ bytes blo 3 ++ bytes bhi 2 ++ [kappa4.toNat] ++
        bytes lo 3 ++ bytes hi 3 ++ bytes (lo * b + hi * a) 3 ++ bytes rr 5 ++
        bytes (sigma - 1 - rr) 5).toArray
    products := #[a * a, a * b, b * b, lo * a, lo * b, hi * a, hi * b]
    a := a, b := b, lo := lo, hi := hi }

/-- Cell j of a row with the given digits: the digit - 128. -/
def cellOf (digits : Array Nat) (j : Nat) : E := ofInt (((digits.getD j 0 : Nat) : Int) - 128)

/-- All seventeen lines on field elements. -/
def linesOf (digits products : Array Nat) (W : List Nat) (eps M : Nat) : List E :=
  let r : Row5 E := row5 (cellOf digits)
  (W.zipIdx.map fun (w, s) => ledCarry5 r s (ofNat w)) ++
    (ledLines5 r (products.map ofNat) (ofNat eps) (ofNat (2 ^ (M + 1)))).toList

/-- Test 1. -/
def vanish (W : List Nat) (eps M : Nat) : Bool :=
  let h := honest W eps M
  h.digits.size == 99 && h.digits.all (· < 256) &&
  (List.range 99).all (fun j => ledMu5 j * h.digits.getD j 0 < 256) &&
  (linesOf h.digits h.products W eps M).length == 17 &&
  (linesOf h.digits h.products W eps M).all isZeroE

/-- Test 2. -/
def everyDigitCounts (W : List Nat) (eps M : Nat) : Bool :=
  let h := honest W eps M
  (List.range 99).all fun j =>
    (decide (80 ≤ j) && decide (j ≤ 85)) !=
      !(linesOf (h.digits.modify j (· + 1)) h.products W eps M).all isZeroE

/-- The value of a form without slots, where entry idx of the one row has the value cell idx. -/
def valueOf (cell : Nat → E) (f : Aff) : E :=
  f.ents.foldl (fun s x => maddE s x.coef (cell x.idx)) f.const

/-- Test 3. -/
def formsAgree (W : List Nat) (eps M : Nat) : Bool :=
  let h := honest W eps M
  let r : Row5 Aff := row5 fun j => Aff.ent 0 0 j
  let forms := (W.zipIdx.map fun (w, s) => ledCarry5 r s (Aff.ofConst (ofNat w))) ++
    (ledLines5 r (h.products.map fun p => Aff.ofConst (ofNat p)) (ofNat eps)
      (Aff.ofConst (ofNat (2 ^ (M + 1))))).toList
  -- one digit is raised, so that not all values are 0
  let digits := h.digits.modify 3 (· + 1)
  forms.map (valueOf (cellOf digits)) == linesOf digits h.products W eps M

/-- Sums that make V about 2^77, so that sigma has both its parts. -/
def large : List Nat :=
  [123456789, 987654321, 55555, 4242424242, 17, 0, 888888, 31415, 9000]

/-- Sums of the same size for which the carry kappa of the square root's line is 1, not 0. -/
def carried : List Nat :=
  [123694359, 987654321, 55585, 4242424242, 917, 30, 889278, 31445, 8970]

/-- Sums that make V small, so that R has both its parts. -/
def small : List Nat := [1000, 3, 0, 0, 0, 0, 0, 0, 0]

#guard vanish large 1 44
#guard vanish large 50000 47
#guard vanish carried 1 44
#guard (honest carried 1 44).digits.getD 79 0 == 5
#guard vanish small 1 44
#guard vanish small 7 24
#guard everyDigitCounts large 1 44
#guard everyDigitCounts small 1 44
#guard formsAgree large 1 44
#guard formsAgree small 1 44

/-- Test 4, with the weights taken from place 2 of a longer list. -/
def productsAgree (W : List Nat) (eps M : Nat) : Bool :=
  let h := honest W eps M
  let om : Array E := Array.ofFn (n := 9) fun i =>
    E.mk3 (UInt64.ofNat (i.val + 5)) 3 (UInt64.ofNat (7 * i.val))
  ledProducts5 om 2 (ofNat h.a) (ofNat h.b) (ofNat h.lo) (ofNat h.hi) ==
    (List.range 7).foldl
      (fun s i => maddE s (om.getD (2 + i) zeroE) (ofNat (h.products.getD i 0))) zeroE

#guard productsAgree large 1 44
#guard productsAgree small 1 44

/-- Test 4 on made-up numbers. -/
def productsAgreeAt (a b lo hi : Nat) : Bool :=
  let om : Array E := Array.ofFn (n := 9) fun i =>
    E.mk3 (UInt64.ofNat (i.val + 5)) 3 (UInt64.ofNat (7 * i.val))
  let products := [a * a, a * b, b * b, lo * a, lo * b, hi * a, hi * b]
  ledProducts5 om 2 (ofNat a) (ofNat b) (ofNat lo) (ofNat hi) ==
    (List.range 7).foldl
      (fun s i => maddE s (om.getD (2 + i) zeroE) (ofNat (products.getD i 0))) zeroE

#guard productsAgreeAt 3 5 7 11

/-- If one product is raised by 1, some line does not vanish. -/
def everyProductCounts (W : List Nat) (eps M : Nat) : Bool :=
  let h := honest W eps M
  (List.range 7).all fun i =>
    !(linesOf h.digits (h.products.modify i (· + 1)) W eps M).all isZeroE

#guard everyProductCounts large 1 44
#guard everyProductCounts small 1 44

#guard (ledNS 5, ledNR 5, ledNP 5, ledNO 5, ledLines 5, ledNRH 5) == (9, 99, 7, 4, 8, 120)
#guard (ledNS 4, ledNR 4, ledNP 4, ledNO 4, ledLines 4, ledNRH 4) == (7, 74, 3, 3, 5, 95)
#guard (ledG.map fun x => x.2).sum == ledNE
#guard ledG == [(0, 5), (5, 1), (6, 5), (11, 5), (16, 2), (18, 3)]
#guard (ledNE, exc, bigH) == (21, 3, 137438953472)

/-- The digits whose multiplier is not 1, each with its multiplier. -/
def multipliers (mu : Nat → Nat) : List (Nat × Nat) :=
  ((List.range 200).map fun i => (i, mu i)).filter fun x => x.2 != 1

#guard multipliers ledMu4 == [(7, 32), (44, 2), (45, 128), (48, 4)]
#guard multipliers ledMu5 == [(9, 4), (58, 2), (59, 128), (63, 2), (76, 2), (79, 32)]
#guard multipliers (ledMu 5) == multipliers ledMu5
#guard multipliers (ledMu 4) == multipliers ledMu4

/-- Test 5: the members of the row that the sub-proofs read in addition to the lines. -/
def membersAgree (W : List Nat) (eps M : Nat) : Bool :=
  let h := honest W eps M
  let r : Row5 E := row5 (cellOf h.digits)
  r.a == ofNat h.a && r.b == ofNat h.b && r.Rlo == ofNat h.lo && r.Rhi == ofNat h.hi &&
  r.R == ofNat (h.lo + 2 ^ 24 * h.hi) && r.sig == ofNat (h.a + 2 ^ 24 * h.b) &&
  r.s0 == ofNat (h.a % 2) && r.Dg.size == 99 && r.c.size == 10

#guard membersAgree large 1 44
#guard membersAgree carried 1 44
#guard membersAgree small 1 44

-- where there is no line, the result does not vanish
#guard ledCarry5 (row5 (cellOf (honest small 1 44).digits)) 9 zeroE == oneE
#guard ledLines5 (row5 (cellOf (honest small 1 44).digits)) (Array.replicate 6 zeroE) zeroE zeroE
  == Array.replicate 8 oneE

end OnBytes.Model.TestLedger
