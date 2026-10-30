-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/NormRow.lean: a norm's row of digits, made in whole numbers.

WHAT IT DOES NOT SHOW. No law says that the row made here meets the verifier's claims, or that its
digits lie in the ranges that the lookup asks: the tests at the end of this file try the 17 linear
lines of a row at four synthetic inputs, one of them at a second pair (M, eps), and see, for each of
the 99 cells, some line fail when that cell is raised by one. They are evaluations by Lean at these
inputs: no proof. No range of a digit is tested. At all of these inputs kap is 0, so its rule is
tried at that one value; at the second pair R is 0. Where a number does not fit the bytes that the
row has for it, its high part is dropped without a word, and the row is then false.
THE ROW IS MEANT FOR 24 ≤ M ≤ 47, 1 ≤ eps < 2^48 AND Vsq + eps < 2^78, which the
verifier's tests on the public numbers and the model's ranges are meant to give; none of the three
is asked here. Beyond M = 47 the product of the two high pieces need not be 0, which one line asks;
at eps = 0 and Vsq = 0 the root is 0 and the division by it yields 0. Nothing is said of any model's
run.

WHAT IT DEFINES. For one norm at one token the prover commits to 99 cells, each a digit less 128
(docs/format/11-2-feed-forward-segment.md, "A norm's row of digits", five limbs;
OnBytes/Model/Ledger.lean has the same table). With W_0 .. W_8 the nine sums of limb products of the
token's stream values, eps and M the norm's public numbers:
  Vsq = the sum of 256^s W_s;   sig = floor(sqrt(Vsq + eps));
  R = floor((2^M + floor(sig / 2)) / sig)
and the row spells Vsq, the carries of that sum, sig in two pieces a and b, R in two pieces, and the
slacks and partial products that tie them. Definitions with code. No theorem.

  bytesOf, intOfF        tools
  normDigits, normRow    the 99 digits; the 99 cells
  rowLines               the verifier's 17 lines of a row at one token, as field elements: the nine
                         carries and the eight lines of OnBytes/Desc/First/P6/NormRow.lean, with the
                         seven products taken of the row's own fields
  limbSums               W_0 .. W_8 of a token's limbs

Nothing on any property.
No property is claimed.
-/
import OnBytes.Model.LayerTables
import OnBytes.Desc.First.P6.NormRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest
open OnBytes
open OnBytes.Model (Aff ofNat ofInt)
open OnBytes.Model.Layer (isqrt)

/-- The n lowest bytes of x, the lowest first. -/
def bytesOf (n x : Nat) : List Nat := (List.range n).map fun j => x / 256 ^ j % 256

/-- A word of the field as a whole number of either sign: the residue nearest to 0. -/
def intOfF (x : F) : Int :=
  if 2 * x.toNat > pW.toNat then Int.ofNat x.toNat - Int.ofNat pW.toNat else Int.ofNat x.toNat

/-- **The 99 digits of a norm's row at one token.** M, eps: the norm's public numbers. W: the nine
sums of limb products. -/
def normDigits (M eps : Nat) (W : Array Int) : Array Int :=
  -- byte s of Vsq and the carry into byte s + 1: W_s + c_s = v_s + 256 c_(s+1), 0 ≤ v_s < 256
  let bc := (List.range 9).foldl
    (fun (st : Int × Array Int × Array Int) s =>
      let acc := W.getD s 0 + st.1
      let v := acc.emod 256
      let c := (acc - v) / 256
      (c, st.2.1.push v, st.2.2.push c))
    (0, #[], #[])
  -- v_9 is the last carry
  let v := bc.2.1.push bc.1
  let V : Nat := ((List.range 10).foldl (fun (s : Int) j => s + 256 ^ j * v.getD j 0) 0).toNat
  let sig : Nat := isqrt (V + eps)
  let a : Nat := sig % 2 ^ 24
  let b : Nat := sig / 2 ^ 24
  let l1 : Nat := V + eps - sig * sig
  let h1 : Nat := 2 * sig - l1
  let Blo : Nat := a * b % 2 ^ 23
  let Bhi : Nat := a * b / 2 ^ 23
  let kap : Int := Int.ofNat (V / 2 ^ 48) - Int.ofNat Bhi - Int.ofNat (b * b)
  let R : Nat := (2 ^ M + sig / 2) / sig
  let Rlo : Nat := R % 2 ^ 24
  let Rhi : Nat := R / 2 ^ 24
  let q1 : Nat := Rlo * b + Rhi * a
  let rr : Nat := 2 ^ M + sig / 2 - R * sig
  let rq : Nat := sig - 1 - rr
  let nat (l : List Nat) : List Int := l.map Int.ofNat
  (v.toList ++
    ((List.range 8).flatMap fun s => nat (bytesOf 6 (bc.2.2.getD s 0 + 2 ^ 47).toNat)) ++
    nat [a % 256 / 2, a % 2, a / 2 ^ 8 % 256, a / 2 ^ 16 % 256, b % 256, b / 256] ++
    nat (bytesOf 5 l1) ++ nat (bytesOf 5 h1) ++ nat (bytesOf 3 Blo) ++ nat (bytesOf 2 Bhi) ++
    [kap + 4] ++
    nat (bytesOf 3 Rlo) ++ nat (bytesOf 3 Rhi) ++ nat (bytesOf 3 q1) ++ nat (bytesOf 5 rr) ++
    nat (bytesOf 5 rq)).toArray

/-- **The 99 cells of a norm's row at one token**: each digit less 128. -/
def normRow (M eps : Nat) (W : Array Int) : Array Int := (normDigits M eps W).map (· - 128)

/-- **The verifier's lines of a row, at one token**: the nine carries and then the eight lines, each
as the field element that must be 0. cells: the row's 99 cells. The seven products are those of the
row's own fields a, b, Rlo, Rhi. -/
def rowLines (M eps : Nat) (W cells : Array Int) : List E :=
  let K (x : E) : Aff := Aff.ofConst x
  let D (j : Nat) : Aff := K (ofInt (cells.getD j 0 + 128))
  let f := P6.Row.ofDigits D
  let four := #[f.a.const, f.b.const, f.Rlo.const, f.Rhi.const]
  let P (r : Nat) : Aff :=
    let x := P6.rowProducts.getD r (0, 0)
    K (mulE (four.getD x.1 zeroE) (four.getD x.2 zeroE))
  (P6.carries f D (fun s => K (ofInt (W.getD s 0))) ++
    P6.lines f P (ofNat eps) (K (ofNat (2 ^ (M + 1))))).map (·.const)

/-- The nine sums of limb products of one token: W_s is the sum, over the features j < d and the
ordered pairs (lb, lb') with lb + lb' = s, of limb lb times limb lb' of feature j. xl: the number of
limbs. -/
def limbSums (xl d : Nat) (limb : Nat → Nat → Int) : Array Int :=
  (List.range d).foldl
    (fun acc j =>
      let L := (Array.range xl).map fun lb => limb lb j
      (List.range xl).foldl
        (fun acc lb =>
          (List.range xl).foldl
            (fun (acc : Array Int) lc => acc.modify (lb + lc) (· + L.getD lb 0 * L.getD lc 0)) acc)
        acc)
    (Array.replicate (2 * xl - 1) 0)

/-! ## Tests -/

namespace NormRowTest

/-- Every line of the row made for W is 0. -/
def rowHolds (M eps : Nat) (W : Array Int) : Bool :=
  (rowLines M eps W (normRow M eps W)).all (· == zeroE)

/-- How many of the 17 lines are not 0 at the made row with cell j raised by one. -/
def linesBent (M eps : Nat) (W : Array Int) (j : Nat) : Nat :=
  ((rowLines M eps W ((normRow M eps W).modify j (· + 1))).filter (· != zeroE)).length

/-- A synthetic input: three features, small limbs of either sign. -/
def toyW1 : Array Int := limbSums 5 3 fun lb j => Int.ofNat (7 * lb + 3 * j) - 11

/-- All sums 0. -/
def toyW2 : Array Int := Array.replicate 9 0

/-- 512 features whose four low limbs lie at the bytes' ends and whose top limb is -1, 0 or 1. -/
def toyW3 : Array Int := limbSums 5 512 fun lb j =>
  if lb == 4 then Int.ofNat (j % 3) - 1 else if (lb + j) % 3 == 0 then -128 else 127

/-- Three features with one limb each: 3, 4, 12. -/
def toyW4 : Array Int := limbSums 5 3 fun lb j => if lb == 0 then #[3, 4, 12].getD j 0 else 0

#guard (normRow 44 1 toyW1).size == 99
#guard (rowLines 44 1 toyW1 (normRow 44 1 toyW1)).length == 17
#guard rowHolds 44 1 toyW1
#guard rowHolds 44 1 toyW2
#guard rowHolds 44 1 toyW3
#guard rowHolds 30 977 toyW1
-- at the third input sig has a high piece; at the second sig = 1 and R has a high piece
#guard (normDigits 44 1 toyW3).getD 62 0 != 0
#guard (normDigits 44 1 toyW2).getD 85 0 != 0
-- every cell is read by some line: raised by one, it makes a line fail
#guard (List.range 99).all fun j => linesBent 44 1 toyW1 j != 0
#guard (List.range 99).all fun j => linesBent 44 1 toyW3 j != 0
-- another sum, another eps, another M: the row made for the true ones fails
#guard (rowLines 44 1 (toyW1.modify 4 (· + 1)) (normRow 44 1 toyW1)).any (· != zeroE)
#guard (rowLines 44 2 toyW1 (normRow 44 1 toyW1)).any (· != zeroE)
#guard (rowLines 45 1 toyW1 (normRow 44 1 toyW1)).any (· != zeroE)
-- written numbers: Vsq = 9 + 16 + 144 = 169; with eps = 1, sig = 13 = 2 * 6 + 1, l1 = 1, h1 = 25
#guard (normDigits 44 1 toyW4).toList.take 2 == [169, 0]
#guard ((normDigits 44 1 toyW4).toList.drop 58).take 2 == [6, 1]
#guard (normDigits 44 1 toyW4).getD 64 0 == 1 && (normDigits 44 1 toyW4).getD 69 0 == 25
#guard rowHolds 44 1 toyW4

end NormRowTest

end OnBytes.Desc.First.K4.Honest
