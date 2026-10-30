-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P6/NormRow.lean: the norm's row: the linear forms of one norm at one point over
the tokens, written as formulas. A part beneath two kinds: a layer's norms (the layers' own rounds)
call it once for each norm of the group, the final norm (the head's own rounds) once.

In integers, for one norm at one position, with str the stream:
  Vsq = the sum over k of str[k]^2;   sig = floor(sqrt(Vsq + eps));
  R = floor((2^M + floor(sig / 2)) / sig).
The prover commits to a row of 99 digits that spell these numbers, their slacks and the carries. The
forms below write the equations on the digits, the nine sums of limb products W and the seven
products P of the row's fields; each form must be 0. THE PART ALONE BOUNDS NO DIGIT: the forms are
linear in the row's cells and hold in the field. That each digit is in its range is its caller's
lookup's matter.

ITS LETTERS. D: the 99 digits as forms (where a norm's row is read). W: the nine sums of limb
products. P: the seven row products. eps: the constant under the root. two: 2^(M + 1).
Main names (namespace `OnBytes.Desc.First.P6`): `Row`, `Row.ofDigits`, `carries` (9 forms),
`root` (4), `reciprocal` (4), `lines` (the last two), `rowProducts`, `summand`.

Credit. The formulas are those written for the final norm (Johnson/Desc/Kinds/HeadParts.lean);
here eps and two are letters, and `summand` is written after its sum over `rowProducts`. Runs have
laid all of this file in the places of `verify-on-bytes`'s routines (row5At, ledCarry5, ledLines5,
ledProducts5) at all layers' links of both stored proofs: the ledger behind the claims came out the
same, in the fields compared.
Limits. Definitions alone: no law. It holds no test: 21 formulas with the four shown values that its
callers compare. From the field to the integers nothing is said here.
-/
import OnBytes.Model.Hide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P6
open OnBytes OnBytes.Model

/-- A public constant plus public coefficients on hidden values and on entries of the reads. -/
abbrev Form : Type := Aff

local instance : NatCast Form := ⟨fun n => Aff.ofConst (ofNat n)⟩
local instance (n : Nat) : OfNat Form n := ⟨Aff.ofConst (ofNat n)⟩
local instance : HSMul Nat Form Form := ⟨fun k f => Aff.scale f (ofNat k)⟩

/-- The sum of f i over i < n. -/
def sumTo (n : Nat) (f : Nat → Form) : Form := (List.range n).foldl (fun s i => s + f i) 0

/-- The fields of a position's row. Vsq = Vlo + 2^48 Vhi: the sum of the stream's squares.
sig = a + 2^24 b: the root; s0: its lowest bit. l1, h1: the root's two slacks. a b = Blo + 2^23 Bhi.
kap: a carry. R = Rlo + 2^24 Rhi: the reciprocal. q1 = Rlo b + Rhi a. rr, rq: the reciprocal's
remainder and its slack. c s: the carry into byte s of the sum of squares. -/
structure Row where
  (Vlo Vhi a b s0 sig l1 h1 Blo Bhi kap Rlo Rhi R q1 rr rq : Form)
  c : Nat → Form

/-- The fields from the 99 digits D 0, D 1, ... -/
def Row.ofDigits (D : Nat → Form) : Row :=
  let dig (j n : Nat) : Form := sumTo n fun i => (256 ^ i : Nat) • D (j + i)
  let a := (2 : Nat) • D 58 + D 59 + (2 ^ 8 : Nat) • D 60 + (2 ^ 16 : Nat) • D 61
  let b := D 62 + (2 ^ 8 : Nat) • D 63
  let Rlo := dig 80 3
  let Rhi := dig 83 3
  { Vlo := dig 0 6, Vhi := dig 6 4, a, b, s0 := D 59, sig := a + (2 ^ 24 : Nat) • b,
    l1 := dig 64 5, h1 := dig 69 5, Blo := dig 74 3, Bhi := dig 77 2, kap := D 79 - 4,
    Rlo, Rhi, R := Rlo + (2 ^ 24 : Nat) • Rhi, q1 := dig 86 3, rr := dig 89 5, rq := dig 94 5,
    c := fun s => if s == 0 then 0 else if s == 9 then D 9
      else dig (10 + 6 * (s - 1)) 6 - ((2 ^ 47 : Nat) : Form) }

/-- The nine sums of limb products W s are the bytes of Vsq, with carries. -/
def carries (ρ : Row) (D W : Nat → Form) : List Form :=
  (List.range 9).map fun s => W s + ρ.c s - D s - (256 : Nat) • ρ.c (s + 1)

/-- sig is the largest integer whose square is at most Vsq + eps: Vsq + eps - sig^2 = l1 and
l1 + h1 = 2 sig, in two halves of 48 bits. P: the seven row products
a a, a b, b b, Rlo a, Rlo b, Rhi a, Rhi b. -/
def root (ρ : Row) (P : Nat → Form) (eps : E) : List Form :=
  [P 1 - ρ.Blo - (2 ^ 23 : Nat) • ρ.Bhi,
   ρ.Vlo + Aff.ofConst eps - P 0 - (2 ^ 25 : Nat) • ρ.Blo - ρ.l1 + (2 ^ 48 : Nat) • ρ.kap,
   ρ.Vhi - ρ.Bhi - P 2 - ρ.kap,
   ρ.l1 + ρ.h1 - (2 : Nat) • ρ.sig]

/-- R = floor((2^M + floor(sig / 2)) / sig): 2^M + floor(sig / 2) - R sig = rr, and
rr + rq = sig - 1. two: 2^(M + 1). -/
def reciprocal (ρ : Row) (P : Nat → Form) (two : Form) : List Form :=
  [P 4 + P 5 - ρ.q1,
   P 6,
   two + ρ.sig - ρ.s0 - (2 : Nat) • P 3 - (2 ^ 25 : Nat) • ρ.q1 - (2 : Nat) • ρ.rr,
   ρ.rr + ρ.rq - ρ.sig + 1]

/-- The eight lines of a norm's row: the root's four, the reciprocal's four. -/
def lines (ρ : Row) (P : Nat → Form) (eps : E) (two : Form) : List Form :=
  root ρ P eps ++ reciprocal ρ P two

/-- The seven row products, as pairs of a, b, Rlo, Rhi by their places 0 to 3:
a a, a b, b b, Rlo a, Rlo b, Rhi a, Rhi b. -/
def rowProducts : List (Nat × Nat) := [(0, 0), (0, 1), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1)]

/-- The summand of the products' sumcheck on the four end values as shown: product r under the
weight om r. -/
def summand (om : Nat → E) (s : Nat → E) : E :=
  rowProducts.zipIdx.foldl (fun t x => addE t (mulE (mulE (om x.2) (s x.1.1)) (s x.1.2))) zeroE

end OnBytes.Desc.First.P6
