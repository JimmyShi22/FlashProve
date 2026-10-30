-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Norm.lean: THE NORM'S ROW, a part of the protocol that several kinds of block
call: root and reciprocal of NI norms at once. General in two letters: NI, how many norms are
batched; and a reader, which says where a norm's limbs and row are read. Definitions with code; no
theorem. Beneath it: HeadParts.lean, and for the row's fields and its 17 linear equations the part
OnBytes/Desc/First/P6/NormRow.lean. Its one caller so far is the final norm (HeadNorm.lean), with NI
= 1: at more norms nothing of it has been tried.

WHAT IT IS ABOUT, in integers, for each norm i < NI at EVERY position t. str_i: d features.
  Vsq = sum over k of str_i[k]^2      sig = floor(sqrt(Vsq + epsF i))
  R   = floor((2^(MF i) + floor(sig / 2)) / sig)
What is done with R (the rounding of str_i R, the clamp) is the caller's.

HOW. The prover has committed to str_i in five limbs, and for each norm and position to a row of 99
byte digits that spell Vsq, sig, R, their slacks and carries. Products are not linear, so each
product that the equations need is a hidden scalar of its own, tied to its factors by a sumcheck:
  squares   for each norm the nine sums W of limb products of str_i^2, at a drawn point pV on the
            positions; one sumcheck for all norms, under a drawn point rhoI on their numbers;
  products  for each norm seven products P of the row's fields a, b, Rlo, Rhi (sig = a + 2^24 b; R
            likewise), at pV; one sumcheck for all.
With them Vsq's bytes, the root and the reciprocal are linear equations on the row at pV.
It leaves 5 + 21 NI forms, asks for three kinds of read, and opens no oracle. By itself it bounds no
digit. From outside it needs: that each digit is a byte (below 256 / mul j): a key of the caller's
lookup, at a fourth point; that a cell is bounded, and that a read is the sum of the cells: the
range check's.

WHAT COULD NOT BE MADE GENERAL, or is not tried. Five limbs are written in. The hearing is cut
behind its first round, because a caller that is meant (the layers' first group) has rounds of its
own there.
The caller's own sumcheck on str_i R is not here: the final norm's and the layers' differ in kind.

-/
import Johnson.Desc.Kinds.HeadParts
import OnBytes.Desc.First.P6.NormRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Norm

open OnBytes (E)
open OnBytes.Desc.First (P6.Row P6.Row.ofDigits P6.carries P6.root P6.reciprocal P6.summand)

/-! ## Public -/

/-- T = 2^lt positions. d features, in blocks of S2 = 2^ls. NI norms. MF i, epsF i: norm i's shift
and its epsilon. -/
class Sizes where
  (lt ls d NI : Nat)
  (MF epsF : Nat → Nat)
export Sizes (lt ls d NI MF epsF)
variable [Sizes]

/-- The number of positions. -/
def T : Nat := 2 ^ lt
/-- The number of features in a block. -/
def S2 : Nat := 2 ^ ls
/-- With padding there are 2^lPd features. -/
def lPd : Nat := clog2 d
/-- With padding there are 2^lNI norms. -/
def lNI : Nat := clog2 NI

/-! ## Hear -/

/-- What the steps leave. -/
class Heard where
  pV : Point                     -- a point on the positions, for the rows
  (W : Array Hid) (gam : E)      -- by norm: nine sums of limb products of the squares, at pV
  rhoI : Point                   -- a point on the norms' numbers; empty at one norm
  squares : Sum                  -- the sums of squares; end values: one map, twice
  (P : Array Hid) (om : E)       -- by norm: seven products of the row's fields, at pV
  products : Sum                 -- at pV; end values, by norm: the four fields a, b, Rlo, Rhi
export Heard (pV W gam rhoI squares P om products)

/-- What the sums of squares must equal: the features are summed plainly, so 2^-lPd stands in
front. -/
def squaresStart (W : Array Hid) (gam : E) (rhoI : Point) : Form :=
  half ^ lPd • ∑ i < NI, ∑ s < 9, (eq rhoI i * gam ^ s) • (W.getD (9 * i + s) {}).var

/-- THE ROUNDS, in order, and the verifier on them: the first. -/
def hearPoint : Hear Point := drawPoint lt

/-- The others. Who sends what in a line's rounds is said at the part (HeadParts.lean). A sumcheck
is told the point of its equality weights; halves n stands for a plain sum over n bits. -/
def hearRest (pV : Point) : Hear Heard := do
  let (W, gam) ← sendThenBatch (9 * NI) 9
  let rhoI ← if lNI == 0 then pure #[] else drawJoin lNI
  let squares ← level (rhoI ++ halves lPd ++ pV) (squaresStart W gam rhoI)
  let (P, om) ← sendThenBatch (7 * NI)
  let products ← sumcheck pV (4 * NI)
  pure { pV, W, gam, rhoI, squares, P, om, products }

/-- All, for a caller that has no round between. -/
def hear : Hear Heard := do hearRest (← hearPoint)

/-- The same lines as data. -/
def rounds : List Round :=
  drawPoint.rounds lt ++ sendThenBatch.rounds (9 * NI) 9
    ++ (if lNI == 0 then [] else drawJoin.rounds lNI) ++ level.rounds (lNI + lPd + lt)
    ++ sendThenBatch.rounds (7 * NI) ++ sumcheck.rounds lt (4 * NI)
variable [Heard]

/-! ## Reads: committed behind the caller's rounds -/

/-- The three kinds of read: the streams at the end of squares; the rows at pV; the rows at the end
of products. -/
inductive Read | streams | rowsAtPV | rowsAtProducts

/-- Under which weights. -/
def Read.weights : Read → Weights
  | .streams        => .long (eq (squares.r.extract (lNI + lPd - ls) (lNI + lPd)))
                             (eq (squares.r.extract (lNI + lPd) (lNI + lPd + lt)))
  | .rowsAtPV       => .short (eq pV)
  | .rowsAtProducts => .short (eq products.r)

/-- THE READER: where the caller's vector of reads holds them, each as a variable of a form. limb i
l k: block k of limb l of norm i's stream, in the read streams. cell x i j: the cell of digit j of
norm i's row, in the read x of the rows. Where a limb lies is the caller's layout: at the final norm
limb l begins at feature l d; at the layers the limb is the outer index over several streams. -/
class Reads where
  limb : Nat → Nat → Nat → Form
  cell : Read → Nat → Nat → Form
export Reads (limb cell)
variable [Reads]

/-! ## Claims: each form must be 0 -/

/-- Digit j of norm i's row through a read: a cell holds its digit less 128. -/
def digit (x : Read) (i j : Nat) : Form := cell x i j + off1
/-- Norm i's row through a read. -/
def rowAt (x : Read) (i : Nat) : P6.Row := P6.Row.ofDigits (digit x i)

/-- Vsq: the square of sum_l gam^l limb_l, summed over the features, is sum_s gam^s W s. The two end
values are one map at one point: they are equal, and the first is the streams' value there. -/
def squareForms : List Form :=
  let vL := squares.end_ 0; let vR := squares.end_ 1
  let w := eq (squares.r.extract 0 (lNI + lPd - ls))
  [squares.left (vL.shown * vR.shown),
   vL.var - vR.var,
   vL.var - ∑ i < NI, ∑ k < d / S2, ∑ l < 5, (w (i * 2 ^ lPd / S2 + k) * gam ^ l) • limb i l k]

/-- The hidden P are products of the rows' fields: a sumcheck, whose end values are these fields. -/
def productForms : List Form :=
  let s := fun j => (products.end_ j).shown
  [products.claimed.var - ∑ n < 7 * NI, om ^ n • (P.getD n {}).var,
   products.left (∑ i < NI, P6.summand (fun n => om ^ (7 * i + n)) fun j => s (4 * i + j))]
  ++ (List.range NI).flatMap fun i =>
    let f := rowAt .rowsAtProducts i
    [f.a, f.b, f.Rlo, f.Rhi].zipIdx.map fun x => (products.end_ (4 * i + x.2)).var - x.1

/-- With them the carries', the root's and the reciprocal's equations are linear (the part
NormRow.lean): the carries of all norms, then root and reciprocal norm by norm. -/
def rowForms : List Form :=
  ((List.range NI).flatMap fun i =>
    P6.carries (rowAt .rowsAtPV i) (digit .rowsAtPV i) fun s => (W.getD (9 * i + s) {}).var)
  ++ (List.range NI).flatMap fun i =>
    let p := fun n => (P.getD (7 * i + n) {}).var
    P6.root (rowAt .rowsAtPV i) p (epsF i : Nat) ++
      P6.reciprocal (rowAt .rowsAtPV i) p ((2 ^ (MF i + 1) : Nat) : Form)

/-- All 5 + 21 NI, in the order in which the callers' segments number them. -/
def forms : List Form := squareForms ++ productForms ++ rowForms

end VerifiableInference.Desc.Kinds.Norm
