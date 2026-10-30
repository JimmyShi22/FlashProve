-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Level2Def.lean: levels over an array with gaps (definitions).

The levels are a recursive column test for one linear claim on a committed array. A level runs a
sumcheck, commits a next array that holds a
fold A' and a random combination A'' (coefficients θ) of the present array's rows, and reads q
columns of the present array; the end of the sumcheck, an equation on the fold ((T-end) below), and
the comparison with these columns become one linear claim on the next array (`Lev2.nextClaim`). The
last array is sent in the clear and checked.

Unlike in Blocks/LevelDef.lean an array may have gaps. It is cut into strips of `code.msg` entries,
and only the strips in use are committed. A committed strip has a rank i (its place in a column of
the encoded array) and a number `idx i` (its place in the array and in the sumcheck's hypercube). A
strip whose number is not listed is not sent and counts as 0. So a column has `rows` symbols, and
the sumcheck runs over all 2^mrow strip numbers. With `idx` = id the definitions are those of
Blocks/LevelDef.lean. The implementation commits only the strips in use.

This file's model is not the released programs' (lean/LIMITS.md, L1); how the released programs do
it: docs/format/FORMAT.md. In this model: the coefficients θ of the proximity test are a separate
verifier message after an empty prover message; `idx` is a parameter.

Notation: `a : Lev2 F`: the format of one array; `a.mu`: ℕ; the hypercube has mu variables
(`Lev2.mle`); `a.mrow`: ℕ; the row part of the point ζ is its first mrow coordinates (`Lev2.foldW`:
`eqN a.mrow 0 ζ`); `a.q`: ℕ; q columns are read.

Limits: nothing is proved here. This file has the formats, the rounds (`levels2Shape`) and the claim
and array of the next level; it defines no verifier and no prover on them.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Blocks.Basic
import Code.Iface
import Iop.ShapeKit

namespace Blocks
open Iop

/-- The format of one array (fixed by the public parameters): rows strips are committed; the strip
of rank i has the number idx i (idx is read at i < rows only); q columns are read. -/
structure Lev2 (F : Type) where
  code : Code.Enc F
  rows : ℕ
  idx : ℕ → ℕ
  mrow : ℕ
  mu : ℕ
  q : ℕ
  [nePos : Nonempty (Fin code.n)]

attribute [instance] Lev2.nePos

namespace Lev2
variable {F : Type} [Field F] (a : Lev2 F) (E : Type) [Field E] [Fintype E]
  [DecidableEq E] [Algebra F E]

/-- the array; the received word in the place of its encoding (at each position a column); a linear
claim on it -/
abbrev Arr : Type := Fin a.rows → Fin a.code.msg → E
abbrev Word : Type := Fin a.code.n → Fin a.rows → E
structure Claim where
  coef : Fin a.rows → Fin a.code.msg → E
  v : E

variable {E}

/-- the committed strips of an array that is given by its entries as one sequence: entry t is in the
strip with the number t / msg at the index t % msg -/
def ofFlat (f : ℕ → E) : a.Arr E := fun i j => f (a.idx i.val * a.code.msg + j.val)
/-- the encoding of a row: no randomness -/
def encRow (m : Fin a.code.msg → E) : Fin a.code.n → E :=
  (a.code.GE E).mulVec (a.code.fm m (fun _ => 0))
/-- the honest encoding of an array -/
def word (A : a.Arr E) : a.Word E := fun p i => a.encRow (A i) p

def arrN (A : a.Arr E) : ℕ → ℕ → E := fun i j => nat (fun i' => nat (A i') j) i

/-- the multilinear extension of an array (f i j: entry j of the strip of rank i), placed at (idx i)
‖ j in the hypercube of mu variables -/
def mle (f : ℕ → ℕ → E) (pt : ℕ → E) : E :=
  ∑ i ∈ Finset.range a.rows,
    ∑ j ∈ Finset.range a.code.msg, eqN a.mu 0 pt (a.idx i * 2 ^ (a.mu - a.mrow) + j) * f i j

def ptAt (ζ : ℕ → E) (j : ℕ) (y : E) (z : ℕ) : ℕ → E :=
  fun t => if t < j then ζ t else if t = j then y else if z.testBit (a.mu - 1 - t) then 1 else 0

/-- the two coefficients of a round polynomial that are sent -/
def rp0 (c A : ℕ → ℕ → E) (ζ : ℕ → E) (j : ℕ) : E :=
  ∑ z ∈ Finset.range (2 ^ (a.mu - j - 1)), a.mle c (a.ptAt ζ j 0 z) * a.mle A (a.ptAt ζ j 0 z)
def rp2 (c A : ℕ → ℕ → E) (ζ : ℕ → E) (j : ℕ) : E :=
  ∑ z ∈ Finset.range (2 ^ (a.mu - j - 1)), (a.mle c (a.ptAt ζ j 1 z) - a.mle c (a.ptAt ζ j 0 z)) *
    (a.mle A (a.ptAt ζ j 1 z) - a.mle A (a.ptAt ζ j 0 z))

/-- the running claim after all rounds: cl_j = ζ_j cl_(j-1) + (1 - 2 ζ_j) s0_j + (ζ_j² - ζ_j) s2_j,
unrolled -/
def clEnd (v : E) (ζ s0 s2 : ℕ → E) : E :=
  (∏ i ∈ Finset.range a.mu, ζ i) * v +
    ∑ j ∈ Finset.range a.mu, ((1 - 2 * ζ j) * (∏ i ∈ Finset.Ico (j + 1) a.mu, ζ i) * s0 j +
      (ζ j ^ 2 - ζ j) * (∏ i ∈ Finset.Ico (j + 1) a.mu, ζ i) * s2 j)

/-- the fold of the rows of a received word, or of an array, at the row part of the point; and their
θ-combination -/
def foldW (w : a.Word E) (ζ : ℕ → E) (p : Fin a.code.n) : E :=
  ∑ i, eqN a.mrow 0 ζ (a.idx i.val) * w p i
def combW (w : a.Word E) (θ : Fin a.rows → E) (p : Fin a.code.n) : E := ∑ i, θ i * w p i
def foldA (A : a.Arr E) (ζ : ℕ → E) : Fin a.code.msg → E := fun j =>
  ∑ i, eqN a.mrow 0 ζ (a.idx i.val) * A i j
def combA (A : a.Arr E) (θ : Fin a.rows → E) : Fin a.code.msg → E := fun j => ∑ i, θ i * A i j

/-- (T-end): the end of the sumcheck, read on a candidate for A' -/
def endVal (c : a.Claim E) (ζ : ℕ → E) (av : ℕ → E) : E :=
  a.mle (a.arrN c.coef) ζ * ∑ j ∈ Finset.range a.code.msg, eqN (a.mu - a.mrow) a.mrow ζ j * av j

variable (E) in
/-- three rounds: θ; the last array in the clear, then the positions; the next array encoded, then
the positions with χ0, χ1, χ' (the coefficients with which the checks at the positions enter the
next claim) -/
abbrev rTheta : Round := plainRound Unit (Fin a.rows → E) ()
variable (E) in
abbrev rLast : Round :=
  plainRound ((Fin a.code.msg → E) × (Fin a.code.msg → E))
    (Fin a.q → Fin a.code.n) (fun _ => 0, fun _ => 0)
variable (E) in
abbrev rNext (b : Lev2 F) : Round :=
  wordsRound Unit (fun _ => b.code.n) (fun _ => Fin b.rows → E) Unit
    ((Fin a.q → Fin a.code.n) × E × E × (Fin a.q → E)) (fun _ _ => 0) ()

/-- The claim of the next level on an array that holds (A' ‖ A'') as one sequence. (`ch` is the
verifier's message of `rNext`: `ch.1`: the positions; `ch.2.1`: χ0, at `foldW`; `ch.2.2.1`: χ1, at
`combW`; `ch.2.2.2`: χ'.) -/
def nextClaim (b : Lev2 F) (c : a.Claim E) (w : a.Word E) (ζ s0 s2 : ℕ → E) (θ : Fin a.rows → E)
    (ch : (Fin a.q → Fin a.code.n) × E × E × (Fin a.q → E)) : b.Claim E where
  coef := b.ofFlat fun t =>
    if t < a.code.msg then
      a.mle (a.arrN c.coef) ζ * eqN (a.mu - a.mrow) a.mrow ζ t +
        ∑ i, ch.2.2.2 i * (ch.2.1 * nat (fun s => a.code.GE E (ch.1 i) s) t)
    else if t < 2 * a.code.msg then
      ∑ i, ch.2.2.2 i * (ch.2.2.1 * nat (fun s => a.code.GE E (ch.1 i) s) (t - a.code.msg))
    else 0
  v := a.clEnd c.v ζ s0 s2 +
    ∑ i, ch.2.2.2 i * (ch.2.1 * a.foldW w ζ (ch.1 i) + ch.2.2.1 * a.combW w θ (ch.1 i))

/-- the next array of the honest prover -/
def nextArr (b : Lev2 F) (A : a.Arr E) (ζ : ℕ → E) (θ : Fin a.rows → E) : b.Arr E :=
  b.ofFlat fun t =>
    if t < a.code.msg then nat (a.foldA A ζ) t else nat (a.combA A θ) (t - a.code.msg)

end Lev2

variable {F : Type} [Field F] (E : Type) [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

/-- The shape of the levels: the present array has the format a, the later ones those of the list;
the array after the last is sent in the clear. -/
def levels2Shape : Lev2 F → List (Lev2 F) → Shape
  | a, [] => List.replicate a.mu (LinSh.rSC E) ++ [a.rTheta E, a.rLast E]
  | a, b :: rest =>
    List.replicate a.mu (LinSh.rSC E) ++ (a.rTheta E :: a.rNext E b :: levels2Shape b rest)

end Blocks
