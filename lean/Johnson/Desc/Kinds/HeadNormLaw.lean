-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/HeadNormLaw.lean.
WHAT IS NOT HERE. OF THE NORMALIZATION's 29 FORMS THIS LEMMA SPEAKS OF 17. The other twelve (three
sumchecks' own forms; the ties of their end values to reads; the two batched sums) carry a claim
from a drawn point to the corners: a reduction with chance in it, of the sort of HeadLaw.lean's
Lemma 2b: not stated here. TWO STEPS MORE STAND BETWEEN A VERIFIER's YES AND THIS RELATION, AND ARE
NONE OF THE TWELVE: that each of the 17 forms at a point is the sum of its corner values under the
equality weights, and that a form which is 0 at the drawn point pV is 0 at every corner but for few
points: both are proved in Law/NormPoint.lean (rd_rowsAt, rows_bridge), not stated here. That
CellRelN can be met, by the honest cells of every stream on which the integer program goes on, is
proved in Law/NormHonest.lean; THAT IT CAN BE MET TOGETHER WITH THE HEAD's OWN RELATION IS SHOWN BY
NO THEOREM. That a read is the sum of its cells, that a key is a row of its table, that a cell is
small: other blocks' laws. Nothing on what a proof hides.
WHAT IT IS. THE OUTPUT HEAD's LAW, THE FINAL NORMALIZATION's HALF: ITS DETERMINISTIC LEMMA, STATED
HERE; the proof stands in Law/NormProof.lean. Definitions with code and two `def ... : Prop`; no
theorem in this file. It goes on from HeadLaw.lean, in that file's way: the kind's own forms
(Norm.lean, HeadNorm.lean, and beneath them the part P6/NormRow.lean) take all that they read
through classes; here the classes are filled from INTEGER CELLS and a point; a form so made has no
variable left, and its value is its constant. No formula of a form is written a second time: also
the row's fields, where a hidden product or the reciprocal is laid "in truth", are the part's own
Row.ofDigits on the position's digits.

LEMMA 1-N (`Lemma1NStatement`): no chance in it. Under the tests on the plan: the relation on cells
(`CellRelN`) gives, in integers, at every position: act is the final normalization of the stream:
sum of squares, integer root, reciprocal, rounding, clamp to -2047 .. 2047 (`SaysN`).
LEMMA 1, WHOLE (`Lemma1WholeStatement`): with HeadLaw.lean's relation on the head's cells beside it:
that file's (a), (b), (c) and the normalization together; the condition on the activations falls.
THE RELATION ON CELLS: every cell is small; at each position t the row's 17 linear forms (nine
carries, the root's four, the reciprocal's four: Norm.rowForms) are 0 AT THE CORNER of t, with the
nine sums of limb products and the seven products of the row's fields in truth; the four keys at the
corner of entry x and position t lie in their tables: 16 bits, 16 bits, a row of the clamp's table,
8 bits (this last key runs over the head's 21 digits too).

EVERY INTEGER LETTER THAT IS LAID INTO THE FIELD, AND WHAT BOUNDS IT (a reading): a cell: small; n
in InBits, u in IsClampRow: by their definitions; MF, KF, epsF, d, T: the tests on the plan. The
sums of limb products and the products of fields are made of small cells. EVERY = ON FIELD ELEMENTS:
"v = 0" and "x = (n : E)" compare an output of the field's operations with the image of a bounded
natural; that such outputs are written in the one canonical way is proved where it is used
(Law/NormPoint.lean: okE_rowsAt; Law/NormHonest.lean: okE_keyNAt, okE_natE).

-/
import Johnson.Desc.Kinds.HeadLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Desc.First (P6.Row P6.Row.ofDigits P6.rowProducts)
open Norm (lt ls d lPd T S2)
open FinalNorm (MF KF epsF)

/-! ## 1. The cells, and the classes filled from them -/

/-- The head's cells, and the stream's: (feature, position); limb l of feature k lies at feature
l d + k. -/
structure NCells extends Cells where
  stream : Nat → Nat → Int

/-- A cell of one of the three matrices that the normalization reads. -/
def NCells.of (c : NCells) : FinalNorm.Matrix → Nat → Nat → Int
  | .stream => c.stream
  | .act => c.cell .act
  | .row => c.cell .row

/-- What comes in from the lookup, as in HeadLaw.lean's Pt, for the normalization's four keys. -/
structure NPt where
  (zt zl : Point)
  ewh : FinalNorm.Key → Nat → E

variable [Sizes]

/-- The corner of entry x and position t. -/
def cornerN (x t : Nat) : NPt :=
  { zt := bits lt t, zl := bits ls (x % S2), ewh := fun _ i => if i == x / S2 then 1 else 0 }

/-- How many entries a key has: a feature each; the last: a digit each, the head's 21 among them. -/
def lenN : FinalNorm.Key → Nat
  | .digits => NR + 21
  | _ => d

/-- The weight of entry x of key k: its block's, times the equality weight inside the block. -/
def NPt.ew (p : NPt) (k : FinalNorm.Key) (x : Nat) : E := p.ewh k (x / S2) * eq p.zl (x % S2)

/-- The class, as HeadNorm.lean's In says what each field is. -/
@[reducible] def NPt.normIn (p : NPt) : FinalNorm.In :=
  { zt := p.zt, zl := p.zl, ew := p.ew, ewh := p.ewh, wsum := fun k => ∑ x < lenN k, p.ew k x }

/-- Limb l of feature k of the stream at position t; the feature's value. -/
def limbZ (c : NCells) (t l k : Nat) : Int := c.stream (l * d + k) t
def str (c : NCells) (t k : Nat) : Int := sumZ 5 fun l => 256 ^ l * limbZ c t l k

/-- Digit j of position t's row: a cell holds its digit less 128. -/
def digZ (c : NCells) (t j : Nat) : Int := c.cell .row j t + 128

/-- The sum of limb products number s at position t. -/
def wsqZ (c : NCells) (t s : Nat) : Int :=
  sumZ d fun k => sumZ 5 fun l => sumZ 5 fun l' =>
    if l + l' = s then limbZ c t l k * limbZ c t l' k else 0

/-- Position t's row, by the part's own function on the position's digits. -/
def rowZ (c : NCells) (t : Nat) : P6.Row :=
  P6.Row.ofDigits fun j => ((ofInt (digZ c t j) : E) : Form)

/-- The four fields a, b, Rlo, Rhi by their places 0 to 3; product number n of the part's list. -/
def fieldE (c : NCells) (t : Nat) : Nat → E
  | 0 => (rowZ c t).a.const
  | 1 => (rowZ c t).b.const
  | 2 => (rowZ c t).Rlo.const
  | _ => (rowZ c t).Rhi.const
def prodE (c : NCells) (t n : Nat) : E :=
  fieldE c t (P6.rowProducts.getD n (0, 0)).1 * fieldE c t (P6.rowProducts.getD n (0, 0)).2

/-- Entry i of a read, in truth: the sum of its cells under its weights. -/
def readAtN (c : NCells) (x : FinalNorm.Matrix × Weights) (i : Nat) : E :=
  match x.2 with
  | .long f g => ∑ j < S2, ∑ t < T, f j * g t * ofInt (c.of x.1 (S2 * i + j) t)
  | .short g => ∑ t < T, g t * ofInt (c.of x.1 i t)

/-- What the part has heard, in truth, as far as the row's 17 forms read it: the point on the
positions; the nine sums; the seven products. -/
@[reducible] def normHeardAt (c : NCells) (pV : Point) : Norm.Heard :=
  { pV, gam := 0, rhoI := #[], squares := {}, om := 0, products := {}
    W := ((List.range 9).map fun s =>
      ({ var := ((∑ t < T, eq pV t * ofInt (wsqZ c t s) : E) : Form) } : Hid)).toArray
    P := ((List.range 7).map fun n =>
      ({ var := ((∑ t < T, eq pV t * prodE c t n : E) : Form) } : Hid)).toArray }

section At
variable [FinalNorm.In]

/-- The claimed sum of the sumcheck normed, in truth: the stream times the reciprocal, under the
weights of the key remLow, at the lookup's point on the positions. -/
def trueNormed (c : NCells) : E :=
  ∑ t < T, ∑ x < d,
    eq FinalNorm.zt t * FinalNorm.ew .remLow x * (ofInt (str c t x) * (rowZ c t).R.const)

@[reducible] def finalHeardAt (c : NCells) : FinalNorm.Heard :=
  { normed := { claimed := { var := ((trueNormed c : E) : Form) } } }

/-- The reads, in truth: constant forms. wide: the head's read of its wide matrix at (zl, zt). -/
@[reducible] def normReadsAtCells (c : NCells) [Norm.Heard] [FinalNorm.Heard] : FinalNorm.Reads :=
  { entry := fun r i => ((readAtN c r.of i : E) : Form)
    wide := fun i => ((∑ j < S2, ∑ t < T,
      eq FinalNorm.zl j * eq FinalNorm.zt t * ofInt (c.cell .wide (S2 * i + j) t) : E) : Form) }

end At

/-- The row's 17 forms at the cells and a point on the positions: their constants. -/
def rowsAt (c : NCells) (pV : Point) : List E :=
  let _ := (cornerN 0 0).normIn
  let _ := normHeardAt c pV
  let _ := finalHeardAt c
  let _ := normReadsAtCells c
  Norm.rowForms.map (·.const)

/-- A key of the normalization at the cells and a point: its constant. -/
def keyNAt (c : NCells) (p : NPt) (k : FinalNorm.Key) : E :=
  let _ := p.normIn
  let _ := normHeardAt c p.zt
  let _ := finalHeardAt c
  let _ := normReadsAtCells c
  (FinalNorm.key 21 k).const

/-! ## 2. The relation on cells -/

/-- An integer clamped to -2047 .. 2047. -/
def clampZ (a : Int) : Int := min (max a (-2047)) 2047

/-- A row of the clamp's table: u with the clamp of u - 2^15, moved up by 2^11. -/
def IsClampRow (x : E) : Prop :=
  ∃ u : Nat, u < 2 ^ 16 ∧
    x = ((u + 2 ^ 28 * (clampZ ((u : Int) - 2 ^ 15) + 2 ^ 11).toNat : Nat) : E)

/-- THE RELATION: what the lookup, the range check and the one tested equation are meant to leave of
the normalization's cells, entry by entry and position by position. -/
structure CellRelN (c : NCells) : Prop where
  small : ∀ m f t, (c.cell m f t).natAbs < 2 ^ 18
  smallS : ∀ f t, (c.stream f t).natAbs < 2 ^ 18
  rows : ∀ t, t < T → ∀ v, v ∈ rowsAt c (bits lt t) → v = 0
  remLow : ∀ t, t < T → ∀ x, x < d → InBits 16 (keyNAt c (cornerN x t) .remLow)
  remHigh : ∀ t, t < T → ∀ x, x < d → InBits 16 (keyNAt c (cornerN x t) .remHigh)
  clamp : ∀ t, t < T → ∀ x, x < d → IsClampRow (keyNAt c (cornerN x t) .clamp)
  /-- all NR + 21 entries of the key: the normalization's 99 digits and the head's 21 -/
  digits : ∀ t, t < T → ∀ j, j < NR + 21 → InBits 8 (keyNAt c (cornerN j t) .digits)

/-! ## 3. What it says, in integers (HeadNorm.lean's and Norm.lean's heads) -/

/-- The sum of the stream's squares at position t. -/
def vsq (c : NCells) (t : Nat) : Int := sumZ d fun k => str c t k * str c t k

/-- At every position: sig is the integer root of Vsq + epsF; R the rounded reciprocal; act the
rounded product, clamped. And the integer program's two conditions for going on hold: Vsq + epsF is
below 2^78, and every rounded product fits 16 bits. `/` on integers rounds down here: every divisor
is positive. -/
def SaysN (c : NCells) : Prop :=
  ∀ t, t < T → ∃ sig : Int, 1 ≤ sig ∧ sig * sig ≤ vsq c t + epsF ∧
    vsq c t + epsF < (sig + 1) * (sig + 1) ∧ vsq c t + epsF < 2 ^ 78 ∧
    ∀ k, k < d → ∃ aw : Int,
      aw = (str c t k * ((2 ^ MF + sig / 2) / sig) + 2 ^ (KF - 1)) / 2 ^ KF ∧
      -2 ^ 15 ≤ aw ∧ aw < 2 ^ 15 ∧ act c.toCells t k = clampZ aw

/-! ## 4. The statement -/

/-- **LEMMA 1-N**: from the relation on cells to the final normalization. No chance in it. -/
def Lemma1NStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] (sT : Nat) (c : NCells),
    planOk sT = true → CellRelN c → SaysN c

/-- HeadLaw.lean's relation on the head's cells WITHOUT ITS CLAUSES small AND bytes: both are
clauses of CellRelN or follow from it: that the head's 21 digits are bytes is the key digits at its
entries from NR on. Every other clause is that structure's, to the letter. -/
structure CellRelH [Policy] [Request] [Token] (c : Cells) (tab : Nat → Nat) : Prop where
  top : ∀ t, t < T → ∀ x, x < JV → InBits 16 (keyAt c (corner x t) .marginTop)
  mid : ∀ t, t < T → ∀ x, x < JV → InBits 16 (keyAt c (corner x t) .marginMid)
  low : ∀ t, t < T → ∀ x, x < JV → InBits 8 (keyAt c (corner x t) .marginLow)
  rowA : ∀ t, t < T → ∀ x, x < len .tableA → IsRow tab (keyAt c (corner x t) .tableA)
  rowB : ∀ t, t < T → ∀ x, x < len .tableB → IsRow tab (keyAt c (corner x t) .tableB)
  lines : ∀ t, t < T → clipAt c (corner 0 t) = 0 ∧ tableAt c (corner 0 t) = 0
  sums : meanAt c = 0 ∧ countAt c = 0

/-- **LEMMA 1, WHOLE**: both halves together: HeadLaw.lean's Lemma 1 WITHOUT ITS CONDITION ON THE
ACTIVATIONS: that they are at most 2047 is now a consequence. From the two relations on cells to the
claim under the policy, about logits of activations that are the final normalization of the stream
that the cells hold. No chance in it. -/
def Lemma1WholeStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] (sT : Nat) (tab : Nat → Nat) (c : NCells),
    planOk sT = true → Request.ok = true → y < V → TableOk tab →
    (∀ k v, (c.Wh k v).natAbs ≤ 2 ^ 12) →
    CellRelH c.toCells tab → CellRelN c → Says c.toCells ∧ SaysN c

end VerifiableInference.Desc.Kinds.Head.Law
