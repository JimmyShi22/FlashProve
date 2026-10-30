-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Tensors.lean: where a tensor's entry is in a matrix that sub-proofs share, and the
clamp.

A committed matrix has a cell for each pair of a feature and a token. A tensor takes up a run of the
matrix's features. Two sub-proofs may use the same matrix: one commits to it, the other reads it.
Both are meant to find an entry through the functions of this file, so that one formula serves both.
Nothing enforces that they do. The two agree on where an entry is only if they pass the same TenAt.
For the attention sub-proof's four tensors that is tested elsewhere (tensorsAgree,
OnBytes/Model/LayerLayout.lean). The file follows the index routines at the head of
verifier/src/vf_attention_shape.h.

A column of a matrix holds the cells of some neighbouring features, feature after feature, T tokens
each. A block is the rows of 2^ls neighbouring features. A long table is a table of evaluations with
one entry for each block: a sum over the block's rows under public weights. A point for a long table
has the coordinates of the entry and then those of a row in the block: first the low bits of the
feature, then the token.

Main definitions: clamp, clampBound; TenAt, tenCell, headFeat (entries of tensors); blockRow,
blockRows, longPoint, longPhi (blocks); cutLast, lastOf, hiTab (points for long tables);
tensorsNames.

Refusals. A function that can refuse returns a value or the name of the test that failed. The one
name here, plan-tensor-layout, is that of the C++ source as read.

The file reads no proof and holds no theorem.
-/
import OnBytes.Model.Frame

namespace OnBytes.Model

/-! ## The clamp -/

/-- The clamp. Table FC (rowFC, OnBytes/Model/LayerLayout.lean) clamps a value to -clamp .. clamp,
and the lookups in it are meant to keep the entries of the tensors q, k and v in that range. The
table's rows and the bounds in the sub-proofs' shapes (AttentionShape.lean, LayerLayout.lean,
HeadLayout.lean) use this one constant, so that the table and the bounds cannot differ in it. -/
def clamp : Nat := 2047

/-- The least number above every clamped entry: clamp + 1. The no-overflow conditions of the layer
and head sub-proofs use it (OnBytes/Model/LayerLayout.lean, OnBytes/Model/HeadLayout.lean). -/
def clampBound : Nat := clamp + 1

/-! ## Entries of tensors -/

/-- Where a tensor is among the features of a committed matrix: nl limbs, each of cnt layers of
J features, from feature off on. -/
structure TenAt where
  /-- the first feature -/
  off : Nat := 0
  /-- the number of limbs -/
  nl : Nat := 0
  /-- the number of layers -/
  cnt : Nat := 0
  /-- the tensor's own features in one layer -/
  J : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- The number of the matrix's feature that holds limb l of the tensor's entry at layer i and the
tensor's own feature j. -/
def tenCell (X : TenAt) (l i j : Nat) : Nat := X.off + (l * X.cnt + i) * X.J + j

/-- The first of the dh features of attention head hd in a tensor. Refused: dh is 0 or does not
divide J, or the head is past J. -/
def headFeat (X : TenAt) (hd dh : Nat) : Except String Nat :=
  if dh == 0 || X.J % dh != 0 || hd ≥ X.J / dh then .error "plan-tensor-layout"
  else .ok (hd * dh)

/-! ## Blocks and points for long tables -/

/-- The row of a block for token t of the feature whose low bits are c2. T is the number of
tokens. It follows blockRow of the C++ source. The program does not call it: blockRows produces
this order by construction, and OnBytes/Model/TestTensors.lean compares the two. -/
def blockRow (c2 t T : Nat) : Nat := c2 * T + t

/-- A block's weights: the row of (c2, t) gets low[c2] tok[t] (see blockRow). -/
def blockRows (low tok : Array E) : Array E :=
  low.flatMap fun a => tok.map fun b => mulE a b

/-- A block's point: the coordinates of the feature's low bits, then those of the token. low must
hold exactly the ls coordinates of the low bits. -/
def longPoint (low tok : Array E) : Array E := low ++ tok

/-- A block's weights at a point p of ls + lt coordinates. Not tested here: a shorter p gives a
shorter vector, which the smallness test refuses (objectsF, OnBytes/Model/Tail.lean). -/
def longPhi (p : Array E) (ls lt : Nat) : Array E :=
  blockRows (eqTab (p.extract 0 ls)) (eqTab (p.extract ls (ls + lt)))

/-- Splits a point in two: the coordinates before its last k, and its last k. Refused: the point has
fewer than k coordinates. The C++ source also refuses a negative k. Here k is a natural number. A
caller that forms k, or want in hiTab, by a subtraction must know that the difference is not
negative: cut off at 0 it could match an empty part where the C++ refuses. -/
def cutLast (z : Array E) (k : Nat) : Except String (Array E × Array E) :=
  if k > z.size then .error "plan-tensor-layout"
  else .ok (z.extract 0 (z.size - k), z.extract (z.size - k) z.size)

/-- The last k coordinates of a point. Refused as in cutLast. -/
def lastOf (z : Array E) (k : Nat) : Except String (Array E) := do
  pure (← cutLast z k).2

/-- The weights of a long table's entries at a whole point, that is a point with the coordinates of
the entry and then the la coordinates of the block's row: eq of the coordinates before the last la
with every index. Refused unless there are exactly want of these coordinates. -/
def hiTab (z : Array E) (la want : Nat) : Except String (Array E) := do
  let c ← cutLast z la
  if c.1.size != want then .error "plan-tensor-layout" else .ok (eqTab c.1)

/-- The names under which this file refuses. -/
def tensorsNames : List String := ["plan-tensor-layout"]

end OnBytes.Model
