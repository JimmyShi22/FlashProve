-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/Batt.lean: several linear claims on the committed matrix become one.
C++ counterpart: blocks/iop/batt.h (batt_verify, batt_claim, batt_row).

The committed matrix M has 2^kCol columns. It is never sent. A row on it (`TensorRow`) is the claim
  < g (x) eq(psi, .), M >  +  (a linear form in mask entries)  =  target,
where g weighs the rows of M and eq(psi, .) is the equality vector at the column point psi.

The block takes J such rows, each at a column point of its own, and hands on one row at a fresh
column point. The verifier draws one element x. Row j gets the coefficient x^j. Then the
zero-knowledge sumcheck (OnBytes/Iop/Psc.lean) runs over the kCol column variables on
  sum over the columns c of  sum_j x^j eq(psi_j, c) W_j(c),   W_j = g_j^T M.
The summand is affine in the maps W_j: no map's value is shown, so it has no further variable Y.
The row that the sumcheck hands on names W_j at the point of challenges, and that is again a row
on the matrix: its weights are the sum of a_j g_j with a_j = eps x^j eq(psi_j, point).

No test on a value is made here: what can fail in `verify` (the rows' form and number, the plan's
entries, the ledger, the sumcheck's sizes) does not depend on a value. The protocol's argument is
that a false row among the J, or a sumcheck on other vectors than the W_j, makes the row that is
handed on false, except with the rounds' errors. The test on the committed table reads that row
later.

The block is written once, in the type Blk of OnBytes/Iop/Ground.lean. Its dry run gives its
rounds: BAT-sigma, PSC epsilon, and kCol times PSC round. Its run on a view gives its part of the
decision.

Main definitions: `TensorRow`, `Batt.masksOf`, `Batt.claimOf`, `Batt.summandOf`, `Batt.rowOf`,
`Batt.verify`.

Not claimed here: soundness or hiding. Order, the caller's duty: everything that enters a row (its
weights, its column point, its target, which mask entries it holds) must be fixed before x is drawn.
A prover that may name a target after x could let two false rows cancel.
-/
import OnBytes.Iop.Psc
import OnBytes.Field.Mle
import OnBytes.Chain.Lists

namespace OnBytes

/-- A row on the committed matrix M:
< g (x) eq(psi, .), M > + (the mask form) = target. -/
structure TensorRow where
  /-- the weights of the rows of M are the sum of these vectors -/
  g : List Tensor
  /-- the column point: one coordinate for each bit of a column's number, the lowest first -/
  psi : List E
  /-- the mask form -/
  masks : MaskForm
  /-- the target -/
  target : E
  deriving Inhabited

namespace Batt

/-- The number of mask entries that one run takes. It is also the number of elements sent. -/
def masksOf (kCol : Nat) : Nat := 1 + 2 * kCol

/-! ## The claim and the row -/

/-- The rows have an allowed form: there is a row; the matrix has more than one column; every column
point has kCol coordinates; each row has weights; all weights have the same number of variables. -/
def fits (kCol : Nat) (rows : List TensorRow) : Bool :=
  match rows with
  | [] => false
  | r :: _ =>
    decide (1 ≤ kCol) &&
    rows.all fun s =>
      s.psi.length == kCol && !s.g.isEmpty &&
      s.g.all fun t => some t.vars == r.g.head?.map Tensor.vars

/-- The coefficients of the rows: 1, x, x^2 and so on. -/
def chiOf (rows : List TensorRow) (x : E) : List E := Psc.powers oneE x rows.length

/-- The claim of the sumcheck once x is drawn. The rows' mask forms move into it. -/
def claimOf (rows : List TensorRow) (x : E) : Psc.Claim where
  vars := List.replicate ((rows.head?.map (·.psi.length)).getD 0) (Psc.Weight.plain 3)
  masks := (zipT (chiOf rows x) rows).flatMap fun p => Psc.scaleForm p.1 p.2.masks
  target := (zipT (chiOf rows x) rows).foldl (fun t p => addE t (mulE p.1 p.2.target)) zeroE

/-- The summand once x is drawn: no constant; the map W_j has the coefficient
x^j eq(psi_j, point). -/
def summandOf (rows : List TensorRow) (x : E) : Psc.Summand where
  shown := 0
  kept := rows.length
  degree := 0
  coeffs := fun point _ =>
    zeroE :: (zipT (chiOf rows x) rows).map fun p => mulE p.1 (eqEval p.2.psi point)

/-- The row that is handed on, from the rows that came in and what the sumcheck hands on. The
sumcheck's coefficients belong to the rows in their order; `verify` tests that there is one for
each row. -/
def rowOf (rows : List TensorRow) (o : Psc.Out) : TensorRow where
  g := (zipT rows o.rowMaps).flatMap fun p => p.1.g.map fun t => t.scale p.2
  psi := o.point
  masks := o.rowMasks
  target := o.rowTarget

/-! ## The block -/

/-- The verifier's part in one run on a matrix of 2^kCol columns. ledger: the number of the oracle
message whose mask rows give the `masksOf kCol` mask entries. Returns the one row. -/
def verify (kCol : Nat) (rows : List TensorRow) (ledger : Nat) : Blk TensorRow := do
  Blk.must (fits kCol rows)
  let x ← Blk.closeOne "BAT-sigma"
  Blk.requireRows rows.length
  let fresh ← takeSlots ledger (masksOf kCol)
  let o ← Psc.verify (claimOf rows x) (summandOf rows x) fresh
  Blk.must (o.rowMaps.length == rows.length)
  pure (rowOf rows o)

end Batt

end OnBytes
