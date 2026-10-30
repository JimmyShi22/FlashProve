-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Pending.lean: the equation on the committed matrix that a sub-proof with claims on the
weights leaves to be tested.

It follows the C++ verifier's header verifier/src/vf_weights_pending_claim.h. WsPending and
wsPending have the names of their C++ counterparts. wsSpan is the first loop of the C++
wsPending.

In the sub-proof's merge (OnBytes/Model/Merge.lean) the prover has sent a value fv' and says that
it is fv + beta c. Nothing in the sub-proof tests this. Here c is the sub-proof's entry of the
request's index-mask message (explained at memberPendingRow, OnBytes/Iop/Lin.lean), and
fv = < Gamma (x) eq(rm, .), W >: Gamma is the vector of row weights, that is, of the coefficients on
the rows of the committed matrix W that the claims add up to (they are not weights of the model),
and rm is the merge's point on the columns.
Gamma (x) eq(rm, .) stands for the matrix of all products of a row's weight and a column's weight,
and < A, W > for the sum of the products of the entries of A and W. What is left to be tested is the
equation
    < Gamma (x) eq(rm, .), W > + beta c = fv'.
This file calls that equation the pending row. It is one row of the list of equations that the test
on the matrix (OnBytes/Iop/Lin.lean) takes. Every other "row" below is a row of W.
Gamma is passed on for the stretch of rows of W that the claims' units span, and for no other row.
wsPending forms it from row 0 to the end of that stretch and then cuts the stretch out.
The test on the matrix takes row weights as a sum of vectors of product form. memberWeightsOnRows
in OnBytes/Iop/Lin.lean cuts the stretch into such vectors.

Main definitions: WsPending, wsSpan, wsPending.

What this file does not do: it reads no message and tests no equation of a proof. It does not take
the mask entry c. The caller takes c from the index-mask message and makes the pending row with
memberPendingRow. No theorem is stated here.
-/
import OnBytes.Model.Merge
import OnBytes.Iop.Lin

namespace OnBytes.Model

/-- All of the pending row but the mask entry, which the caller takes from the index-mask message.
C++: WsPending. -/
structure WsPending where
  /-- the row weights are the sum of these vectors -/
  g : List Tensor
  /-- the point on the columns, the coordinate of column bit 0 first -/
  psi : List E
  /-- the factor of the mask entry -/
  beta : E
  /-- the equation's right side, fv' -/
  target : E
  deriving Inhabited

/-- The first row of the units that the claims name, and the row after their last. A claim on a
unit that is not in the layout is refused. An empty list gives (2^64 - 1, 0); wsPending refuses an
empty list before it calls this function. -/
def wsSpan (lay : WsLay) (recs : List WsRecClaim) : Except String (Nat × Nat) :=
  recs.foldlM
    (fun (r : Nat × Nat) c =>
      match lay.U[c.ui]? with
      | none => throw "internal-gamma-rows"
      | some u => pure (min r.1 u.off, max r.2 (u.off + u.rows)))
    (2 ^ 64 - 1, 0)

/-- The pending row of a sub-proof, from what wsForkEnd has returned.
claims: the number of claims in the plan, which follows from the parameter file. S: the shape of
the test on the matrix. That test ignores row weights after its matrix's last row, so the layout
from which the weights are made must have exactly as many rows as that matrix.
C++: wsPending. -/
def wsPending (lay : WsLay) (o : WsForkOut) (claims : Nat) (S : Params.LinShape) :
    Except String WsPending := do
  let rowBits := S.kRow
  if lay.m0 != S.matrixRows then throw "internal-gamma-rows"
  if o.recs.isEmpty || o.recs.length != claims || o.rm.size != lay.lk then
    throw "link-claim-count"
  let (first, last) ← wsSpan lay o.recs
  if last ≤ first || lay.m0 < last || 62 < rowBits || 2 ^ rowBits < lay.m0 then
    throw "internal-gamma-rows"
  let Gam ← o.recs.foldlM (fun G c => wsGammaAdd G lay c oneE) (Array.replicate last zeroE)
  match memberWeightsOnRows S first (Gam.extract first last) with
  -- The tests above give the sizes that memberWeightsOnRows asks. Its last test, that the blocks
  -- cover the stretch, holds by the count at stretchInTheCube. No theorem shows the branch dead.
  | none => throw "internal-gamma-rows"
  | some g => pure { g := g, psi := o.rm.toList.reverse, beta := o.beta, target := o.fvp }

/-- The names under which the functions of this file refuse. -/
def Pending.names : List String := ["internal-gamma-rows", "link-claim-count"]

end OnBytes.Model
