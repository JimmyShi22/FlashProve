-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Head/AtZ.lean: FIVE LETTERS OF THE OUTPUT HEAD's LAYER AS CLOSED TERMS OFF THE
PROOF FILE's PUBLIC PART Z : ProofFile.Pub (Johnson/Desc/ProofFile/Pub.lean), X := Z.p.X: for the composed
meaning's structure of letters. Definitions and nothing else, on light imports.
  hShapeAt Z: the head's public numbers: X.hS.
  iU3At Z: the number of the head's array of the reads: what X's plan names as its third array of
      that list, 0 if it names none: the text of Law/RowRides.lean's readsOf at X.
  sizesAt Z · policyAt Z: the two classes, of hShapeAt Z: the fields sizes and policy of
      Stored/HeadSeatAt.lean's parOf.
  rqAt Z p: the request that the words of p.request spell, p : ProofFile.InstPub: Stored/HeadSeatAt.lean's
      requestOf at Z's state before the first segment with these words laid. It reads the words
      alone.
WHAT IT DOES NOT SAY. Nothing by itself. That Z is any road's value; that X's plan names an array of
reads (then iU3At Z is a default); that the words pass any test (rqAt is bare: no test on their
count, on the tokens or on r < e ≤ T). What ties the five to the block, the seat and the laws:
Law/AtZLaw.lean. X.hS IS NO NUMERAL: in the goals' scope six of its numbers are free
(by report).

-/
import Johnson.Desc.ProofFile.Pub
import Johnson.Stored.HeadSeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.AtZ

open VerifiableInference.Desc.First (S)

/-- The head's public numbers. -/
def hShapeAt (Z : ProofFile.Pub) : OnBytes.Model.Head.Shape := Z.p.X.hS

/-- The number of the head's array of the reads; 0 if the plan names none. -/
def iU3At (Z : ProofFile.Pub) : Nat := (Z.p.X.H.tl.ix.U.getD 2 none).getD 0

/-- The sizes. -/
@[reducible] def sizesAt (Z : ProofFile.Pub) : Sizes := sizesOf (hShapeAt Z)

/-- The policy. -/
@[reducible] def policyAt (Z : ProofFile.Pub) : Policy := (parOf (hShapeAt Z) 0).policy

/-- The request that the words of p.request spell. -/
@[reducible] def rqAt (Z : ProofFile.Pub) (p : ProofFile.InstPub) : Request :=
  requestOf (Z.s₀.withReq (OnBytes.Model.Verify.words32 p.request))

end VerifiableInference.Desc.Kinds.Head.AtZ
