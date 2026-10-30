-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Top/BatchVQueriesN.lean: bounds on the queries to the one oracle f of the three verifiers that the
  compiled scheme runs, where f is queried only for marked blocks. The bounds are for every wire
  record and every query encoding with `Need.Std`. The file also has the part of the openings, as a
  number (`opensOf`).

  The step to one hash function of Rom/OverOneN.lean queries f, at a typed query, only for the
  marked blocks of the answer. With the table of Compile/Batch/NeedTable.lean (`needOf`) these are,
  at a Fiat-Shamir query of round i of protocol t, the blocks below nb t i and the chaining value
  (number K).
    Part 1 every wire record W, every query encoding m that cuts answers in the standard way
            (`Need.Std`), every nb. `queryBound_vTSN`, `queryBound_vLSN`, `queryBound_vBSN`: the
            three verifiers, on any inputs.
    Part 2 the part of the openings only, as a number computed from `L`, its `IsPoint` records and
            `no`; no wire record is named here (Top/BatchVQueriesDraw.lean ties it to
            `QueryLayout.ofDraws`). `opensOf`, `opensOf_le`.

  (Terms: lean/GLOSSARY.md.)

  Limits: No bound for the verifier of the scheme as one algorithm, and none for the Fiat-Shamir
  chains at the generic wire record.
  That the scheme in which only marked blocks are queried has the same output distributions as the
  scheme in which every block is queried needs `QueryLayout.NB W nb` and is not in this file (see the head
  of Rom/OverOneN.lean, "What is proved and what is not").
  Nothing on C and P. The bounds count queries to f, each as one, however long its string is; they
  say nothing of V's work in the fields.
-/
import Top.BatchSizesGen
import Compile.Batch.NeedCost
import Blocks.ChalSum

set_option autoImplicit false

noncomputable section

namespace Top.Batch
open Iop Rom Compile Compile.Batch Compile.Batch.Need Blocks
open Compile.Need (sumNb)

/-! ## Part 1. Every wire record, every query encoding with `Need.Std`, every nb -/

section Any
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (nb : Tag → ℕ → ℕ)
  {m : OracleCoding (spec lam W.K L) lam} (hm : Need.Std m)
include hm

/-- The verifier of Test, only marked blocks queried. -/
theorem queryBound_vTSN (sMT sFS : ℕ) (cm : Dig lam) (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline)) :
    ((vTS W sMT sFS cm π).overOneN m (needOf nb m)).QueryBound (cVQLN (nb .test) W.T) :=
  queryBound_overOneN m (needOf nb m) _ _ (cn_vTS W nb hm sMT sFS cm π)

/-- The verifier of Link, likewise. -/
theorem queryBound_vLSN (sMT sFS : ℕ) (cm cm' : Dig lam)
    (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)) :
    ((vLS W sMT sFS cm cm' π).overOneN m (needOf nb m)).QueryBound (cVQLN (nb .link) W.Lk) :=
  queryBound_overOneN m (needOf nb m) _ _ (cn_vLS W nb hm sMT sFS cm cm' π)

/-- The verifier of one slot of Batch, likewise. -/
theorem queryBound_vBSN (sMT sFS : ℕ) (cm : Dig lam) (x : X) (π : OneProtocolProof lam L.onlineBatch) :
    ((vBS W sMT sFS cm x π).overOneN m (needOf nb m)).QueryBound (cVQBN (nb .onl) W.B W.depthReq) :=
  queryBound_overOneN m (needOf nb m) _ _ (cn_vBS W nb hm sMT sFS cm x π)

end Any

/-! ## Part 2. The part of the openings -/



section Gen
variable {I X : Type} (lam : ℕ) (L : BatchProtocol I X) (pT : L.offline.shape.IsPoint)
  (pL : L.link.shape.IsPoint) (pB : L.onlineBatch.loc.shape.IsPoint) (z : L.Symbol) (no : OpenNums)
  (ax : L.Aux pT pL pB) (p : Params) (D : SerLHB L)

/-- The part of the openings. Each position that a wire record announces as opened is counted with a
leaf and a path in a tree of the largest depth of its protocol, the tree over an encoded index
included. `no` has the numbers of these positions, own and external positions together. -/
def opensOf (L : BatchProtocol I X) (pT : L.offline.shape.IsPoint) (pL : L.link.shape.IsPoint)
    (pB : L.onlineBatch.loc.shape.IsPoint) (no : OpenNums) : ℕ :=
  no.T * (max (Nat.clog 2 L.wordLength) (depths L.offline.shape pT) + 1) +
    no.L * (max (Nat.clog 2 L.wordLength) (depths L.link.shape pL) + 1) +
    no.O * (max (Nat.clog 2 L.wordLength) (depths L.onlineBatch.loc.shape pB) + 1)

omit lam z ax p D in
/-- Under the hypotheses below: `opensOf` ≤ N, from bounds for the depths. -/
theorem opensOf_le {dT dL dO N : ℕ} (hI : Nat.clog 2 L.wordLength ≤ min dT (min dL dO))
    (hT : depths L.offline.shape pT ≤ dT) (hL : depths L.link.shape pL ≤ dL)
    (hO : depths L.onlineBatch.loc.shape pB ≤ dO)
    (hN : no.T * (dT + 1) + no.L * (dL + 1) + no.O * (dO + 1) ≤ N) : opensOf L pT pL pB no ≤ N := by
  have hI1 := le_trans hI (min_le_left _ _)
  have hI2 := le_trans hI (le_trans (min_le_right _ _) (min_le_left _ _))
  have hI3 := le_trans hI (le_trans (min_le_right _ _) (min_le_right _ _))
  exact le_trans
    (Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.add_le_add_right (max_le hI1 hT) 1))
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (max_le hI2 hL) 1)))
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right (max_le hI3 hO) 1))) hN




/-! the three compiled verifiers one by one, from bounds for their parts: nothing is stated here -/



end Gen

end Top.Batch
