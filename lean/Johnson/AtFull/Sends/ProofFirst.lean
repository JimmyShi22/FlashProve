-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Sends/ProofFirst.lean: THE HEAD's EXAMPLE: THE SENDINGS OF THE PROOF FILE's FIRST
CHAIN (48,293 rounds; 82 sendings) AT THE WRITTEN PARTS, AS A VALUE: sendsFrom's inner routine
returns the written chain. ONE CLOSED FACT BY LEAN's KERNEL, AT THE TWIN THAT WALKS THE RUNS ONCE
(Johnson/AtFull/Sends/OneOfRuns.lean): the rounds are never laid out.

  `isB r C`: r returns, and what it returns is the chain C (`sameChain`,
    Johnson/Desc/Ok/PlanWritten/SendsTest.lean).
  `p0B`: the closed fact (its control, which comes out false, stands in ProofFirstNo.lean: one
  kernel fact a file).
  **`p0_W`**: ∃ w2, wSend W.sized.proof.batch.shape = .ok w2 ∧ oneOf "proof" 0 W.sized.proof.codes
  (frameSends … ++ [w2]) proofThree.A.plan = .ok proofSendsFull.1: the ledger's a₃ and b₄
  (sendsFrom_of_parts).

Limits. At the written parts W := writtenMade.at Hung.none alone. Nothing on soundness.

-/
import Johnson.AtFull.Sends.OneOfRuns
import Johnson.Goal.Written.Made
import Johnson.Desc.Ok.PlanWritten.SendsTestLaws

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Sends

open VerifiableInference.PlanWritten VerifiableInference.PlanWritten.Joined Johnson.G
  Johnson.G.MadeFree
open OnBytes OnBytes.Params
open Johnson.G.Runs (valRuns)

/-- The written parts, joined, with nothing hung on. -/
def W : Configured := writtenMade.at Hung.none

/-- It returns, and the chain is the written one. -/
def isB (r : Except String ChainSends) (C : ChainSends) : Bool :=
  match r with
  | .ok a => sameChain a C
  | .error _ => false

theorem isB_ok {r : Except String ChainSends} {C : ChainSends} (h : isB r C = true) : r = .ok C :=
by
  cases r with
  | error e => exact nomatch h
  | ok a => exact congrArg Except.ok (sameChain_eq h)

/-- The first chain's sendings, made along the runs. -/
def p0R : Except String ChainSends :=
  (wSend W.sized.proof.batch.shape).bind fun w2 =>
    oneOfN "proof" 0 W.sized.proof.codes
      (frameSends W.sized.proof W.sized.set.samples 0 (reqGroups W.sized.proof.request).toList
        W.sized.proof.request.link ++ [w2])
      (valRuns VerifiableInference.Number.ByRuns.proofThree.A.recs
        VerifiableInference.Number.ByRuns.proofThree.A.runs)

theorem p0B : isB p0R proofSendsFull.1 = true := by decide +kernel

/-- **The ledger's a₃ and b₄ at the written parts.** -/
theorem p0_W : ∃ w2, wSend W.sized.proof.batch.shape = .ok w2 ∧
    oneOf "proof" 0 W.sized.proof.codes
      (frameSends W.sized.proof W.sized.set.samples 0 (reqGroups W.sized.proof.request).toList
        W.sized.proof.request.link ++ [w2]) VerifiableInference.Number.ByRuns.proofThree.A.plan =
      .ok proofSendsFull.1 := by
  have h := isB_ok p0B
  unfold p0R at h
  cases hw : wSend W.sized.proof.batch.shape with
  | error e =>
    rw [hw] at h
    exact nomatch h
  | ok w2 =>
    rw [hw] at h
    exact ⟨w2, rfl, (oneOf_walk _ _ _ _ _).trans h⟩

end Johnson.AtFull.Sends

#print axioms Johnson.AtFull.Sends.p0B
#print axioms Johnson.AtFull.Sends.p0_W
