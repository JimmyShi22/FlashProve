-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Sends/ProofLater.lean: THE HEAD's EXAMPLE: THE SENDINGS OF THE PROOF FILE's TWO LATER
CHAINS AND OF THE ENTRY's CHAIN AT THE WRITTEN PARTS, AS VALUES: closed facts by Lean's kernel, at
sendsFrom's inner routine `oneOf` itself (these plans are short).

  `p1B` | `p2B`: the closed facts; `p1B_no` | `p2B_no`: their controls, which come out false.
  **`p1_W`**: ∃ s2, linSharedSends … = .ok s2 ∧ oneOf "proof" 1 … s2 proofThree.B.plan = .ok
    proofSendsFull.2.1: the ledger's a₄ and b₅. **`p2_W`**: the ledger's b₆.
  `enB` | **`en_W`**: the entry's chain returns: ∃ En: the ledger's b₃ (there is no written chain to
    hold it against).

Limits. At the written parts W := writtenMade.at Hung.none alone. Nothing on soundness.

-/
import Johnson.AtFull.Sends.ProofFirst

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Sends

open VerifiableInference.PlanWritten VerifiableInference.PlanWritten.Joined Johnson.G
  Johnson.G.MadeFree
open OnBytes OnBytes.Params
open VerifiableInference.Number.ByRuns (proofThree)

/-- The second chain's sendings. -/
def p1R : Except String ChainSends :=
  (linSharedSends W.sized.proof.batch.shape W.sized.set.samples).bind fun s2 =>
    oneOf "proof" 1 W.sized.proof.codes s2 proofThree.B.plan

/-- The third chain's sendings. -/
def p2R : Except String ChainSends :=
  oneOf "proof" 2 W.sized.proof.codes (ioppSends "the own test" W.sized.set.samples
    W.sized.proof.batch.shape.choice.masksRide 1 W.sized.proof.batch.shape.testOwn)
    proofThree.C.plan

/-- The entry's chain's sendings. -/
def enR : Except String ChainSends :=
  oneOf "entry" 0 W.sized.entryCodes
    (⟨"the link's message", (linkMessage W.sized.link.shape W.sized.set.samples).toList⟩ ::
      ioppSends "the link's test" W.sized.set.samples W.sized.link.shape.choice.masksRide 1
        W.sized.link.shape.test) W.entry

theorem p1B : isB p1R proofSendsFull.2.1 = true := by decide +kernel
theorem p1B_no : isB p1R proofSendsFull.2.2 = false := by decide +kernel
theorem p2B : isB p2R proofSendsFull.2.2 = true := by decide +kernel
theorem p2B_no : isB p2R proofSendsFull.2.1 = false := by decide +kernel
theorem enB : enR.toOption.isSome = true := by decide +kernel

/-- **The ledger's a₄ and b₅ at the written parts.** -/
theorem p1_W : ∃ s2, linSharedSends W.sized.proof.batch.shape W.sized.set.samples = .ok s2 ∧
    oneOf "proof" 1 W.sized.proof.codes s2 proofThree.B.plan = .ok proofSendsFull.2.1 := by
  have h := isB_ok p1B
  unfold p1R at h
  cases hw : linSharedSends W.sized.proof.batch.shape W.sized.set.samples with
  | error e =>
    rw [hw] at h
    exact nomatch h
  | ok s2 =>
    rw [hw] at h
    exact ⟨s2, rfl, h⟩

/-- **The ledger's b₆ at the written parts.** -/
theorem p2_W : oneOf "proof" 2 W.sized.proof.codes (ioppSends "the own test" W.sized.set.samples
    W.sized.proof.batch.shape.choice.masksRide 1 W.sized.proof.batch.shape.testOwn)
    proofThree.C.plan = .ok proofSendsFull.2.2 := isB_ok p2B

/-- **The ledger's b₃ at the written parts.** -/
theorem en_W : ∃ En, oneOf "entry" 0 W.sized.entryCodes
    (⟨"the link's message", (linkMessage W.sized.link.shape W.sized.set.samples).toList⟩ ::
      ioppSends "the link's test" W.sized.set.samples W.sized.link.shape.choice.masksRide 1
        W.sized.link.shape.test) W.entry = .ok En := by
  have h := enB
  unfold enR at h
  cases hw : oneOf "entry" 0 W.sized.entryCodes
    (⟨"the link's message", (linkMessage W.sized.link.shape W.sized.set.samples).toList⟩ ::
      ioppSends "the link's test" W.sized.set.samples W.sized.link.shape.choice.masksRide 1
        W.sized.link.shape.test) W.entry with
  | error e =>
    rw [hw] at h
    exact nomatch h
  | ok En => exact ⟨En, rfl⟩

end Johnson.AtFull.Sends

#print axioms Johnson.AtFull.Sends.p1B
#print axioms Johnson.AtFull.Sends.p1B_no
#print axioms Johnson.AtFull.Sends.p2B
#print axioms Johnson.AtFull.Sends.p2B_no
#print axioms Johnson.AtFull.Sends.enB
#print axioms Johnson.AtFull.Sends.p1_W
#print axioms Johnson.AtFull.Sends.p2_W
#print axioms Johnson.AtFull.Sends.en_W
