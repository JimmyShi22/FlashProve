-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Sends/SendsW.lean: THE HEAD's EXAMPLE: THE SENDINGS AS A VALUE AT THE WRITTEN PARTS:
`Johnson.G.sendsFrom` at W := writtenMade.at Hung.none returns seven chains, of which the proof
file's three are the written ones: FROM THE KEY FILE's FIVE STEPS AS NAMED PREMISES. A joining:
calls of the ledger `sendsFrom_of_parts` (Johnson/AtFull/Made/SendsLedger.lean) at
`p0_W` (ProofFirst.lean), `p1_W` | `p2_W` | `en_W` (ProofLater.lean).

  `KeySendsAtW w1 s1 K0 K1 K2`: the ledger's a₁ · a₂ · b₀ · b₁ · b₂ at W, in the ledger's own
    letters: A PREMISE.
  **`sends_W`**: KeySendsAtW w1 s1 K0 K1 K2 ⟹ ∃ En, sendsFrom W = .ok [K0, K1, K2, En,
    proofSendsFull.1, proofSendsFull.2.1, proofSendsFull.2.2].
  **`sends_all`**: ∃ En, ∀ c, freeOf c = writtenMade → sendsFrom c = …: ONE En for every such
  record.
  `sends_any`: the same at every record whose four free parts are the written ones (sendsFrom reads
  neither the bytes nor the digest: `sendsFrom_free`).

Limits. THE KEY FILE's FIVE ARE NOT SHOWN HERE (another folder holds the three chains as closed
facts in letters of its own). The entry's chain is shown to return; there is no written chain to
hold it against. That a made record's free parts are the written ones is not said here.
Nothing on soundness.
-/
import Johnson.AtFull.Sends.ProofLater
import Johnson.AtFull.Made.SendsLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Sends

open VerifiableInference.PlanWritten VerifiableInference.PlanWritten.Joined Johnson.G
  Johnson.G.MadeFree
open OnBytes OnBytes.Params
open VerifiableInference.Number.ByRuns (proofThree keyThree)
open Johnson.AtFull.Made (sendsFrom_of_parts sendsFrom_free)

/-- **The key file's five steps at the written parts**, in the ledger's own letters. -/
structure KeySendsAtW (w1 : Listed) (s1 : List Listed) (K0 K1 K2 : ChainSends) : Prop where
  a₁ : wSend W.sized.key.once.shape = .ok w1
  a₂ : linSharedSends W.sized.key.once.shape W.sized.set.samples = .ok s1
  b₀ : oneOf "key" 0 W.sized.key.codes
    ([⟨"the index-mask message", [W.sized.key.once.input]⟩,
      ⟨"the multiplicities", (Wf.messageOf W.sized.key.ranges.x).toList⟩] ++
      ioppSends "the ranges' test" W.sized.set.samples W.sized.key.ranges.x.choice.masksRide 1
        W.sized.key.ranges.x.stages ++ [w1]) keyThree.A.plan = .ok K0
  b₁ : oneOf "key" 1 W.sized.key.codes s1 keyThree.B.plan = .ok K1
  b₂ : oneOf "key" 2 W.sized.key.codes (ioppSends "the own test" W.sized.set.samples
    W.sized.key.once.shape.choice.masksRide 1 W.sized.key.once.shape.testOwn) keyThree.C.plan =
    .ok K2

/-- **The sendings as a value at the written parts.** -/
theorem sends_W {w1 : Listed} {s1 : List Listed} {K0 K1 K2 : ChainSends}
    (K : KeySendsAtW w1 s1 K0 K1 K2) :
    ∃ En, sendsFrom W = .ok [K0, K1, K2, En, proofSendsFull.1, proofSendsFull.2.1,
      proofSendsFull.2.2] := by
  obtain ⟨w2, a3, b4⟩ := p0_W
  obtain ⟨s2, a4, b5⟩ := p1_W
  obtain ⟨En, b3⟩ := en_W
  exact ⟨En, sendsFrom_of_parts (c := W) (k0 := keyThree.A.plan) (k1 := keyThree.B.plan)
    (k2 := keyThree.C.plan) (p0 := proofThree.A.plan) (p1 := proofThree.B.plan)
    (p2 := proofThree.C.plan) rfl rfl K.a₁ K.a₂ a3 a4 K.b₀ K.b₁ K.b₂ b3 b4 b5 p2_W⟩

/-- The same at every record whose four free parts are the written ones. -/
theorem sends_any {w1 : Listed} {s1 : List Listed} {K0 K1 K2 : ChainSends}
    (K : KeySendsAtW w1 s1 K0 K1 K2) {c : Configured} (hc : freeOf c = writtenMade) :
    ∃ En, sendsFrom c = .ok [K0, K1, K2, En, proofSendsFull.1, proofSendsFull.2.1,
      proofSendsFull.2.2] := by
  rw [sendsFrom_free c, hc]
  exact sends_W K

/-- **The same with the entry's chain fixed in front**: one En for every such record. -/
theorem sends_all {w1 : Listed} {s1 : List Listed} {K0 K1 K2 : ChainSends}
    (K : KeySendsAtW w1 s1 K0 K1 K2) :
    ∃ En, ∀ c : Configured, freeOf c = writtenMade →
      sendsFrom c = .ok [K0, K1, K2, En, proofSendsFull.1, proofSendsFull.2.1,
        proofSendsFull.2.2] := by
  obtain ⟨En, h⟩ := sends_W K
  refine ⟨En, fun c hc => ?_⟩
  rw [sendsFrom_free c, hc]
  exact h

end Johnson.AtFull.Sends

#print axioms Johnson.AtFull.Sends.sends_all
#print axioms Johnson.AtFull.Sends.sends_W
#print axioms Johnson.AtFull.Sends.sends_any
