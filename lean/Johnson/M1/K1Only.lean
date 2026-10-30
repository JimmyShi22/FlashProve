-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- no other lot of the term's filling lays a half of the kind K1.
/-
Johnson/M1/K1Only.lean: of the lots of the unread filling, a half at a place of the kind K1 lies in
K1's own lot or in W's. No property of the protocol is claimed here.
-/
import Johnson.M1.FillTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc

variable {W₀ : Type}

/-- **No other lot lays a half of the kind K1.** -/
theorem k1_only (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots, ∀ g ∈ M.halves Z G, g.place.kind = KindName.K1 →
      M = HLot.byPub I.weights (LongLots.plain (W₀ := W₀) (X := Unit) o S O).k1 ∨
        M = wLotAt I o O := by
  intro M hM g hg e
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((h | rfl) | rfl) | rfl
  · rw [widerFillAt_lots] at h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
    have hk := (FirstFill.widerKinds I o S O Z G).all q hq g hg
    rw [e] at hk
    have k : q.2 = KindName.K1 := hk.symm
    have e' : q = (HLot.byPub I.weights (LongLots.plain o S O).k1, .K1) :=
      List.inj_on_of_nodup_map widerPairs_nodup hq (List.Mem.head _) k
    rw [e']
    exact .inl rfl
  · have hk := closeLotAt_kinds I S Z G g hg
    rw [e] at hk
    cases hk
  · have hk := proxLotAt_kinds I S Z G g hg
    rw [e] at hk
    cases hk
  · exact .inr rfl

end Johnson.M1

#print axioms Johnson.M1.k1_only
