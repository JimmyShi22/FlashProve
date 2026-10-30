-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FirstFillK1.lean: CONDITIONAL: IN THE PROVER THAT onlineProverFromPublicFiles
RETURNS AT THE FILLING widerFillAt NO SIDE STANDS AT A PLACE OF THE KIND K1 BEHIND THE SEGMENTS: so
none at the sending that follows the last segment. One statement with its proof: wider_first_none_in
(Honest/Thread/FirstFill.lean) at k1_linked (Honest/Thread/FirstFillKinds.lean).

  k1_none_behind   CONDITIONAL: A.H.first.find? (fun g => g.place == ⟨c, none, pc, .K1⟩) = none, at
                   every chain's number c and piece pc

Why it is said. K1 is one of the ten kinds that have a list in the filling, so the statement on the
kinds without a list (wider_first_none) does not reach this place.

The premises. h: onlineProverFromPublicFiles returns A at the filling · K: WiderKinds at A's public part and ground.

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. Conditional. Neither premise is proved here. That a sub-protocol of the kind K1 stands
behind the segments, and that it has a round, is not said here. The statement is about lists and
places. No property of a prover or a protocol is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstFill
open VerifiableInference.Desc (Place KindName)

variable {W₀ : Type} {I : WiderIn W₀} {o o' : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {pol lay KL : ByteArray} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **NO SIDE AT A PLACE OF THE KIND K1 BEHIND THE SEGMENTS.** CONDITIONAL: onlineProverFromPublicFiles returns A at the
filling; WiderKinds at A's public part and ground. -/
theorem k1_none_behind (h : onlineProverFromPublicFiles o' pol lay KL (widerFillAt I o S O) = .ok A)
    (K : WiderKinds I o S O A.Z A.G) (c pc : Nat) :
    A.H.first.find? (fun g => g.place == ⟨c, none, pc, .K1⟩) = none := by
  refine wider_first_none_in h K (q := (HLot.byPub I.weights (LongLots.plain o S O).k1, .K1))
    (by unfold widerPairs; exact .head _) rfl ?_
  rw [List.find?_eq_none]
  intro x hx e
  have hx' : x ∈ (K1.dataSideNo S (fun w : Local W₀ IndexCommitterCoins Inst Cells =>
      ⟨w.x, ⟨w.trace, I.weights A.Z w.w₀, w.rc⟩⟩) o :
      HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves A.Z A.G := hx
  have hl := k1_linked S _ o A.Z A.G x hx'
  have ep : x.place = ⟨c, none, pc, .K1⟩ := beq_iff_eq.1 e
  rw [ep] at hl
  exact hl rfl

end ProofFile.Honest.FirstFill

#print axioms ProofFile.Honest.FirstFill.k1_none_behind
