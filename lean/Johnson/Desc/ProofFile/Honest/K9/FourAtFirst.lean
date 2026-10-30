-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/FourAtFirst.lean: FOUR OF THE FIVE STATEMENTS THAT A SUB-PROTOCOL OWES AT ITS BORDER, AT EVERY BORDER OF THE KIND K9, at the
first chain's thread of the online part as a named term (`firstThread`, Honest/Thread/TheFirstThread.lean), at the prover that the maker
`onlineProverFromPublicFiles` returns at the filling `onlineProverPartsInUse`: "it plays" (`PlaysS`), "behind" (`BehindS`), "exchange" (`ExchangeS`), "rides past"
(`RidesPastS`): what `OwesS` (Honest/Thread/PaysS.lean) asks at a border.

  **`four_at_k9_first`**   at every number b at which the written list of places has a place of the kind K9 (75 numbers: three in each
                         of the 25 segments: the batching, "the one equation", "the segment is shut"): the four, at every Said that
                         gives `SaidOk`

Where each comes from: Honest/K9/AtFirstThread.lean · BehindAtFirst.lean · ExchangeBatFirst.lean, ExchangeEq.lean, FiveAtShut.lean · RidesAtFirst.lean.

What is left as premises: the maker's return hA · the head at that return · Said gives `SaidOk`.

Limits. The fifth statement (the sub-protocol's own step accepts) is not here: at the first chain it goes by the run on shapes, from
the named tests on values (Honest/K9/BatchHeadPaid.lean, EqAtFirst.lean). All four speak at every stand at which the thread's invariant
(`Thr`) and Said hold; that they hold together at any run is not proved here: where they hold at none, the four hold for nothing.
This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.FiveAtShut
import Johnson.Desc.ProofFile.Honest.K9.RidesAtFirst
import Johnson.Desc.ProofFile.Honest.K9.ExchangeBatFirst
import Johnson.Desc.ProofFile.Honest.K9.ExchangeEq
import Johnson.Desc.ProofFile.Honest.K9.SendsNothing

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc
open ProofFile.Honest.FirstThread

/-- **The four at every border of this kind, at the first thread at the maker's return.** -/
theorem four_at_k9_first {W₀ : Type} {files : VerifierAndGoals.PublicFiles} (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o Sz O) = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (Said : ℕ → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) {b : ℕ} {pl : Place} (hp : P5J.At.ps[b]? = some pl)
    (hk : pl.kind = KindName.K9) :
    PlaysS (firstThread h parts w) Said b ∧ BehindS (firstThread h parts w) Said b ∧
      ExchangeS (firstThread h parts w) Said b ∧ RidesPastS (firstThread h parts w) Said b := by
  obtain ⟨l, hl, e | e | e⟩ := k9_number hp hk <;> subst e
  · exact ⟨(playsS_k9_first I o Sz O hA h parts w l hl Said).1, (k9_behindS_first h parts w Said l hl).1,
      k9_exchangeS_bat_first h parts w Said hSaid l hl, (k9_ridesPastS_first h parts w Said l hl).1⟩
  · exact ⟨(playsS_k9_first I o Sz O hA h parts w l hl Said).2.1, (k9_behindS_first h parts w Said l hl).2.1,
      k9_exchangeS_eq_first h parts w Said hSaid l hl, (k9_ridesPastS_first h parts w Said l hl).2.1⟩
  · exact ⟨(playsS_k9_first I o Sz O hA h parts w l hl Said).2.2, (k9_behindS_first h parts w Said l hl).2.2,
      k9_exchangeS_shut h.head A.H parts.script _ _ _ _ _ _ _ _ _ w Said l hl,
      (k9_ridesPastS_first h parts w Said l hl).2.2⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.four_at_k9_first
