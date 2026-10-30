-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/AtFirstThread.lean: the closing of a segment (K10) at the first chain's thread as a
named term (`firstThread`, Honest/Thread/TheFirstThread.lean), at the prover that the maker `onlineProverFromPublicFiles` returns at the filling
`onlineProverPartsInUse I o S O`: two of the five statements that a sub-protocol's authors owe at each of its borders
(`FiveAtBorder`, Honest/Thread/FiveAtBorder.lean), at all 25 closings.

  **`k10_plays_first`**      `PlaysS (firstThread h parts w) Said b`, at every Said
  **`k10_accepted_first`**   `AcceptedS (firstThread h parts w) Said fall b`, at every fall and every Said that gives `SaidOk`

The index's reader I, the thread's parts (the script, the falls' numbers, the riders' parameters) and the run's input w are
letters. h is the library's head at the return (`HeadAtReturn`).

Limits. The return of `onlineProverFromPublicFiles` and the head at it are premises. Where the thread's invariant holds at no stand of a border
both forms hold there for nothing. They do not say what the part sends. The other three of the five are not here.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.AcceptedAtBase
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open P5J (TS)
open ProofFile.Honest.FirstThread

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (onlineProverPartsInUse I o S O) = .ok A)
  (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)

include hA in
/-- **At the first thread the closing's part plays at each of the 25 closings**, at every Said. -/
theorem k10_plays_first (l : Nat) (hl : l < 25)
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) :
    PlaysS (firstThread h parts w) Said (14 * l + IM.nAt l + 5) :=
  playsS_base h.head I o S O hA parts.script _ _ _ _ _ _ _ _ _ w l hl Said

include hA in
/-- **At the first thread the closing's block accepts at each of the 25 closings**, at every fall and at every Said that
gives `SaidOk`. -/
theorem k10_accepted_first (l : Nat) (hl : l < 25)
    {Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop}
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (firstThread h parts w) Said fall (14 * l + IM.nAt l + 5) :=
  acceptedS_base h.head I o S O hA parts.script _ _ _ _ _ _ _ _ _ w l hl hSaid fall

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.k10_plays_first
#print axioms ProofFile.Honest.K10.k10_accepted_first
