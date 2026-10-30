-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/FiveByKind.lean: the shared sending (kind K1): the five statements in the form FiveAtBorderJ at
every place of the kind K1 in the first chain's written list, at the first thread of the base prover
(firstThread h parts w, Honest/Thread/TheFirstThread.lean) with the Script firstScriptAt.

  1  k1_fiveJ_first   FiveAtBorderJ at every b whose place in P5J.At.ps has the kind K1

By k1_number_of_kind (Honest/K1/Law/NumbersOfKind.lean) such a b is 2, K1.noL l d with l below 25, or 356; there
are 52 (k1_places_52, k1_kind_at: ExchangeAtBase.lean). Then k1_fiveJ_two_first, k1_fiveJ_digits_first
(FiveAtFirst.lean), k1_fiveJ_reads_first (FiveAtBorderReads.lean), k1_fiveJ_w_first (FiveAtBorderW.lean).

Limits.
  * THREE HYPOTHESES ARE DEBTS. hyes: the run on shapes returns over the 358 members, from startShA; proved at no
    public files. hTie: the share of the exchange at the item tie l at the 25 members "reads". hWrow: the share
    at the item wrow at 356, the kind K13's. hTie and hWrow speak of values: they can be met only at the honest
    prover's parameters (S := Sz.ref, Op := openHonest, an I whose trace is the model's); whoever spends a law
    that pays them nails these.
  * hSaid: the condition Said gives SaidOk.
  * hA (the maker returns A at the base filling), h (the head at that return) and hQ (the thread's Script is
    firstScriptAt) are hypotheses.
  * The fields accepted and next are asked with J in hand. That J begins at the chain's start, and that it is
    carried, which needs NextJ at every member in front, of every kind, is not shown here. At a fall that
    always speaks they are idle.
  * Each field stands under the thread's invariant in front of the member. That the invariant holds there at a
    run needs the five statements at every member in front, of every kind. At an input that does not meet the
    thread's valid (ReadyInput) all six fields are idle.
  * The first chain of the online proof alone. The shared chain's two places of the kind K1, the key file's
    sendings and the link's are not here.
  * This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.K1.FiveAtBorderReads
import AtFullSide.K1.FiveAtBorderW
import Johnson.Desc.ProofFile.Honest.K1.Law.NumbersOfKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (KindName)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread
open Johnson.AtFull.Shape

variable {files : VerifierAndGoals.PublicFiles} {W₀ : Type} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **The five statements at every place of the kind K1 in the first chain, at the first thread.** -/
theorem k1_fiveJ_first
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (hQ : parts.script = firstScriptAt I S Op A h.firstChain) (w : LocB W₀)
    (Said : Nat → Coins A.B → Mid (LocB W₀) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (fall : Nat → TS → List Fmt.Drawn → Option String)
    (hyes : (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))).yes startShA 358 =
      true)
    (hTie : ∀ l, l < 25 → ExchangeAtS (firstThread h parts w) Said (K1.noL l false) (.tie l))
    (hWrow : ExchangeAtS (firstThread h parts w) Said 356 .wrow) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K1 →
      FiveAtBorderJ (firstThread h parts w) Said
        (shapeJ (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))) startShA) fall
        b := by
  intro b p hb hk
  rcases k1_number_of_kind hb hk with rfl | ⟨l, hl, d, rfl⟩ | rfl
  · exact k1_fiveJ_two_first hA h parts hQ w Said fall hyes
  · cases d
    · exact k1_fiveJ_reads_first hA h parts hQ w Said hSaid fall hyes hl (hTie l hl)
    · exact k1_fiveJ_digits_first hA h parts hQ w Said fall hyes hl
  · exact k1_fiveJ_w_first hA h parts hQ w Said fall hyes hWrow

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1_fiveJ_first
