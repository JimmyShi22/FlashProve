-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/ExchangeWhole.lean: the shared sending (kind K1) at the base prover of the online proof:
ExchangeS (Honest/Thread/PaysS.lean), whole, at 26 of the kind's 52 members: at number 2 (the opening) and
at the 25 members "digits" (K1.noL l true).

  1  exchangeS_two_base      ExchangeS at number 2
  2  exchangeS_digits_base   ExchangeS at K1.noL l true, at each l below 25

At these members the row owes pins and sample rows alone (owed_two, owed_digits: OwedAtMembers.lean, by the
kernel), and each is paid under the record K1Seated, which k1Seated_at_base (RecordAtBase.lean) gives.

Limits.
  * The head h, the return hA and OthersApart are hypotheses. No hypothesis is put on Said, on cells, tok, or
    on the other ten parameters of lettersHead.
  * At Vd := fun _ => False the thread's valid holds of nothing, and both conclusions are idle.
  * A law under the member's accepted step holds of nothing at a book that does not cover the part's count.
    Here that is not so: hasCoins is a field of the record K1Seated, and k1Seated_at_base pays it at A.B.
  * OthersApart is met at the sum of the code switch's and the proximity test's shares
    (othersApart_at_shares, RecordAtBase.lean).
  * Each conclusion stands under the invariant and the member's accepted step, inside ExchangeS.
  * The 25 members "reads" and number 356 are not here: there the items tie l, pileOne, wrow and the items
    that are owed again are left (ExchangeAtBase.lean).
  * This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.K1.RecordAtBase
import Johnson.Desc.ProofFile.Honest.K1.Law.SharesAtMembers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Wit Place Block)
open VerifiableInference.Desc.Sound (MsgT Mem)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread

variable {Z : VerifierAndGoals.PublicFiles} {W₀ : Type} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **ExchangeS at number 2, at the base prover.** -/
theorem exchangeS_two_base (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (cells : LocB W₀ → CellsM OnBytes.Flat.numsFull) (tok : LocB W₀ → P5J.At.Tok)
    (Oth : Others A.B (LocB W₀)) (hO : OthersApart A Oth)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀)
    (Said : Nat → Coins A.B → Mid (LocB W₀) Unit → Prop) :
    ExchangeS (lettersHead h A.H (scriptAt I S Op A cF cells tok Oth)
      test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 2 := by
  obtain ⟨⟨b2, R⟩, -, -⟩ := k1Seated_at_base h hA cells tok Oth hO test carryX item n₁ n₂ b₀ Vd Rd
    Kp w
  refine (exchangeS_iff _ Said).2 fun j hj => ?_
  rcases owed_two hj with rfl | rfl | rfl
  · exact exchange_pin R Said 0 0 rfl
  · exact exchange_pinI R Said
  · exact exchange_rows_two h A.H _ test carryX item n₁ n₂ b₀ Vd Rd Kp w R Said

/-- **ExchangeS at each of the 25 members "digits", at the base prover.** -/
theorem exchangeS_digits_base (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (cells : LocB W₀ → CellsM OnBytes.Flat.numsFull) (tok : LocB W₀ → P5J.At.Tok)
    (Oth : Others A.B (LocB W₀)) (hO : OthersApart A Oth)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀)
    (Said : Nat → Coins A.B → Mid (LocB W₀) Unit → Prop) {l : ℕ} (hl : l < 25) :
    ExchangeS (lettersHead h A.H (scriptAt I S Op A cF cells tok Oth)
      test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said (K1.noL l true) := by
  obtain ⟨-, RL, -⟩ := k1Seated_at_base h hA cells tok Oth hO test carryX item n₁ n₂ b₀ Vd Rd Kp w
  obtain ⟨bl, R⟩ := RL l hl true
  refine (exchangeS_iff _ Said).2 fun j hj => ?_
  rcases owed_digits hl hj with rfl | rfl
  · exact exchange_pin R Said l 2 rfl
  · exact exchange_rows_fifty_tied h A.H _ test carryX item n₁ n₂ b₀ Vd Rd Kp w hl true R Said

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.exchangeS_two_base
#print axioms ProofFile.Honest.K1.exchangeS_digits_base
