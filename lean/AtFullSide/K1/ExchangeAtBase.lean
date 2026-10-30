-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/ExchangeAtBase.lean: the shared sending (kind K1) at the base prover of the online proof:
what its 52 members owe under ExchangeS (Honest/Thread/PaysS.lean), item by item.

  1  k1_places_52   the written list of places has 52 of the kind K1
  2  k1_kind_at   which 52
  3  k1_exchange_at_base   ExchangeAtS (Honest/Thread/SharesS.lean) at every place of the kind K1 and every
     item that the row owes there, but for an item that is open in front of the member and is a pin, pinI,
     pinW, or a constr at one of parts4

By k1_exchange_by_kind (Honest/K1/Law/DebtByKind.lean) at the records of k1Seated_at_base
(AtFullSide/K1/RecordAtBase.lean).

Limits.
  * Four hypotheses are left, each by name. hSaid: the condition Said gives SaidOk. hTie: the share at the
    item tie l, at each l below 25. hPile, hWrow: the shares at pileOne and wrow at number 356, which are
    the kind K13's.
  * It is not ExchangeS: the items that are left out (by OwedAtMembers.lean: pin l 0 and constr l small at
    the 25 members "reads", where they are open in front; at 356 pinW) are owed besides.
  * The head h, the return hA and OthersApart are hypotheses; cells, tok, Oth and the other ten parameters
    of lettersHead are bound by "for all".
  * At Vd := fun _ => False the thread's valid holds of nothing, and every conclusion here is idle.
  * Each conclusion stands under the invariant and the member's accepted step, inside ExchangeAtS.
  * For the honest run's own forms alone: no statement on any other party may take it. Never on
    soundness's road: DebtByKind.lean imports twins at the honest meaning.
  * This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.K1.RecordAtBase
import Johnson.Desc.ProofFile.Honest.K1.Law.DebtByKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Wit Place Block KindName)
open VerifiableInference.Desc.Sound (MsgT Mem)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T parts4)
open ProofFile.Honest.FirstThread

/-- **The written list of places has 52 of the kind K1.** -/
theorem k1_places_52 : (P5J.At.ps.filter fun p => p.kind == KindName.K1).length = 52 := by
  decide +kernel

/-- **Which 52**: at number 2, at the fifty numbers K1.noL l d and at number 356 the written list has a
place of the kind K1. With k1_number_of_kind (NumbersOfKind.lean), which says that there is no other. -/
theorem k1_kind_at :
    (P5J.At.ps[2]?).map (·.kind) = some KindName.K1 ∧
    (∀ l, l < 25 → ∀ d : Bool, (P5J.At.ps[K1.noL l d]?).map (·.kind) = some KindName.K1) ∧
    (P5J.At.ps[356]?).map (·.kind) = some KindName.K1 := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {W₀ : Type} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **K1's debt under the exchange, at the base prover.** -/
theorem k1_exchange_at_base (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (cells : LocB W₀ → CellsM OnBytes.Flat.numsFull) (tok : LocB W₀ → P5J.At.Tok)
    (Oth : Others A.B (LocB W₀)) (hO : OthersApart A Oth)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀)
    (Said : Nat → Coins A.B → Mid (LocB W₀) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (hTie : ∀ l, l < 25 → ExchangeAtS (lettersHead h A.H (scriptAt I S Op A cF cells tok Oth)
      test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said (K1.noL l false) (.tie l))
    (hPile : ExchangeAtS (lettersHead h A.H (scriptAt I S Op A cF cells tok Oth)
      test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 356 .pileOne)
    (hWrow : ExchangeAtS (lettersHead h A.H (scriptAt I S Op A cF cells tok Oth)
      test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 356 .wrow) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K1 →
      ∀ j : VerifiableInference.Desc.First.Item, j ∈ ((lettersHead h A.H (scriptAt I S Op A cF cells tok Oth)
        test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).owes →
      (j ∈ (lettersHead h A.H (scriptAt I S Op A cF cells tok Oth)
          test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b →
        (∀ m t, j ≠ .pin m t) ∧ j ≠ .pinI ∧ j ≠ .pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ .constr m q) →
      ExchangeAtS (lettersHead h A.H (scriptAt I S Op A cF cells tok Oth)
        test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b j := by
  obtain ⟨⟨b2, R2⟩, RL, ⟨bw, Rw⟩⟩ := k1Seated_at_base h hA cells tok Oth hO test carryX item n₁ n₂ b₀
    Vd Rd Kp w
  exact k1_exchange_by_kind h A.H _ test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid
    ⟨b2, _, _, _, _, _, _, _, R2⟩
    (fun l hl => (RL l hl false).elim fun bl R => ⟨bl, _, _, _, _, _, _, _, R⟩)
    (fun l hl => (RL l hl true).elim fun bl R => ⟨bl, _, _, _, _, _, _, _, R⟩)
    ⟨bw, _, _, _, _, _, _, _, Rw⟩ hTie hPile hWrow

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1_places_52
#print axioms ProofFile.Honest.K1.k1_kind_at
#print axioms ProofFile.Honest.K1.k1_exchange_at_base
