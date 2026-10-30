-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/ValuesReachedHead.lean: ReachSeat (ValuesReached.lean) IS MET AT THE FIRST CHAIN's
THREAD UNDER THE HEAD, at every value of its letters (`lettersHead`,
Johnson/Desc/ProofFile/Honest/Thread/FirstHead.lean), where Said gives SaidOk: `reachSeat_head`. So the four
fields of SortValues that ValuesReached.lean pays stand there: `reached_fields_head`. Calls; nothing is evaluated.

Limits. THE ONE PREMISE LEFT: Said b k m → SaidOk b k m. At a Said that never holds the laws are idle. Nothing on
soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.ValuesReached
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest (ProverCoinCounts Coins Mid Prover Local SaidOk ValuesJ storedWords_lt)
open ProofFile.Honest.FirstThread (Script lettersHead WtF)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE SEAT IS MET AT THE FIRST CHAIN's THREAD UNDER THE HEAD, AT ALL ITS LETTERS.** -/
theorem reachSeat_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hS : ∀ b k m, Said b k m → SaidOk b k m) :
    ReachSeat Zp cF (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said where
  bs := rfl
  ft := rfl
  begun := fun _ v _ _ => ⟨v.x.pub, fun _ h0 => h0⟩
  stored := fun v i p u hu => storedWords_lt H v.w₀ v.rc i p u hu
  said := hS

/-- **THE FOUR FIELDS THERE**: the code switch at the links 1 to 23, the finish, the 25 closings. -/
theorem reached_fields_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hS : ∀ b k m, Said b k m → SaidOk b k m) (J : Nat → TS → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) (G : ProofFile.Ground) :
    (∀ l, 0 < l → l < 24 →
      ValuesJ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said J
        (firstZA (Tab.g Zp G) (Tab.vals Zp G)) fall (14 * l + 1 + 1)) ∧
    ValuesJ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said J
      (firstZA (Tab.g Zp G) (Tab.vals Zp G)) fall (353 + 0) ∧
    (∀ l, l < 24 →
      ValuesJ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said J
        (firstZA (Tab.g Zp G) (Tab.vals Zp G)) fall (14 * l + 11 + 1)) ∧
    ValuesJ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said J
      (firstZA (Tab.g Zp G) (Tab.vals Zp G)) fall (337 + 13) :=
  have R := reachSeat_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hS
  ⟨fun l h0 hl => switch_values h R l h0 hl, finish_values h R, fun l hl => close_values h R l hl,
    closeHead_values h R⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.reachSeat_head
#print axioms Johnson.AtFull.Shape.reached_fields_head
