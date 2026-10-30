-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/K11PinRides.lean: the items `pin m t`, `pinI` and `unmarked` of
the first chain's invariant at sub-protocol number 346, the merge of the claims on the weights (kind
K11). The file holds four conditional lemmas and no definition.

The condition of the kind K11 for `keeps` is `K11Keeps P` (Johnson/Desc/K11/Returns/
KeepsStatement.lean). It writes the state
after the step as the state before it with two fields changed (`rowsOwed`, and `here` in the output
head's own part), and says that no failure mark is set. So the statement is as it was, and the
hypotheses of Honest/Thread/PinRides.lean hold.

  1  `k11Keeps_st`, `k11Keeps_mark`   `K11Keeps` leaves the statement as it was; no failure mark
  2  `k11_rides_pins`   `pin m t` (for all `m`, `t`), `pinI` and `unmarked` pass over number 346
  3  `k11_pins_again`   `pin m t` and `pinI`, where the row of number 346 has to show them again

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the format's second hash function.
  * `hk` is a hypothesis: that `keeps 346` gives `K11Keeps P` for some `P`. It holds where the
    argument `Kp` of `lettersHead` is chosen so at the place of number 346; `kpBy fHead`
    (Honest/Thread/FHead.lean) is chosen so.
  * In `k11_pins_again`, that the item is open at border 346 (`hi`) and the condition `BehindS` at
    346 (`hB`) are hypotheses.
  * The other items that are open across number 346 are not treated here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PinRides
import Johnson.Desc.K11.Returns.KeepsStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open Johnson.Desc.First.ForkMerge.Returns (K11Keeps)

/-- `K11Keeps` leaves the statement as it was. -/
theorem k11Keeps_st {P : Johnson.Desc.First.ForkMerge.HeadMergeP} {s s' : TS}
    (h : K11Keeps P s s') : s'.st = s.st := by
  obtain ⟨⟨a, wo, v, β, -, -, -, -, -, -, rfl⟩, -⟩ := h
  rfl

/-- `K11Keeps` includes "no failure mark after the step". -/
theorem k11Keeps_mark {P : Johnson.Desc.First.ForkMerge.HeadMergeP} {s s' : TS}
    (h : K11Keeps P s s') : s'.failed = none := h.2

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The items `pin m t`, `pinI` and `unmarked` pass over sub-protocol number 346. -/
theorem k11_rides_pins (P : Johnson.Desc.First.ForkMerge.HeadMergeP)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 346 s s' →
      K11Keeps P s s') :
    (∀ m t, RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 346
      (Item.pin m t)) ∧
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 346 Item.pinI ∧
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 346 Item.unmarked :=
  ⟨fun m t => ridesPastAt_pin h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m t
      fun s s' hK => k11Keeps_st (hk s s' hK),
    ridesPastAt_pinI h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      fun s s' hK => k11Keeps_st (hk s s' hK),
    ridesPastAt_unmarked h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      fun s s' hK => k11Keeps_mark (hk s s' hK)⟩

/-- The pins, where the row of sub-protocol number 346 has to show them again after the step. -/
theorem k11_pins_again (P : Johnson.Desc.First.ForkMerge.HeadMergeP)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 346 s s' →
      K11Keeps P s s')
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hB : BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 346) :
    (∀ m t,
      Item.pin m t ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened 346 →
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 346
        (Item.pin m t)) ∧
    (Item.pinI ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened 346 →
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 346
        Item.pinI) :=
  ⟨fun m t hi => exchangeAtS_pin h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m t Said
      (fun s s' hK => k11Keeps_st (hk s s' hK)) hi hB,
    fun hi => exchangeAtS_pinI h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
      (fun s s' hK => k11Keeps_st (hk s s' hK)) hi hB⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k11Keeps_st
#print axioms ProofFile.Honest.FirstThread.k11Keeps_mark
#print axioms ProofFile.Honest.FirstThread.k11_rides_pins
#print axioms ProofFile.Honest.FirstThread.k11_pins_again
