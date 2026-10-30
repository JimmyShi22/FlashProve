-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/HeadPinW.lean: THE STORED TABLE's PIN (the item `pinW`) AT THE
FIRST CHAIN's THREAD AT THE HEAD: IT HOLDS BY UNFOLDING, AT EVERY BORDER. The library's `pinW`
says: the witness's cells are what the stored table decodes to, with the record (`pinWOf`,
Johnson/Desc/Sound/MeaningSig.lean). At the threads the decoder is the constant "the Script's cells
of the input" (`lettersAt`, Honest/Thread/FirstAt.lean: decT), and the thread's witness has just
these cells (`Script.wit`, Honest/Thread/First.lean). So at the thread's own witness the item says
"x = x": it reads neither the state nor an oracle. Hence its shares (`ExchangeAt`, `RidesPastAt`:
Honest/Thread/Shares.lean) of `Exchange` and `RidesPast` (Honest/Thread/Pays.lean) are paid at every
member: no kind's authors owe them.

  `head_pinW`   the item at the thread's own witness
  `ridesPastAt_pinW`, `exchangeAt_pinW`   its two shares, at every member

Limits. It says nothing of the stored table itself: the constant decoder is a letter's filling at
the threads. THE FULL SIZE ALONE. None is one of the library's goals. This file proves nothing about
soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.Shares

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **AT THE THREAD's OWN WITNESS THE STORED TABLE's PIN HOLDS**: at every input, state, oracles,
coins and challenges. -/
theorem head_pinW (v : Local W₀ Rc ProofFile.Inst Tr) (a : ProofFile.InstPub × TS) (y : Strs) (k : Coins Bk)
    (ds : List Fmt.Drawn) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.means v Item.pinW a y
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k v ds) := rfl

/-- It reads neither the state nor the oracles: so it rides past every member. -/
theorem ridesPastAt_pinW (b : Nat) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pinW :=
  fun _ _ _ _ _ _ _ _ _ h0 => h0

/-- Its share of `Exchange`, at every member. -/
theorem exchangeAt_pinW (b : Nat) :
    ExchangeAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pinW := by
  intro blk _ k s m E ds y cols s' _ _ _ ds' j hj
  obtain rfl := List.mem_singleton.1 hj
  exact head_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w _ _ _ _ _

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_pinW
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pinW
#print axioms ProofFile.Honest.FirstThread.exchangeAt_pinW
