-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/WoRidesHead.lean

What is here. Law/WoRidesAt.lean's statement at the parameters at which the threads' own file lays
the first chain's thread (`lettersHead`, Honest/Thread/FirstHead.lean), with the clause of keeps
in that file's form: by the member's place. One statement with its proof: unfolding and a call.

  `k4_ridesPastAtS_wo_head`: RidesPastAtS T Said b (Item.wo m).

Limits. CONDITIONAL: on h, on hp (the list of places has a place p at the number b) and on hK:
that, wherever the thread's sentence and what has been said hold in front, the thread's parameter
Kp at that place leaves the statement, the book, «out» and what is left for the pending row. hK IS
SHOWN OF NO PLACE HERE; it is not meant for a member that turns the statement or the book
(Law/WoRides.lean's `K4WoSame` is the form there). THE FULL SIZE ALONE, AND THE FORMAT's EARLIER
HASH ALONE. IT IS A LAW, NOT A PART: through h it rests on modules under Johnson/Goal/ (a walk
stops at 16 there): no file that defines a part may build on it. Nothing on soundness, on
completeness or on any other property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.WoRidesAt
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Strs Chain)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA TS CellsM)
open Johnson.Desc.First.Walk.Law (leftOf)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **`RidesPastAtS` AT THE PENDING ROW's ITEM, AT THE THREAD, AT A PLACE THAT LEAVES THE FOUR.**
CONDITIONAL: on h, hp and hK. -/
theorem k4_ridesPastAtS_wo_head
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) (b m : Nat) {p : Place}
    (hp : P5J.At.ps[b]? = some p)
    (hK : ∀ k s m E s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said b k s m E →
      Kp p s s' → s'.st = s.st ∧ s'.book = s.book ∧ s'.out = s.out ∧ leftOf s' = leftOf s) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread
      Said b (Item.wo m) :=
  k4_ridesPastAtS_wo_at h _ Q _ _ test carryX item n₁ n₂ _ _ _ Said b m
    fun k s m E s' hT hk => hK k s m E s' hT (hk p hp)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_ridesPastAtS_wo_head
