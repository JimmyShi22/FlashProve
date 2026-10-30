-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/CountAtM3.lean: kind K13, the members' batching: THE GUARD "count"
OF THE NINE (`K13Guards`, Debts.lean of this folder: the pile has the plan's number of rows) UNDER
THE THREAD AT BORDER 355, AT THE LIBRARY's OWN PARAMETERS (`FirstThread.lettersAt`,
Honest/Thread/FirstAt.lean): FROM THE HYPOTHESIS h AND THE THREAD ALONE. One statement with its
proof: calls. THE FULL SIZE ALONE, AT THE HASH `OnBytes.secondHashFunction` ALONE.

The road. Under the thread the state is reached by the first 355 sub-protocols of the first chain's
flat list (`k13_reach_at`, TakenAtM3.lean). At every state reached by at most 355 of them the pile
has as many rows as the library's count `P1L20.takenAt` says (`pile_length_reach`,
PileLengthReach.lean of this folder). At 355 that count is the plan's number of rows
(`m3_rows_taken`, GuardsAtM3.lean: both are 13).

What is not claimed. That the hypothesis h can be met. That the thread holds at any run. Nothing on
any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.GuardsAtM3
import Johnson.Desc.ProofFile.Honest.K13.PileLengthReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open VerifiableInference.Desc (Chain Strs)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersAt Script WtF)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **THE GUARD "count", under the thread at border 355: from h and the thread alone.** -/
theorem k13_count_at {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
      m En) :
    s.out.pending.length = h.𝔇.P13.rows := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have q := (pile_length_reach h.scope h.reads O h.laid.planOk
    (k13_reach_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT)
    (Nat.le_refl 355)).2
  exact q.trans (m3_rows_taken h).symm

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_count_at
