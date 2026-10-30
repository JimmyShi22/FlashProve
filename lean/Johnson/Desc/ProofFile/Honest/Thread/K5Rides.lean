-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K5Rides.lean: the open items of the first chain's invariant
that pass over an attention segment's own rounds (kind K5), at `lettersHead`. A call of the lemma of
the authors of kind K5, `K5.k5_ridesPastAt_T` (Honest/K5/Law/SharesT.lean), which is stated for a
variable invariant under two structures. The same authors show both structures for the first chain's
invariant (`k5AtT_thrAt`, Honest/K5/Law/AtT.lean; `k5RidersT_thrAt`, Honest/K5/Law/RidersT.lean).
Its condition on the statement of a pin holds at the one that `lettersHead` has (`ansOn_head`,
K5Through.lean). No definition.

  `ridesPastAt_k5`   at group `g` below 12: the hypothesis `RidesPastAt` (Honest/Thread/Shares.lean)
     at the item `unmarked` and at every item of the library's five sorts that pass over that
     sub-protocol (`Att.P.riderB`, Johnson/Desc/First/Att/K05Riders.lean), other than the parts
     `lookDigits`
  `ridesPastAt_formsT_k5`   at the item `formsT (2 g + 1) 2 "objects"`

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * That `keeps` at the sub-protocol's number gives the kind's clause `K5Keeps` is a hypothesis.
    This file does not show it.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.K5Through
import Johnson.Desc.ProofFile.Honest.K5.Law.SharesT

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.First.Att.P (riderB)
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

/-- The items that pass over the own rounds of attention segment `2 g + 1`. -/
theorem ridesPastAt_k5 {g : Nat} (hg : g < 12)
    (hk : ∀ s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps (K5.borderOf g) s s' →
      H2K5.Honest.K5Keeps s s')
    (i : Item) (hi : i = .unmarked ∨ riderB (2 * g + 1) i = true)
    (hd : ∀ n, i ≠ .constr n .lookDigits) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (K5.borderOf g) i :=
  K5.k5_ridesPastAt_T h
    (K5.k5AtT_thrAt h H.first Q (fun v => H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay)) test carryX
      item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ Rd b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → Kp p s s') hg)
    (K5.k5RidersT_thrAt h H.first Q (fun v => H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay)) test carryX
      item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ Rd b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → Kp p s s') hg hk)
    hg (ansOn_head Zp Z.lay _ _) i hi hd

/-- The item `formsT (2 g + 1) 2 "objects"` passes over the own rounds of that segment. -/
theorem ridesPastAt_formsT_k5 {g : Nat} (hg : g < 12)
    (hk : ∀ s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps (K5.borderOf g) s s' →
      H2K5.Honest.K5Keeps s s') :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (K5.borderOf g)
      (Item.formsT (2 * g + 1) 2 "objects") :=
  ridesPastAt_k5 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg hk _
    (Or.inr (by simp [riderB])) (fun _ e => nomatch e)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.ridesPastAt_k5
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_formsT_k5
