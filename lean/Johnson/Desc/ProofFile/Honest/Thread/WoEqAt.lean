-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/WoEqAt.lean: the open item `wo m` of the first chain's
invariant passes over "the one equation" of each of the 25 segments, from that sub-protocol's clause
of `keeps` alone. WoEq.lean has the lemma under two facts on the state before the step. Here both
are shown wherever the invariant holds at that sub-protocol's number. No definition.

  1  `head_ownNotIndex`   no message of the open segment's own is the message of the index masks
     (`LinkJoin.OwnNotIndex`). By two lemmas of the authors of kind K9 (`K9.hne_of_reach`,
     `K9.index_of_xk`, Honest/K9/XkEqReach.lean): from "the state is reached", no mark of failure,
     and the executable tests at the border. The invariant gives the three (`thr_reach`,
     ReachFacts.lean; `xk_ew_front`, K9FormBehind.lean)
  2  `ridesPastAt_wo_eq_at`   the hypothesis `RidesPastAt` (Honest/Thread/Shares.lean) for the item
     at `lettersHead`, at number `14 l + nAt l + 4`

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * That `keeps` at that number gives the clause `EqKeeps`, and that the number is at most the
    length of the chain's list (`hb`), are hypotheses.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.WoEq
import Johnson.Desc.ProofFile.Honest.Thread.HeadFences
import Johnson.Desc.ProofFile.Honest.Thread.OpenFacts
import Johnson.Desc.ProofFile.Honest.Thread.K9FormBehind
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.ProofFile.Honest.K9.XkEqReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.LinkJoin (OwnNotIndex)
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

/-- Wherever the invariant holds in front of "the one equation" of segment `l`, no message of that
segment's own is the message of the index masks. -/
theorem head_ownNotIndex {l : Nat} (hl : l < 25) (hb : 14 * l + IM.nAt l + 4 + 0 ≤ cF.blocksInOrder.length)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + IM.nAt l + 4 + 0) k s m E) : OwnNotIndex s := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hF, -, -, -, -⟩ := hT'
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 hF.1
  have hR := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  have hxE := xk_ew_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF
  exact ProofFile.Honest.K9.hne_of_reach h hl hR h0 (ProofFile.Honest.K9.index_of_xk hl hxE)

/-- The item `wo m` passes over "the one equation" of segment `l`, if `keeps` there gives that
sub-protocol's clause. -/
theorem ridesPastAt_wo_eq_at {l : Nat} (hl : l < 25)
    (hb : 14 * l + IM.nAt l + 4 + 0 ≤ cF.blocksInOrder.length) (m : Nat)
    (hk : ∀ s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps
        (14 * l + IM.nAt l + 4 + 0) s s' →
      ProofFile.Honest.K9.EqKeeps s s') :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + IM.nAt l + 4 + 0) (Item.wo m) := by
  have h9 : IM.nAt l ≤ 9 := by
    unfold IM.nAt
    split <;> omega
  exact ridesPastAt_wo_eq h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m hk
    (fun _ _ _ _ hA => head_ownNotIndex h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hb hA)
    (fun _ _ _ _ hA => head_index h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA
      (open_pinI (by omega) (by omega)))

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_ownNotIndex
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_wo_eq_at
