-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/WoKinds.lean: the open item `wo m` of the first chain's
invariant passes over the sub-protocols of three kinds, from each kind's own clause of `keeps`:
a sending at a later moment of a segment (K1), the draw of the smallness test (K8) and the lookup on
the digits (K3). WoForward.lean has the general lemmas. No definition.

What the general lemmas ask and where it comes from.
  * What the open segment has left for its row (`Walk.Law.leftOf`) is read off the field `here`: in
    a feed-forward segment the field `own`, in the output head's segment the field `wo`. Each of the
    clauses writes `here` after the step out, and none of them turns these two fields (part 1).
  * K8 and K3 leave the statement, the list of commitment trees and `out` (parts 3 and 4).
  * K1: `out` stays, the statement grows, and every message that is there keeps its ledger
    (`K1Rest`, Honest/K1/Law/Keeps.lean). So the reader of the pending row gives the same answer
    (`LinkJoin.rowAt_of_ledger`, Johnson/Desc/First/Link/Law/RidersLight.lean) (part 2).

  1  `leftOf_here`, `leftOf_puts`, `k1Commit_left`, `k1Quiet_left`, `k1Reads_left`
  2  `k1Rest_ledger`, `k1Rest_rowAt`, `ridesPastAt_wo_k1`
  3  `k8Keeps_drawn`, `ridesPastAt_wo_k8`
  4  `digitsArms_four`, `k3Head_four`   the hypothesis of `K4.k4_ridesPastAtS_wo_head`
     (Honest/K4/Law/WoRidesHead.lean, of the authors of kind K4), which gives the item over a lookup
     on the digits

Limits.
  * The lemmas `ridesPastAt_…`: full size only, and only under the library's hypothesis `AtMgA` at
    the hash function `secondHashFunction` (FirstAt.lean says which that is).
  * That `keeps b` gives the kind's clause, and that the message of the index masks is there before
    the step (`hidx`), are hypotheses. This file shows them for no number `b`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.WoForward
import Johnson.Desc.ProofFile.Honest.Thread.RowPileForwardKinds
import Johnson.Desc.ProofFile.Honest.K1.Law.KeepsReads
import Johnson.Desc.K8.Honest.Keeps
import Johnson.Desc.First.K8.BlindPub
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.K3Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Close (leftHead)
open Johnson.Desc.First.Walk (leftLay)
open Johnson.Desc.First.Walk.Law (rowAt leftOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 What is left for the row -/

/-- What is left for the row is read off the field `here`. -/
theorem leftOf_here {s t : S} (e : s.here = t.here) : leftOf s = leftOf t := by
  unfold leftOf leftLay leftHead
  rw [e]

/-- Writing the open segment's context and its ledger leaves it. -/
theorem leftOf_puts (s : S) (C : OnBytes.Model.LinkCtx) (F : OnBytes.Model.Fork) :
    leftOf ((s.putLink C).putFork F) = leftOf s := by
  cases hs : s.here with
  | head a =>
    by_cases ho : a.opened = true <;>
      simp [leftOf, leftLay, leftHead, S.putFork, S.putLink, hs, ho]
  | _ => simp [leftOf, leftLay, leftHead, S.putFork, S.putLink, hs]

theorem k1Commit_left {s s' : S} (k : ProofFile.Honest.K1.K1CommitKeeps s s') :
    leftOf s' = leftOf s := by
  obtain ⟨-, -, -, L, F, tl, L', F', -, -, -, hh, -, -⟩ := k
  exact (leftOf_here hh).trans (leftOf_puts s L' F')

theorem k1Quiet_left {s s' : S} (k : ProofFile.Honest.K1.K1QuietKeeps s s') :
    leftOf s' = leftOf s := by
  obtain ⟨-, -, -, -, -, -, -, -, hh⟩ := k
  rcases hh with ⟨a, tl, e1, e2⟩ | ⟨a, t, tl, e1, e2⟩ | ⟨a, t, tl, e1, -, e2⟩ <;>
    simp [leftOf, leftLay, leftHead, e1, e2]

theorem k1Reads_left {s s' : S} (k : ProofFile.Honest.K1.K1ReadsKeeps s s') :
    leftOf s' = leftOf s := by
  obtain ⟨m, k1, k2⟩ := k
  exact (k1Quiet_left k2).trans (k1Commit_left k1)

/-! ## 2 Kind K1 -/

/-- Under `K1Rest` the message of the index masks keeps its ledger, if it is there. -/
theorem k1Rest_ledger {s s' : S} (k : ProofFile.Honest.K1.K1Rest s s')
    (hlt : s.out.indexMasks < s.st.oracles.size) :
    (s'.st.oracles[s.out.indexMasks]?).bind (·.ledger) =
      (s.st.oracles[s.out.indexMasks]?).bind (·.ledger) := by
  obtain ⟨x', hx', -, e⟩ := k.2.2.2.2.2.2.1.msg _ _ (Array.getElem?_eq_getElem hlt)
  rw [hx', Array.getElem?_eq_getElem hlt]
  exact e

/-- So the reader of the pending row gives the same answer. -/
theorem k1Rest_rowAt {s s' : S} (k : ProofFile.Honest.K1.K1Rest s s') (hl : leftOf s' = leftOf s)
    (hlt : s.out.indexMasks < s.st.oracles.size) (lay : OnBytes.Model.WsLay) (n : Nat)
    (lin : OnBytes.Params.LinShape) : rowAt lay n lin s' = rowAt lay n lin s :=
  VerifiableInference.Desc.LinkJoin.rowAt_of_ledger k.2.1 hl (k1Rest_ledger k hlt) lay n lin

/-! ## 3 and 4 Kinds K8 and K3: four fields stay -/

/-- K8's clause is the library's relation for the draw. -/
theorem k8Keeps_drawn {s s' : S} (k : VerifiableInference.Desc.First.K8.Honest.K8Keeps s s') :
    VerifiableInference.Desc.First.K8.Drawn s s' := by
  obtain ⟨tl, cf, first, h1, -, -, -, -, e⟩ := k
  exact ⟨tl, cf, first, h1, e⟩

/-- The three forms of the state after a lookup on the digits leave the four fields. -/
theorem digitsArms_four {s s' : S} {tl' : OnBytes.Model.HTailF2} {G' : OnBytes.Model.Fork}
    (k : ProofFile.Honest.K3.Law.AtThr.DigitsArms s s' tl' G') :
    s'.st = s.st ∧ s'.book = s.book ∧ s'.out = s.out ∧ leftOf s' = leftOf s := by
  rcases k with ⟨a, e1, rfl⟩ | ⟨a, e1, rfl⟩ | ⟨a, e1, -, rfl⟩ <;>
    exact ⟨rfl, rfl, rfl, by simp [leftOf, leftLay, leftHead, e1]⟩

/-- The lookup on the digits of the output head's segment leaves the four fields. -/
theorem k3Head_four {hs : OnBytes.Model.Forest.Shape} {s s' : S}
    (k : ProofFile.Honest.K3.Law.AtThr.K3KeepsHead hs s s') :
    s'.st = s.st ∧ s'.book = s.book ∧ s'.out = s.out ∧ leftOf s' = leftOf s := by
  obtain ⟨-, tl, F, H, G, a₀, claim, -, -, e1, -, rfl, -⟩ := k
  exact ⟨rfl, rfl, rfl, by simp [leftOf, leftLay, leftHead, e1]⟩

/-! ## At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The item `wo m` passes over a sub-protocol whose `keeps` gives the common part of K1's clauses,
that what is left for the row stays, and that every tree that is there stays. -/
theorem ridesPastAt_wo_k1 {b : Nat} (hb : b ≤ cF.blocksInOrder.length) (m : Nat)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ProofFile.Honest.K1.K1Rest s s' ∧ leftOf s' = leftOf s ∧
        VerifiableInference.Desc.K1.TreesOlder s.book s'.book)
    (hidx : ∀ k s mm E,
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s mm E →
      s.out.indexMasks < s.st.oracles.size) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.wo m) :=
  ridesPastAt_wo_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m
    fun k s mm E s' hA hK =>
      ⟨k1Rest_rowAt (hk s s' hK).1 (hk s s' hK).2.1 (hidx k s mm E hA) _ _ _, hidx k s mm E hA,
        k1Rest_extends (hk s s' hK).1,
        bookKept_of_rels (hk s s' hK).1.2.2.2.2.2.2.2.2 (hk s s' hK).2.2
          (head_book h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA).2
          (head_hold h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hA)⟩

/-- The item `wo m` passes over a sub-protocol whose `keeps` gives K8's clause. -/
theorem ridesPastAt_wo_k8 {b : Nat} (m : Nat)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      VerifiableInference.Desc.First.K8.Honest.K8Keeps s s')
    (hidx : ∀ k s mm E,
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s mm E →
      s.out.indexMasks < s.st.oracles.size) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.wo m) :=
  ridesPastAt_wo_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m
    fun k s mm E s' hA hK => by
      have e1 := (hk s s' hK).rest.1
      have e2 := (hk s s' hK).rest.2.1
      refine ⟨VerifiableInference.Desc.K1.rowAt_eq_of_alike
          (VerifiableInference.Desc.K1.rowAlike_of_same
            (VerifiableInference.Desc.First.K8.blind_leftOf s s' (k8Keeps_drawn (hk s s' hK)))
            (hk s s' hK).rest.2.2.2.2.2.2.1 e1) (hidx k s mm E hA) _ _ _,
        hidx k s mm E hA, ?_, fun o _ => ?_⟩
      · rw [e1]
        exact OnBytes.Means.Extends.refl _
      · rw [e2]
        exact ⟨rfl, fun _ _ => rfl⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.leftOf_here
#print axioms ProofFile.Honest.FirstThread.leftOf_puts
#print axioms ProofFile.Honest.FirstThread.k1Commit_left
#print axioms ProofFile.Honest.FirstThread.k1Quiet_left
#print axioms ProofFile.Honest.FirstThread.k1Reads_left
#print axioms ProofFile.Honest.FirstThread.k1Rest_ledger
#print axioms ProofFile.Honest.FirstThread.k1Rest_rowAt
#print axioms ProofFile.Honest.FirstThread.k8Keeps_drawn
#print axioms ProofFile.Honest.FirstThread.digitsArms_four
#print axioms ProofFile.Honest.FirstThread.k3Head_four
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_wo_k1
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_wo_k8
