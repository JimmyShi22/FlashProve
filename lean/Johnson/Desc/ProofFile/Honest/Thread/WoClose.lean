-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/WoClose.lean: the open item `wo m` of the first chain's
invariant passes over two sub-protocols at the end of a segment, from each one's own clause of
`keeps`: the closing of the segment's group (K10) and "the segment is shut" (K9). WoForward.lean has
the general lemmas, WoKinds.lean the kinds K1, K8 and K3. No definition.

  1  `putLink_four`, `shutKeeps_four`   "the segment is shut" writes the open segment's context
     alone: the statement, the list of commitment trees, `out` and what is left for the row stay.
     This is the hypothesis of `K4.k4_ridesPastAtS_wo_head` (Honest/K4/Law/WoRidesHead.lean, of the
     authors of kind K4), which gives the item over that sub-protocol
  2  `k10Keeps_left`, `k10Keeps_ledger`, `k10Keeps_rowAt`   K10's clause writes the statement after
     the step out: the ledgers of the group's members are closed and one message is marked. If the
     message of the index masks is a member of no group, its ledger stays
     (`Close.behind_ledger`, Johnson/Desc/First/Close/Law/LedgerBehind.lean), so the reader of the
     pending row gives the same answer
  3  `head_indexFree`   wherever the invariant holds, from border 3 to border 355, the message of
     the index masks is a member of no group: `head_roomLeft_thr` (PileAtHead.lean) at room 0, where
     its condition on public data is empty
  4  `ridesPastAt_wo_k10`   the hypothesis `RidesPastAt` (Honest/Thread/Shares.lean) for the item at
     `lettersHead`, over a sub-protocol whose `keeps` gives K10's clause

Limits.
  * Parts 3 and 4: full size only, and only under the library's hypothesis `AtMgA` at the hash
    function `secondHashFunction` (FirstAt.lean says which that is).
  * That `keeps b` gives the clause is a hypothesis. This file shows it for no number `b`.
  * Nothing on K9's two other sub-protocols (the batching, the one equation).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.WoKinds
import Johnson.Desc.ProofFile.Honest.Thread.PileAtHead
import Johnson.Desc.ProofFile.Honest.Thread.HeadFences
import Johnson.Desc.ProofFile.Honest.Thread.OpenFacts
import Johnson.Desc.ProofFile.Honest.K9.CloseKeeps
import Johnson.Desc.First.Close.Law.LedgerBehind
import Johnson.Desc.First.Close.Law.EPubAtK10

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

/-! ## 1 "The segment is shut" -/

/-- Writing the open segment's context leaves four things. -/
theorem putLink_four (s : S) (C : OnBytes.Model.LinkCtx) :
    (s.putLink C).st = s.st ∧ (s.putLink C).book = s.book ∧ (s.putLink C).out = s.out ∧
      leftOf (s.putLink C) = leftOf s := by
  obtain ⟨st, book, roots, ro, fl, ck, out, here, req⟩ := s
  cases here with
  | between => exact ⟨rfl, rfl, rfl, rfl⟩
  | lay a => exact ⟨rfl, rfl, rfl, rfl⟩
  | att a => exact ⟨rfl, rfl, rfl, rfl⟩
  | head a =>
    by_cases ho : a.opened = true
    · simp [S.putLink, leftOf, leftLay, leftHead, ho]
    · simp [S.putLink, leftOf, leftLay, leftHead, ho]
  | fin a => exact ⟨rfl, rfl, rfl, rfl⟩
  | mem a => exact ⟨rfl, rfl, rfl, rfl⟩

theorem shutKeeps_four {s s' : S} (k : ProofFile.Honest.K9.ShutKeeps s s') :
    s'.st = s.st ∧ s'.book = s.book ∧ s'.out = s.out ∧ leftOf s' = leftOf s := by
  obtain ⟨L, -, rfl⟩ := k.laid
  exact putLink_four s _

/-! ## 2 The closing of the segment's group -/

theorem k10Keeps_left {t t' : S} (k : ProofFile.Honest.K10.YesFree.K10Keeps t t') :
    leftOf t' = leftOf t :=
  (congrArg leftOf k.1.2).trans (VerifiableInference.Desc.First.Close.leftOf_putRec t _)

/-- If the message of the index masks is a member of no group, its ledger stays. -/
theorem k10Keeps_ledger {t t' : S} (k : ProofFile.Honest.K10.YesFree.K10Keeps t t')
    (hI : ∀ G ∈ t.st.groups, t.out.indexMasks ∉ G.members) :
    (t'.st.oracles[t.out.indexMasks]?).bind (·.ledger) =
      (t.st.oracles[t.out.indexMasks]?).bind (·.ledger) := by
  obtain ⟨L, Gq, G, m, rows, -, -, -, -, -, -, hG, -, -, e⟩ := k.1.1
  have hG' : t.st.groups[(VerifiableInference.Desc.K9.recOf t).frame.group]? = some G := hG
  have e' : t'.st = VerifiableInference.Desc.First.Close.spent
      (OnBytes.Slice.begun t.st (VerifiableInference.Desc.K9.recOf t).frame.group G) m :=
    congrArg (·.st) e
  rw [e']
  exact VerifiableInference.Desc.First.Close.behind_ledger _ _ G m _
    (hI G (Array.mem_of_getElem? hG'))

theorem k10Keeps_rowAt {t t' : S} (k : ProofFile.Honest.K10.YesFree.K10Keeps t t')
    (hI : ∀ G ∈ t.st.groups, t.out.indexMasks ∉ G.members) (lay : OnBytes.Model.WsLay) (n : Nat)
    (lin : OnBytes.Params.LinShape) : rowAt lay n lin t' = rowAt lay n lin t :=
  VerifiableInference.Desc.LinkJoin.rowAt_of_ledger (ProofFile.Honest.K10.YesFree.keeps_six k).2.2.2.1
    (k10Keeps_left k) (k10Keeps_ledger k hI) lay n lin

/-! ## 3 and 4 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- Wherever the invariant holds, from border 3 to border 355, the message of the index masks is a
member of no group. -/
theorem head_indexFree {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (hb : b ≤ cF.blocksInOrder.length) (h3 : 3 ≤ b) (h355 : b ≤ 355)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    ∀ G ∈ s.st.groups, s.out.indexMasks ∉ G.members :=
  P1L20.outOfGroupsB_iff.1
    (head_roomLeft_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (room := 0)
      (fun _ _ _ => Nat.zero_le _) hb h3 h355 hT).2

/-- The item `wo m` passes over a sub-protocol, from number 3 to number 355, whose `keeps` gives
K10's clause. -/
theorem ridesPastAt_wo_k10 {b : Nat} (hb : b ≤ cF.blocksInOrder.length) (h3 : 3 ≤ b) (h355 : b ≤ 355)
    (m : Nat)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ProofFile.Honest.K10.YesFree.K10Keeps s s') :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.wo m) :=
  ridesPastAt_wo_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m
    fun _ s _ _ s' hA hK =>
      ⟨k10Keeps_rowAt (hk s s' hK)
          (head_indexFree h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb h3 h355 hA) _ _ _,
        head_index h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA
          (open_pinI h3 (Nat.le_trans h355 (by decide))),
        k10Keeps_extends (hk s s' hK), k10Keeps_bookKept (hk s s' hK)⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.putLink_four
#print axioms ProofFile.Honest.FirstThread.shutKeeps_four
#print axioms ProofFile.Honest.FirstThread.k10Keeps_left
#print axioms ProofFile.Honest.FirstThread.k10Keeps_ledger
#print axioms ProofFile.Honest.FirstThread.k10Keeps_rowAt
#print axioms ProofFile.Honest.FirstThread.head_indexFree
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_wo_k10
