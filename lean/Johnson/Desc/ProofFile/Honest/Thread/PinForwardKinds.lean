-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/PinForwardKinds.lean: the hypothesis of PinForward.lean, "a first
sample row that the statement holds before the step is still there after it", for the sub-protocols
of two kinds whose step changes the statement: a sending of oracle messages (kind K1) and the
closing of a segment (kind K10). Each is shown from the clause of `keeps` that the authors of that
kind's lemmas have written. No definition.

  1  `k1Rest_row`, `k1KeepsAt_rest`, `k1KeepsAt_row`   kind K1. The common part of its clauses
     (`K1Rest`, Honest/K1/Law/Keeps.lean) states that a message that is marked as sampled keeps its
     sample rows (`K1.SmpStay`). It states nothing about a message without the mark. So the lemma
     has a second hypothesis on the statement before the step: a message without the mark has no
     sample row (`OnBytes.Means.NoneYet`)
  2  `k10Keeps_row`   kind K10. By `keeps_st` (Johnson/Desc/K10/Honest/Keeps.lean) every message
     has the same sample rows after the step, so the first sample row is the same
  3  `head_tidy`   the second hypothesis of 1 holds wherever the invariant holds: the library shows
     that the statement of every state that the first chain reaches without a failure mark is tidy
     (`OnBytes.Means.Tidy`, the field `tidy` of `FoldFacts`), and ReachFacts.lean has that
     structure at the invariant. `Tidy` contains `NoneYet`, and also `InOrder`
  4  `head_older_k1`, `head_older_same`   the hypothesis in the form in which PinForward.lean takes it

Limits.
  * Parts 3 and 4: full size only, and only under the library's hypothesis `AtMgA` at the hash
    function `secondHashFunction` (FirstAt.lean says which that is).
  * Part 4 takes as a hypothesis that `keeps b` gives the kind's clause. This file shows that for
    no number `b`.
  * `K1KeepsAt p` is `False` at every place `p` other than pieces 4 to 7 of a segment of the first
    chain with kind K1. Two places of kind K1 are among these (the head of KeepsMember.lean names
    them). At all of them `k1KeepsAt_rest` and `k1KeepsAt_row` state nothing.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PinForward
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.ProofFile.Honest.K1.Law.KeepsMember
import Johnson.Desc.K10.Honest.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 Kind K1 -/

/-- Where the common part of K1's clauses holds, and a message without the mark has no sample row
before the step, a first sample row that is there stays. -/
theorem k1Rest_row {s s' : S} (k : ProofFile.Honest.K1.K1Rest s s') (hN : OnBytes.Means.NoneYet s.st)
    {o : Nat} {q : OnBytes.Row} (hq : rowAt₀ s.st o = some q) : rowAt₀ s'.st o = some q :=
  rowAt₀_smpStay k.2.2.2.2.1.2 hN hq

/-- K1's clause at a place contains the common part. -/
theorem k1KeepsAt_rest {p : Place} {s s' : S} (k : ProofFile.Honest.K1.K1KeepsAt p s s') :
    ProofFile.Honest.K1.K1Rest s s' := by
  unfold ProofFile.Honest.K1.K1KeepsAt at k
  split at k <;>
    first
      | exact ProofFile.Honest.K1.rest_reads k.1
      | exact k.1.1
      | exact k.elim

/-- The same as `k1Rest_row`, from K1's clause at a place. -/
theorem k1KeepsAt_row {p : Place} {s s' : S} (k : ProofFile.Honest.K1.K1KeepsAt p s s')
    (hN : OnBytes.Means.NoneYet s.st) {o : Nat} {q : OnBytes.Row} (hq : rowAt₀ s.st o = some q) :
    rowAt₀ s'.st o = some q :=
  k1Rest_row (k1KeepsAt_rest k) hN hq

/-! ## 2 Kind K10 -/

/-- Where K10's clause holds, every message's first sample row is the same after the step. -/
theorem k10Keeps_row {t t' : S} (k : ProofFile.Honest.K10.YesFree.K10Keeps t t') (o : Nat) :
    rowAt₀ t'.st o = rowAt₀ t.st o :=
  rowAt₀_same ((ProofFile.Honest.K10.YesFree.keeps_st k.1.1).2.2.2.1 o)

/-! ## 3 The statement is tidy wherever the invariant holds -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **Wherever the invariant holds, the verifier's statement is tidy.** -/
theorem head_tidy {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (hb : b ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    OnBytes.Means.Tidy s.st := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hF, -, -, -, -⟩ := hT'
  exact OnBytes.Means.tidy4B_iff.1
    ((foldFacts_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).tidy b (m.st.input.x.pub, s)
      ⟨hb, k, m, E, hT, rfl⟩ (Option.isNone_iff_eq_none.1 hF.1))

/-! ## 4 The hypothesis in the form in which PinForward.lean takes it -/

/-- At a sub-protocol whose `keeps` gives the common part of K1's clauses. -/
theorem head_older_k1 {b : Nat} (hb : b ≤ cF.blocksInOrder.length)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ProofFile.Honest.K1.K1Rest s s') :
    ∀ k s mm E s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s mm E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ∀ o q, rowAt₀ s.st o = some q → rowAt₀ s'.st o = some q :=
  fun _ s _ _ s' hA hK _ _ hq =>
    k1Rest_row (hk s s' hK)
      (head_tidy h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hA).noneYet hq

/-- At a sub-protocol whose `keeps` leaves every message's first sample row. -/
theorem head_older_same {b : Nat}
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ∀ o, rowAt₀ s'.st o = rowAt₀ s.st o) :
    ∀ k s mm E s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s mm E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ∀ o q, rowAt₀ s.st o = some q → rowAt₀ s'.st o = some q :=
  fun _ s _ _ s' _ hK o _ hq => (hk s s' hK o).trans hq

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k1Rest_row
#print axioms ProofFile.Honest.FirstThread.k1KeepsAt_rest
#print axioms ProofFile.Honest.FirstThread.k1KeepsAt_row
#print axioms ProofFile.Honest.FirstThread.k10Keeps_row
#print axioms ProofFile.Honest.FirstThread.head_tidy
#print axioms ProofFile.Honest.FirstThread.head_older_k1
#print axioms ProofFile.Honest.FirstThread.head_older_same
