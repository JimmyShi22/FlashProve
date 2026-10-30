-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/PinForwardSend.lean: the hypothesis of PinForward.lean, "a first
sample row that the statement holds before the step is still there after it", for the sub-protocol
after the segments at which the message W is sent (kind K1) and a step of kind K13 follows. The
clause of `keeps` there has a state between the two steps (`fHead`, FHead.lean): `K1SendKeeps` holds
up to it (Honest/K1/Law/Keeps.lean) and `K13RowsKeeps` from it
(Johnson/Desc/K13/Honest/RowsKeeps.lean). No definition.

  1  `k1Send_old`   `K1SendKeeps` gives the library's relation "the older messages stay"
     (`K1.OldMsgs`): its text has every older message as it was, field for field
  2  `k13Rows_old`   `K13RowsKeeps` gives the same relation: by `K13RowsKeeps.same` every message
     keeps its shape, its mark and its sample rows
  3  `send_rows_old`, `send_rows_row`   the two steps together
  4  `ridesPastAt_pinI_send`   the item `pinI` passes over a sub-protocol whose `keeps` gives the
     two clauses with a state between

Limits.
  * Part 4: full size only, and only under the library's hypothesis `AtMgA` at the hash function
    `secondHashFunction` (FirstAt.lean says which that is).
  * Part 4 takes as a hypothesis that `keeps b` gives the two clauses. This file shows that for no
    number `b`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PinForward
import Johnson.Desc.ProofFile.Honest.K1.Law.Keeps
import Johnson.Desc.K13.Honest.RowsKeeps
import Johnson.Desc.K13.Law.AtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-- Under `K1SendKeeps` the older messages stay. -/
theorem k1Send_old {s m : S} (k : ProofFile.Honest.K1.K1SendKeeps s m) :
    VerifiableInference.Desc.K1.OldMsgs s.st m.st :=
  ⟨k.1.2.2.2.2.1.1.1.1.1, fun j hj => by rw [k.2.2.2.2.1 j hj]⟩

/-- Under `K13RowsKeeps` the older messages stay. -/
theorem k13Rows_old {P : VerifiableInference.Desc.K13.Where} {m s' : S}
    (k : VerifiableInference.Desc.K13.Honest.K13RowsKeeps P m s') :
    VerifiableInference.Desc.K1.OldMsgs m.st s'.st :=
  VerifiableInference.Desc.K1.old_of_same (VerifiableInference.Desc.K13.Law.sameMsgs_of_all k.same)

/-- Under the two clauses with a state between, the older messages stay. -/
theorem send_rows_old {P : VerifiableInference.Desc.K13.Where} {s s' : S}
    (k : ∃ m, ProofFile.Honest.K1.K1SendKeeps s m ∧
      VerifiableInference.Desc.K13.Honest.K13RowsKeeps P m s') :
    VerifiableInference.Desc.K1.OldMsgs s.st s'.st := by
  obtain ⟨m, k1, k2⟩ := k
  exact (k1Send_old k1).trans (k13Rows_old k2)

/-- So a first sample row that is there stays. -/
theorem send_rows_row {P : VerifiableInference.Desc.K13.Where} {s s' : S}
    (k : ∃ m, ProofFile.Honest.K1.K1SendKeeps s m ∧
      VerifiableInference.Desc.K13.Honest.K13RowsKeeps P m s')
    {o : Nat} {q : OnBytes.Row} (hq : rowAt₀ s.st o = some q) : rowAt₀ s'.st o = some q :=
  rowAt₀_old (send_rows_old k) hq

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The item `pinI` passes over a sub-protocol whose `keeps` gives `K1SendKeeps` up to a state
between and `K13RowsKeeps` from it. -/
theorem ridesPastAt_pinI_send {b : Nat} {P : VerifiableInference.Desc.K13.Where}
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ∃ m, ProofFile.Honest.K1.K1SendKeeps s m ∧
        VerifiableInference.Desc.K13.Honest.K13RowsKeeps P m s') :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pinI :=
  ridesPastAt_pinI_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    fun _ s _ _ s' _ hK _ _ hq => send_rows_row (hk s s' hK) hq

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k1Send_old
#print axioms ProofFile.Honest.FirstThread.k13Rows_old
#print axioms ProofFile.Honest.FirstThread.send_rows_old
#print axioms ProofFile.Honest.FirstThread.send_rows_row
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pinI_send
