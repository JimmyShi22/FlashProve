-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/PileFirst.lean: the open item `pile` of the first chain's
invariant passes over sub-protocol number 2, the opening of the first segment (kind K1) with the
frame's step "opened" joined after it. PileForward.lean does not reach this number: it asks that the
message of the index masks is there, and that message is sent by this sub-protocol. Here the reason
is another one. Before number 2 there is no pending row, the step adds none, and `pile` states
something of each pending row only. No definition.

  1  `pile_of_noRows`   at a state without a pending row the statement of `pile` holds, at the
     library's meaning `mgAll`
  2  `first_opened_rows`   under `K1FirstKeeps` (Honest/K1/Law/Keeps.lean) up to a state between
     and `keepsOpenedR` (OpenedKeepsR.lean) from it, the pending rows after the step are the list
     `out.pending` before it
  3  `takenAt_two`   the library's count of the rows that are pending before a border
     (`P1L20.takenAt`) is 0 at border 2
  4  `ridesPastAt_pile_noRows`, `ridesPastAt_pile_two`   the hypothesis `RidesPastAt`
     (Honest/Thread/Shares.lean) for `pile`: at every number `b` at which that count is 0, and at 2

Limits.
  * Part 4: full size only, and only under the library's hypothesis `AtMgA` at the hash function
    `secondHashFunction` (FirstAt.lean says which that is).
  * Part 4 takes as a hypothesis that `keeps b` gives the two clauses with a state between. This
    file shows that for no number `b`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PileAtHead
import Johnson.Desc.ProofFile.Honest.Thread.Shares
import Johnson.Desc.ProofFile.Honest.Thread.OpenedKeepsR
import Johnson.Desc.ProofFile.Honest.K1.Law.Keeps
import Johnson.Desc.K13.Law.ReaderByBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (S Item Meaning)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll mgBase mgAll_pile CellsQ)
open VerifiableInference.Desc.K13.Law (Holds rwBook)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 Without a pending row -/

/-- At a state without a pending row the statement of `pile` holds. -/
theorem pile_of_noRows {Xi P Tok : Type} {rows cols nR : Nat} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
    {s' : S} (e : s'.rows = []) (z : P) (y' : Strs) (w : Wit (CellsQ rows cols) Tok MsgT) :
    (mgAll 𝔇 Mg).pile (z, s') y' w := by
  rw [mgAll_pile]
  show ∀ r ∈ s'.rows, Holds _ (rwBook 𝔇.arr 𝔇.mat13 (z, s') w) r
  rw [e]
  intro r hr
  cases hr

/-! ## 2 The pending rows after the step -/

/-- Under the two clauses with a state between, the pending rows after the step are the list
`out.pending` before it. -/
theorem first_opened_rows {l : Nat} {s s' : S}
    (k : ∃ m, ProofFile.Honest.K1.K1FirstKeeps s m ∧ keepsOpenedR l m s') :
    s'.rows = s.out.pending := by
  obtain ⟨m, k1, k2⟩ := k
  have e : m.rows = m.out.pending := by simp [S.rows, k1.2.2]
  rw [k2.2, e, k1.1.2.1]

/-! ## 3 The library's count at border 2 -/

/-- No row is pending before border 2, by the library's count. -/
theorem takenAt_two : P1L20.takenAt 2 = 0 := by decide

/-! ## 4 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The item `pile` passes over a sub-protocol before which the library counts no pending row and
whose `keeps` gives the two clauses with a state between. -/
theorem ridesPastAt_pile_noRows {b l : Nat} (hb : b ≤ cF.blocksInOrder.length) (h355 : b ≤ 355)
    (h0 : P1L20.takenAt b = 0)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ∃ m, ProofFile.Honest.K1.K1FirstKeeps s m ∧ keepsOpenedR l m s') :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pile := by
  intro k s mm E s' ps v hA hK _
  have hp := head_pile h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb h355 hA
  rw [h0] at hp
  have e : s'.rows = [] := by
    rw [first_opened_rows (hk s s' hK)]
    exact List.eq_nil_of_length_eq_zero hp
  exact pile_of_noRows
    { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX } mgBase e
    mm.st.input.x.pub
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v

/-- The same at number 2, from the clause in the form that `fHead` has there. -/
theorem ridesPastAt_pile_two (hb : 2 ≤ cF.blocksInOrder.length)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 2 s s' →
      ∃ m, (ProofFile.Honest.K1.K1FirstKeeps s m ∧ ProofFile.Honest.K1.K1Out s m) ∧ keepsOpenedR 0 m s') :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 2 Item.pile :=
  ridesPastAt_pile_noRows h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb (by decide) takenAt_two
    fun s s' hK =>
      let ⟨m, k1, k2⟩ := hk s s' hK
      ⟨m, k1.1, k2⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.pile_of_noRows
#print axioms ProofFile.Honest.FirstThread.first_opened_rows
#print axioms ProofFile.Honest.FirstThread.takenAt_two
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pile_noRows
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pile_two
