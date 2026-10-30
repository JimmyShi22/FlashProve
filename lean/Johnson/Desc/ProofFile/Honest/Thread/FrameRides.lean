-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FrameRides.lean: open items of the first chain's invariant that
pass over a sub-protocol of the kind `frame`, from that kind's clause of `keeps` (`keepsFrame`,
Honest/Law/NoHouse/KeepsFrame.lean). At the front, at the seal and at a segment's place "laid" the
clause states that the state after the step is the state before it. At a segment's place "cleared"
it states that every oracle message is as it was but for its ledger (`keepsCleared`). No definition.

  1  `pileOne_strs`, `wrow_strs`   the statements of the items `pileOne` and `wrow` at the library's
     meaning `mgAll` do not read the strings
  2  `ridesPastAt_pileOne_eq`, `ridesPastAt_wrow_eq`   the two items pass over a sub-protocol whose
     `keeps` gives that the state is as it was
  3  `cleared_row`   under `keepsCleared` every message's first sample row is as it was
  4  `ridesPastAt_pinKept_cleared`   the item `pinKept m` passes over a sub-protocol whose `keeps`
     gives `keepsCleared`

Limits.
  * Parts 2 and 4: full size only, and only under the library's hypothesis `AtMgA` at the hash
    function `secondHashFunction` (FirstAt.lean says which that is).
  * That `keeps b` gives the clause is a hypothesis. This file shows it for no number `b`.
  * Nothing on the item `carry m`, which passes over the same sub-protocols: its statement is an
    argument of `lettersHead`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PinForward
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.KeepsFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (S Item Meaning)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll mgBase mgAll_pileOne mgAll_wrow CellsQ)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 Two statements that do not read the strings -/

section
variable {Xi P Tok : Type} {rows cols nR : Nat} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

theorem pileOne_strs (a : P × S) (y y' : Strs) (w : Wit (CellsQ rows cols) Tok MsgT)
    (h0 : (mgAll 𝔇 Mg).pileOne a y w) : (mgAll 𝔇 Mg).pileOne a y' w := by
  rw [mgAll_pileOne] at h0 ⊢
  exact h0

theorem wrow_strs (a : P × S) (y y' : Strs) (w : Wit (CellsQ rows cols) Tok MsgT)
    (h0 : (mgAll 𝔇 Mg).wrow a y w) : (mgAll 𝔇 Mg).wrow a y' w := by
  rw [mgAll_wrow] at h0 ⊢
  exact h0

end

/-! ## 3 Under `keepsCleared` -/

/-- Under `keepsCleared` every message's first sample row is as it was. -/
theorem cleared_row {take : Bool} {s t : S} (k : keepsCleared take s t) (o : Nat) :
    rowAt₀ t.st o = rowAt₀ s.st o := by
  have e := congrArg (Option.map fun x : OnBytes.Oracle => x.sampleRows)
    (k.2.2.2.2.2.2.2.2.2.2.2.1 o)
  exact rowAt₀_same (by simpa [Option.map_map, Function.comp_def] using e)

/-! ## 2 and 4 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The item `pileOne` passes over a sub-protocol whose `keeps` gives that the state is as it
was. -/
theorem ridesPastAt_pileOne_eq {b : Nat}
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      s' = s) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pileOne := by
  intro k s mm E s' ps v _ hK h0
  rw [hk s s' hK]
  exact pileOne_strs { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX }
    mgBase _ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v h0

/-- The item `wrow` passes over a sub-protocol whose `keeps` gives that the state is as it was. -/
theorem ridesPastAt_wrow_eq {b : Nat}
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      s' = s) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.wrow := by
  intro k s mm E s' ps v _ hK h0
  rw [hk s s' hK]
  exact wrow_strs { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX }
    mgBase _ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v h0

/-- The item `pinKept m` passes over a sub-protocol whose `keeps` gives `keepsCleared`. -/
theorem ridesPastAt_pinKept_cleared {b : Nat} (m : Nat) {take : Bool}
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      keepsCleared take s s') :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.pinKept m) :=
  ridesPastAt_pinKept_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m
    fun _ s _ _ s' _ hK o _ hq => (cleared_row (hk s s' hK) o).trans hq

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.pileOne_strs
#print axioms ProofFile.Honest.FirstThread.wrow_strs
#print axioms ProofFile.Honest.FirstThread.cleared_row
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pileOne_eq
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_wrow_eq
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pinKept_cleared
