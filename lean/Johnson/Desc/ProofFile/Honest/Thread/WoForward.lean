-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/WoForward.lean: the open item `wo m` of the first chain's
invariant passes over a sub-protocol, from the state before the step to the state after it. The item
states that the row which the frame's reader of the pending row gives at the verifier's state, if it
gives one, holds of the witness (`First.FillP1.woAt`, Johnson/Top/H0/Fill/FillP1.lean). No
definition.

What the statement reads of the state. The reader of the pending row (`Walk.Law.rowAt`) reads what
the open segment has left for its row, the field `out`, and the ledger of the message of the index
masks. The witness is read by the reader of the item `pile` (`K13.Law.rwBook`). Every mask entry
that the row names belongs to the message of the index masks (`K1.rowAt_onLedger`,
Johnson/Desc/K1/Law/HasRowAtLater.lean). So it is enough that the reader of the pending row gives
the same answer at both states, and that the two readers of the witness agree at that message
(`rwBook_agree`, PileForward.lean).

The library shows the opposite direction (`K1.wo_back`, HasRowAtLater.lean; `wo_back_k10`,
Johnson/Desc/First/Link/Law/RidersLight.lean; `mgAll_wo_back`,
Johnson/Desc/Sound/MgAt/K3RidesDig.lean). The step in these proofs is an equivalence
(`K13.Law.holds_congr`).

For a sub-protocol that leaves the statement, the list of commitment trees, `out` and what is left
for the row, the authors of kind K4 have the item at `lettersHead` (`K4.k4_ridesPastAtS_wo_head`,
Honest/K4/Law/WoRidesHead.lean, over `K4.woAt_rides`, Honest/K4/Law/WoRides.lean). This file is for
the sub-protocols that turn the statement or the list of trees, where their file says that it does
not help.

  1  `wo_older`   the statement at the library's meaning `mgAll`
  2  `ridesPastAt_wo_older`   the hypothesis `RidesPastAt` (Honest/Thread/Shares.lean) for the item
     at `lettersHead`, at every sub-protocol number `b`. Its hypothesis may use the invariant before
     the step (`Thr`)

Limits.
  * Part 2: full size only, and only under the library's hypothesis `AtMgA` at the hash function
    `secondHashFunction` (FirstAt.lean says which that is).
  * The hypotheses on the two states have to be shown for each kind. This file shows them for no
    kind and at no state.
  * The witness is the same before and after the step.
  * Nothing here shows that the item's statement holds at any state of a run.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PileForward
import Johnson.Desc.K1.Law.HasRowAtLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (S Item Meaning BookKept)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll mgBase mgAll_wo CellsQ)
open VerifiableInference.Desc.K13.Law (AgreeAt holds_congr rwBook)
open Johnson.Desc.First.Walk.Law (rowAt leftOf)
open OnBytes.Means (Extends)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 At the library's meaning -/

section
variable {Xi P Tok : Type} {rows cols nR : Nat} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  {s s' : S}

/-- The statement of `wo m` passes from `s` to `s'`. -/
theorem wo_older (m : Nat)
    (hrow : rowAt 𝔇.d1.lay (𝔇.d1.ncl m) 𝔇.d1.lin s' = rowAt 𝔇.d1.lay (𝔇.d1.ncl m) 𝔇.d1.lin s)
    (hlt : s.out.indexMasks < s.st.oracles.size) (hE : Extends s.st s'.st) (hB : BookKept s s')
    (z : P) (y y' : Strs) (w : Wit (CellsQ rows cols) Tok MsgT)
    (h0 : (mgAll 𝔇 Mg).wo m (z, s) y w) : (mgAll 𝔇 Mg).wo m (z, s') y' w := by
  rw [mgAll_wo] at h0 ⊢
  have hA : AgreeAt s.out.indexMasks (𝔇.rw13 (z, s') w) (𝔇.rw13 (z, s) w) :=
    rwBook_agree 𝔇.arr 𝔇.mat13 (z, s) (z, s') w s.out.indexMasks hE.codes
      (shape_of_extends hE hlt) (hB _ hlt).1 (hB _ hlt).2
  intro r hr
  have hr' : rowAt 𝔇.d1.lay (𝔇.d1.ncl m) 𝔇.d1.lin s = some r := by
    rw [← hrow]
    exact hr
  exact (holds_congr OnBytes.Model.Reading.gl
    (VerifiableInference.Desc.K1.rowAt_onLedger hr') hA).2 (h0 r hr')

end

/-! ## 2 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The item `wo m` passes over sub-protocol `b` if, wherever the invariant holds before the step,
the reader of the pending row gives the same answer after the step, the message of the index masks
is there, the statement after the step extends the one before it, and every message keeps its place
and the tree there. -/
theorem ridesPastAt_wo_older {b : Nat} (m : Nat)
    (hk : ∀ k s mm E s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s mm E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      rowAt h.𝔇.d1.lay (h.𝔇.d1.ncl m) h.𝔇.d1.lin s' =
          rowAt h.𝔇.d1.lay (h.𝔇.d1.ncl m) h.𝔇.d1.lin s ∧
        s.out.indexMasks < s.st.oracles.size ∧ Extends s.st s'.st ∧ BookKept s s') :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.wo m) := by
  intro k s mm E s' ps v hA hK h0
  obtain ⟨h1, h2, h3, h4⟩ := hk k s mm E s' hA hK
  exact wo_older { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX } mgBase m
    h1 h2 h3 h4 mm.st.input.x.pub
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v h0

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.wo_older
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_wo_older
