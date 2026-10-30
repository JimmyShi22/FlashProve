-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/ConstrDigitsRides.lean: the open item `constr m lookDigits` of
the first chain's invariant passes over every sub-protocol. At this part the item's statement is the
library's `digitsPartK3` (Johnson/Desc/First/Look/K3FillDigits.lean), which reads the witness alone:
neither the verifier's state nor the strings. So the statement before a step and the statement after
it are the same by unfolding. One lemma, no definition.

The lemma has the form and the proof of `ridesPastAt_constr`
(Johnson/Goal/HonestTrace/ConstrAtThread.lean), which shows the same for four other parts.

  `ridesPastAt_constr_lookDigits`

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * Nothing here shows that the item's statement holds at any state of a run.
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.Shares

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item)
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

/-- The item `constr m lookDigits` passes over every sub-protocol. -/
theorem ridesPastAt_constr_lookDigits (b m : Nat) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.constr m .lookDigits) := by
  intro k s mm E s' ps v _ _ h0
  exact h0

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.ridesPastAt_constr_lookDigits
