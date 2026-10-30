-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/ConstrHeardCell.lean: the open item `constr m lookCallsHeard`
of the first chain's invariant passes over sub-protocol number 339, the switch of codes (kind K2) in
the output head's segment, at the invariant whose `keeps` is `kpBy fHead` (FHead.lean). No
definition.

ConstrHeardRides.lean asks that `keeps` leaves the field `out` of the verifier's state. At number
339 the clause is `K2Keeps` at a parameter that stands at the head (`head_keeps_hear`,
HeadKeepsAt.lean; `fHead_K2_head`, FHead.lean). Its authors' `K2Keeps.common`
(Johnson/Desc/K2/Honest/KeepsAt.lean) gives `K2Common`, whose second part says that `out` is the
same.

  `constr_cell_339`   the hypothesis `RidesPastAt` (Honest/Thread/Shares.lean) for the item, at
     every `m`

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * Nothing here shows that the item's statement holds at any state of a run.
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ConstrHeardRides
import Johnson.Desc.ProofFile.Honest.Thread.FHead
import Johnson.Desc.ProofFile.Honest.Thread.HeadKeepsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
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
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)

/-- The item `constr m lookCallsHeard` passes over sub-protocol number 339. -/
theorem constr_cell_339 (m : Nat) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread
      339 (Item.constr m .lookCallsHeard) :=
  ridesPastAt_constr_heard h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHead Zp cF G take P11 p12 P13)) w m
    fun s s' hK => by
      have a := (head_keeps_hear h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (fHead Zp cF G take P11 p12 P13) w (l := 24) (i := 1) (k := KindName.K2) (by decide) rfl
        s s').1 hK
      obtain ⟨q, -, k2⟩ := (fHead_K2_head Zp cF G take P11 p12 P13
        (p := { chain := 1, link := some 24, piece := 1 + 1, kind := KindName.K2 }) rfl s s').1 a
      exact k2.common.2.1

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.constr_cell_339
