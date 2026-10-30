-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/CellsQuiet.lean: at the places of the first chain at the full
size whose kind is K3, K4, K6 or K8, the clause of `fHead` (FHead.lean) leaves the statement, the
book of trees and the rows on the table as they were (ArmsQuiet.lean). So the items `pile`, `pinI`,
`pin` and `row` pass over these 88 sub-protocols, at every condition `keeps` that implies `fHead`.
That is a part of the column `hR` of the gathering (`owesS_head_form`, GatherHeadForm.lean). No
definition.

  1  `rides_of_quiet`   general in the number: where `keeps` gives the three equations, the four
     sorts of item pass
  2  `fHead_quiet`   the clause at a place of one of the four kinds gives the three equations
  3  `head_rides_quiet`   the four sorts of item pass over the sub-protocol at such a place

At K3 the clause speaks through the public part's site for the place. `site_digits_paid`
(Johnson/Desc/ProofFile/Honest/K3/Law/Thread/RngWrittenHolds.lean), `quiet_digits_head` and
`quiet_head_head` (QuietAtLink.lean, QuietAtHeadLink.lean there), all of other authors, say which of
the clause's three cases holds. `k3_k5_places` (CellsMark.lean) says which places are meant.

Limits.
  * Not treated: the other nine kinds.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.CellsMark
import Johnson.Desc.ProofFile.Honest.Thread.ArmsQuiet
import Johnson.Desc.ProofFile.Honest.Thread.RowPileRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item RowClass)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.K3.Law.AtThr (site_digits_paid quiet_digits_head quiet_head_head)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- **The clause of `fHead` at a place of the kind K3, K4, K6 or K8 gives the three equations.** -/
theorem fHead_quiet (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) {b : Nat} {p : Place}
    (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K3 ∨ p.kind = KindName.K4 ∨ p.kind = KindName.K6 ∨
      p.kind = KindName.K8) (s s' : TS)
    (ha : fHead Zp cF G take P11 p12 P13 p.kind p s s') :
    s'.st = s.st ∧ s'.book = s.book ∧ s'.rows = s.rows := by
  rcases hk with hκ | hκ | hκ | hκ <;> rw [hκ] at ha
  · have t1 := (Bool.and_eq_true_iff.1
      (List.all_eq_true.1 k3_k5_places p (List.mem_of_getElem? hp))).1
    rw [hκ, show (KindName.K3 != KindName.K3) = false from rfl, Bool.false_or] at t1
    obtain ⟨l, hl, hq⟩ := List.any_eq_true.1 t1
    have hl' := List.mem_range.1 hl
    have ha' : ProofFile.Honest.K3.Law.AtThr.k3KeepsAt Zp p s s' := ha
    rcases Bool.or_eq_true_iff.1 hq with hq | hq
    · obtain ⟨u, hu, -, e2, e3, -⟩ := site_digits_paid h l hl' false
      exact k3Calls_quiet ((ha' u hu (e3.trans (eq_of_beq hq).symm)).2.1 e2)
    · obtain ⟨u, hu, e1, e2, e3, -⟩ := site_digits_paid h l hl' true
      have hc := ha' u hu (e3.trans (eq_of_beq hq).symm)
      by_cases h24 : l = 24
      · subst h24
        exact k3Head_quiet (hc.2.2.2 e2 (by rw [e1]; exact quiet_head_head h))
      · obtain ⟨used, claims, hqd⟩ := quiet_digits_head h l (by omega)
        exact k3Digits_quiet (hc.2.2.1 e2 used claims (by rw [e1]; exact hqd))
  · exact k4_quiet (show ProofFile.Honest.K4.K4KeepsM s s' from ha).1
  · exact k6_quiet (show VerifiableInference.Desc.Kinds.Head.Honest.K6Keeps s s' from ha)
  · exact k8_quiet (show VerifiableInference.Desc.First.K8.Honest.K8KeepsM s s' from ha).1

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- Where `keeps` gives the three equations, the four sorts of item pass. -/
theorem rides_of_quiet {b : Nat}
    (hq : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      s'.st = s.st ∧ s'.book = s.book ∧ s'.rows = s.rows) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pile ∧
      RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pinI ∧
      (∀ m t, RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
        (Item.pin m t)) ∧
      ∀ m c, RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
        (Item.row m c) :=
  ⟨ridesPastAt_pile h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hq,
    ridesPastAt_pinI h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w fun s s' hK => (hq s s' hK).1,
    fun m t => ridesPastAt_pin h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m t fun s s' hK =>
      (hq s s' hK).1,
    fun m c => ridesPastAt_row h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m c fun s s' hK =>
      ⟨(hq s s' hK).1, (hq s s' hK).2.1⟩⟩

/-- **The items `pile`, `pinI`, `pin` and `row` pass over a sub-protocol of the kind K3, K4, K6 or
K8**, at every `Kp` that implies `fHead`. -/
theorem head_rides_quiet (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where)
    (hle : ∀ p s s', Kp p s s' → kpBy (fHead Zp cF G take P11 p12 P13) p s s') {b : Nat}
    {p : Place} (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K3 ∨ p.kind = KindName.K4 ∨ p.kind = KindName.K6 ∨
      p.kind = KindName.K8) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pile ∧
      RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pinI ∧
      (∀ m t, RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
        (Item.pin m t)) ∧
      ∀ m c, RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
        (Item.row m c) :=
  rides_of_quiet h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w fun s s' hK =>
    fHead_quiet h G take P11 p12 P13 hp hk s s'
      (hle p s s' ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hp s s').1 hK))

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.fHead_quiet
#print axioms ProofFile.Honest.FirstThread.rides_of_quiet
#print axioms ProofFile.Honest.FirstThread.head_rides_quiet
