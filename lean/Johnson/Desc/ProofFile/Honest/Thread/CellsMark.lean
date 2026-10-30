-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/CellsMark.lean: every clause of `fHead` (FHead.lean) at a place
of the first chain at the full size says that the state after the step has no mark (`s'.failed =
none`). So the item `unmarked` passes over every sub-protocol of the chain, at every condition
`keeps` that implies `fHead`. That is the column `hR` of the gathering (`owesS_head_form`,
GatherHeadForm.lean) at this item. No definition.

  1  `k3_k5_places`   a test on the written list of the 358 places: a place of the kind K3 is the
     place of a lookup in one of the 25 segments, and a place of the kind K5 names a segment whose
     half is below 12. The statement has no free variable. It is decided by the kernel's evaluation
     (`decide +kernel`), so it is counted apart from the other lemmas
  2  `k3_k5_places_control`   the test can fail: at 24 segments it fails
  3  `fHead_mark`   the clause at a place of the list gives `s'.failed = none`
  4  `head_rides_unmarked`   the item `unmarked` passes over the sub-protocol

The clauses of K3 and K5 speak only where the public part has a site, or an attention plan, for the
place. `site_digits_paid` (Johnson/Desc/ProofFile/Honest/K3/Law/Thread/RngWrittenHolds.lean, of
other authors) and `fHead_hA` (FHeadStaysAll.lean) give these. The test says which places are meant.

Limits.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHeadStaysAll
import Johnson.Desc.ProofFile.Honest.Thread.NoK14K15
import Johnson.Desc.ProofFile.Honest.Thread.PinRides
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RngWrittenHolds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

set_option maxRecDepth 1000000 in
/-- Which places of the written list have the kinds K3 and K5. -/
theorem k3_k5_places :
    (P5J.At.ps.all fun p =>
      (p.kind != KindName.K3 ||
        (List.range 25).any fun l => p == IM.k3Place l false || p == IM.k3Place l true) &&
      (p.kind != KindName.K5 || (p.link.isSome && decide (p.link.getD 99 / 2 < 12)))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at 24 segments the same test fails. -/
theorem k3_k5_places_control :
    (P5J.At.ps.all fun p =>
      (p.kind != KindName.K3 ||
        (List.range 24).any fun l => p == IM.k3Place l false || p == IM.k3Place l true) &&
      (p.kind != KindName.K5 || (p.link.isSome && decide (p.link.getD 99 / 2 < 12)))) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- **The clause of `fHead` at a place of the list gives `s'.failed = none`.** -/
theorem fHead_mark (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) {b : Nat} {p : Place}
    (hp : P5J.At.ps[b]? = some p) (hk : p.kind ≠ KindName.frame) (s s' : TS)
    (ha : fHead Zp cF G take P11 p12 P13 p.kind p s s') : s'.failed = none := by
  have hm : p ∈ P5J.At.ps := List.mem_of_getElem? hp
  have t := Bool.and_eq_true_iff.1 (List.all_eq_true.1 k3_k5_places p hm)
  cases hκ : p.kind <;> rw [hκ] at ha
  case frame => exact absurd hκ hk
  case K1 =>
    change (if p.link = some 0 ∧ p.piece = 1 then _ else if p.link = none ∧ p.piece = 4 then _
      else _) at ha
    split at ha
    · obtain ⟨m, -, ho⟩ := ha
      exact ho.1.1
    · split at ha
      · exact ha.2
      · have hc := ha.1
        unfold ProofFile.Honest.K1.K1KeepsAt at hc
        split at hc
        · exact hc.2
        · exact hc.2
        · exact hc.2
        · exact hc.2
        · exact hc.elim
  case K2 =>
    cases hl : p.link with
    | none =>
      obtain ⟨q, hq, hK⟩ := (fHead_K2_finish Zp cF G take P11 p12 P13 hl s s').1 ha
      unfold VerifiableInference.Desc.K2.Honest.K2Keeps at hK
      rw [hq] at hK
      exact hK.2.2
    | some l =>
      by_cases h24 : l = 24
      · subst h24
        obtain ⟨q, hq, hK⟩ := (fHead_K2_head Zp cF G take P11 p12 P13 hl s s').1 ha
        unfold VerifiableInference.Desc.K2.Honest.K2Keeps at hK
        rw [hq] at hK
        exact hK.2.2
      · obtain ⟨m, -, ho⟩ := (fHead_K2_link Zp cF G take P11 p12 P13 hl h24 s s').1 ha
        exact ho.1.1
  case K3 =>
    have t1 := t.1
    rw [hκ, show (KindName.K3 != KindName.K3) = false from rfl, Bool.false_or] at t1
    obtain ⟨l, hl, hq⟩ := List.any_eq_true.1 t1
    have hl' := List.mem_range.1 hl
    have ha' : ProofFile.Honest.K3.Law.AtThr.k3KeepsAt Zp p s s' := ha
    rcases Bool.or_eq_true_iff.1 hq with hq | hq
    · obtain ⟨u, hu, -, -, e3, -⟩ := ProofFile.Honest.K3.Law.AtThr.site_digits_paid h l hl' false
      exact (ha' u hu (e3.trans (eq_of_beq hq).symm)).1
    · obtain ⟨u, hu, -, -, e3, -⟩ := ProofFile.Honest.K3.Law.AtThr.site_digits_paid h l hl' true
      exact (ha' u hu (e3.trans (eq_of_beq hq).symm)).1
  case K4 => exact (show ProofFile.Honest.K4.K4KeepsM s s' from ha).2
  case K5 =>
    have t2 := t.2
    rw [hκ, show (KindName.K5 != KindName.K5) = false from rfl, Bool.false_or] at t2
    obtain ⟨t3, t4⟩ := Bool.and_eq_true_iff.1 t2
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 t3
    rw [hl] at t4
    obtain ⟨a, hA⟩ := fHead_hA h (l / 2) (of_decide_eq_true t4)
    have ha' : H2K5.Honest.K5KeepsAt (P5J.At.X Zp) p s s' := ha
    exact (ha' l a hl hA).1
  case K6 => exact (show VerifiableInference.Desc.Kinds.Head.Honest.K6Keeps s s' from ha).1
  case K7 =>
    obtain ⟨m, -, ho⟩ := (show K7KeepsAt G p s s' from ha).2
    exact ho.1
  case K8 => exact (show VerifiableInference.Desc.First.K8.Honest.K8KeepsM s s' from ha).2
  case K9 => exact (show ProofFile.Honest.K9.k9KeepsAt cF Zp p s s' from ha).1
  case K10 => exact (show ProofFile.Honest.K10.YesFree.K10Keeps s s' from ha).2
  case K11 =>
    exact (show Johnson.Desc.First.ForkMerge.Returns.K11KeepsYesAt P11 p s s' from ha).2.1.2
  case K12 => exact (show ProofFile.Honest.Sh.K12KeepsFirst p12 s s' from ha).1
  case K13 => exact (show VerifiableInference.Desc.K13.Honest.K13KeepsAll P13 s s' from ha).1.1
  case K14 =>
    have u := List.all_eq_true.1 places_no_k14_k15 p hm
    rw [hκ] at u
    exact absurd u (by decide)
  case K15 =>
    have u := List.all_eq_true.1 places_no_k14_k15 p hm
    rw [hκ] at u
    exact absurd u (by decide)

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The item `unmarked` passes over every sub-protocol that is not of the kind `frame`**, at every
`Kp` that implies `fHead`. -/
theorem head_rides_unmarked (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where)
    (hle : ∀ p s s', Kp p s s' → kpBy (fHead Zp cF G take P11 p12 P13) p s s') {b : Nat}
    {p : Place} (hp : P5J.At.ps[b]? = some p) (hk : p.kind ≠ KindName.frame) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.unmarked :=
  ridesPastAt_unmarked h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w fun s s' hK =>
    fHead_mark h G take P11 p12 P13 hp hk s s'
      (hle p s s' ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hp s s').1 hK))

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k3_k5_places
#print axioms ProofFile.Honest.FirstThread.k3_k5_places_control
#print axioms ProofFile.Honest.FirstThread.fHead_mark
#print axioms ProofFile.Honest.FirstThread.head_rides_unmarked
