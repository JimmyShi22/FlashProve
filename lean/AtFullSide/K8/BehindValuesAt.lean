-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/BehindValuesAt.lean: the table's test at the member behind the batching, number 14 l +
10 or 348, at each of the 25 segments, as one theorem. It joins the step's own clauses
(behind_values_att, _head, _lay, Honest/K9/BehindValues.lean) to the smallness test's tests on values
(k8_valsS_at_thread, k8_valsS_free_at). The rider of the first chain's list says what the layers'
clause asks of the state.

  own_of_rides        a layers' segment's own part is there behind its batching, from the rider
  k8_behind_valuesJ   ValuesJ at the member behind the batching of segment l

Limits. Said is read through hOk. The letter fall is read through two implications: where it says
nothing, the step's share of the fall and the smallness test's share are silent. That a thread
comes to such a stand is not shown.
-/
import AtFullSide.K8.TailAtThread
import Johnson.Desc.ProofFile.Honest.K9.BehindValues
import Johnson.Desc.ProofFile.Honest.Thread.CsHead
import Johnson.AtFull.Shape.SeatsNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8.Term
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims.Law.Tests (bareRun valsS)
open OnBytes.Maker (WholeD)
open OnBytes.Model.Stages (LinkH)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K8 (k8Share)
open ProofFile.Honest.K9 (freeSlotShare behind_values_att behind_values_head behind_values_lay)
open Johnson.AtFull.Shape (firstZA layers_named behind_named)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
  (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {Bk : ProverCoinCounts}
  {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (ν : Nat) (st : Nat → TS → Prop)
  (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- **A layers' segment's own part is there behind its batching.** -/
theorem own_of_rides {g : Nat} (hg : g < 12) {κ : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) Kp w).thread
      Said (14 * (2 * g) + 10) κ s m E) :
    ∃ a o, s.here = .lay a ∧ a.own = some o := by
  have hThr := hT.1
  unfold Thr at hThr
  obtain ⟨-, -, -, -, -, hR, -⟩ := hThr
  have hc := hR.2 ⟨28 * g + 5, 28 * g + 10, fun _ _ s => ∃ o, s.own? = some o⟩
    ((csHead_mem ν st R _).2 (Or.inr ⟨g, hg, rfl⟩)) (by show 28 * g + 5 ≤ _; omega)
    (by show _ ≤ 28 * g + 10; omega)
  obtain ⟨o, ho⟩ := hc
  unfold S.own? at ho
  split at ho
  · rename_i a ha
    exact ⟨a, o, ha, ho⟩
  · exact nomatch ho

include h hB in
/-- **The table's test at the member behind the batching of segment l.** -/
theorem k8_behind_valuesJ (hOk : ∀ b k m, Said b k m → SaidOk b k m) (J : Nat → TS → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) {l : Nat} (hl : l < 25)
    (hfree : ∀ u, VerifiableInference.Desc.K9.testsWhere Zp.p.X l 0 = some u → ∀ s ds,
      fall (14 * l + (if l = 24 then 11 else 9) + 1) s ds = none →
        freeSlotShare u.2.2.filled s = none)
    (hshare : ∀ Xl, Bs.G₀.built[l]? = some Xl → ∀ s ds,
      fall (14 * l + (if l = 24 then 11 else 9) + 1) s ds = none →
        k8Share (ProofFile.k8NU Bs.G₀ Xl) s = none) :
    ValuesJ (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) Kp w).thread
      Said J (firstZA (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀)) fall
      (14 * l + (if l = 24 then 11 else 9) + 1) := by
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨Bs', Xl, u, L, hB', hX, hw, -⟩ := behind_named h 24 (by omega) (by decide)
    obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans hB')
    exact behind_values_head h hw hX _ rfl (hfree u hw)
      fun κ s m E ds s₁ hT hf h₁ => k8_valsS_at_thread h hB H Q test carryX item n₁ n₂ 339 Vd
        (ridersOf (csHead ν st R)) Kp w Said hOk (by omega) hX hT (hshare Xl hX s ds hf) h₁
  · rw [if_neg h24] at hfree hshare ⊢
    rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · have hg : g < 12 := by omega
      obtain ⟨Bs', Xl, hp, u, L, hB', hX, hH, hw, -⟩ := layers_named h g hg
      obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans hB')
      obtain ⟨Bs₂, base, O⟩ := h.laid.opened
      obtain rfl : Bs = Bs₂ := Except.ok.inj (hB.symm.trans O.made)
      exact behind_values_lay h hg hw hX hH O.W _ rfl (hfree u hw)
        (fun κ s m E ds hT _ => own_of_rides h H Q test carryX item n₁ n₂ Vd ν st R Kp w Said hg hT)
        fun κ s m E ds s₁ s₂ hT hf h₁ h₂ => k8_valsS_free_at h hB H Q test carryX item n₁ n₂ 339 Vd
          (ridersOf (csHead ν st R)) Kp w Said hOk (by omega) hX
          (by rw [if_neg h24]; exact hT) (hshare Xl hX s ds hf) h₁ h₂
    · have hg : g < 12 := by omega
      obtain ⟨Bs', Xl, u, L, hB', hX, hw, -⟩ := behind_named h (2 * g + 1) (by omega) (by
        unfold IM.subAt
        rw [if_neg h24, if_neg (by omega)]
        decide)
      obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans hB')
      exact behind_values_att h hg hw hX _ rfl (hfree u hw)
        fun κ s m E ds s₁ hT hf h₁ => k8_valsS_at_thread h hB H Q test carryX item n₁ n₂ 339 Vd
          (ridersOf (csHead ν st R)) Kp w Said hOk (by omega) hX
          (by rw [if_neg h24]; exact hT) (hshare Xl hX s ds hf) h₁

end AtFullSide.K8.Term

#print axioms AtFullSide.K8.Term.own_of_rides
#print axioms AtFullSide.K8.Term.k8_behind_valuesJ
