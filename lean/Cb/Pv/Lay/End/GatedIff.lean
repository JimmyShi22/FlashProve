-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/GatedIff.lean: the pull-backs of the ledgers of the claims on the gated products and
of the merge hold exactly if the output claims of the three sumchecks hold.

Cb/Pv/Lay/End/GatedShare.lean and Cb/Pv/Lay/End/MergeShare.lean conclude the output claims from the
ledgers. This file shows the converses. So the ledgers ask no more than the output claims, and at an
output whose claims hold the two theorems' premises on the ledger and the pending row are met,
whatever the cells and the entries are. Their premises on names, forms and sizes stay.

Main theorems.
  val_cEnd_shift: a claim on an end value is worth c less if the shown value is c less.
  gated_last_conv: on entries with true tables, GatedLast gives that the four claims are worth 0.
  gated_bill_conv: the rows on the four end values give GatedLast at the letters off the outputs.
  gated_pull_iff, merge_pull_iff, merge_pull_first_iff.

Limits: as the two files named.


-/
import Cb.Pv.Lay.End.GatedShare
import Cb.Pv.Lay.End.MergeShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End.Gated

open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model.FFSeg (Dim Cell slV upV slV' upV' lF lFe)
open Blocks (ext Form)

section Claims

variable {E J : Type} [Field E] [Fintype J] [DecidableEq J]

/-- A claim on an end value is worth c less if the shown value is c less. -/
theorem val_cEnd_shift (sh c β : E) (m : J) (u : ℕ → ℕ → ℕ → J) (r : ℕ → E) (g rows blocks : ℕ)
    (lamOf : ℕ → ℕ) (first : ℕ) (y : J → E) :
    Form.val y (cEnd (sh - c) β m u r g rows blocks lamOf first) =
      Form.val y (cEnd sh β m u r g rows blocks lamOf first) - c := by
  unfold cEnd hid
  rw [map_add, map_add, map_sub, map_sub, Form.val_const, Form.val_const]
  ring

/-- On entries with true tables, GatedLast gives that the four claims are worth 0. -/
theorem gated_last_conv (N : GatedNames J) (e : GatedE E) (D : Dim) (t : Cell → E) (s : ℕ)
    (y : J → E) (h1 : s ≤ lF D) (h2 : s ≤ lFe D) (hfe : D.fe = 2 ^ lFe D)
    (T : GatedTables N e D t s y) (L : GatedLast N e D t y) :
    ∀ f ∈ gatedCl N e D s, Form.val y f = 0 := by
  obtain ⟨v1, e1⟩ : ∃ v, v = Form.val y (cEnd e.shL5 e.β5 N.mL5 N.uS5 e.r5 (D.lL + lF D - s)
    (2 ^ D.lL) (2 ^ (lF D - s)) id 0) := ⟨_, rfl⟩
  obtain ⟨v2, e2⟩ : ∃ v, v = Form.val y (cEnd e.shR5 e.β5 N.mR5 N.uU5 e.r5 (D.lL + lF D - s)
    (2 ^ D.lL) (2 ^ (lF D - s)) id 0) := ⟨_, rfl⟩
  obtain ⟨v3, e3⟩ : ∃ v, v = Form.val y (cEnd e.shL6 e.β6 N.mL6 N.uS6 e.r6
    (D.lL - 1 + lFe D - s) (2 ^ (D.lL - 1)) (2 ^ (lFe D - s)) (fun lm => 2 * lm + 1)
    (2 ^ (lFe D - s))) := ⟨_, rfl⟩
  obtain ⟨v4, e4⟩ : ∃ v, v = Form.val y (cEnd e.shR6 e.β6 N.mR6 N.uU6 e.r6
    (D.lL - 1 + lFe D - s) (2 ^ (D.lL - 1)) (2 ^ (lFe D - s)) (fun lm => 2 * lm + 1)
    (2 ^ (lFe D - s))) := ⟨_, rfl⟩
  have L' := gated_last N ⟨e.r5, e.r6, e.β5, e.β6, e.shL5 - v1, e.shR5 - v2, e.shL6 - v3,
    e.shR6 - v4⟩ D t s y h1 h2 hfe ⟨T.s5, T.u5, T.s6, T.u6⟩ (fun f hf => by
      unfold gatedCl at hf
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl
      · rw [val_cEnd_shift, ← e1, sub_self]
      · rw [val_cEnd_shift, ← e2, sub_self]
      · rw [val_cEnd_shift, ← e3, sub_self]
      · rw [val_cEnd_shift, ← e4, sub_self])
  have z1 : v1 = 0 := by
    have a := L'.L5
    have b := L.L5
    have a' : e.shL5 - v1 - e.β5 * y N.mL5 = ext (D.lL + lF D + D.lT) (slV D t) e.r5 := a
    linear_combination b - a'
  have z2 : v2 = 0 := by
    have a := L'.R5
    have b := L.R5
    have a' : e.shR5 - v2 - e.β5 * y N.mR5 = ext (D.lL + lF D + D.lT) (upV D t) e.r5 := a
    linear_combination b - a'
  have z3 : v3 = 0 := by
    have a := L'.L6
    have b := L.L6
    have a' : e.shL6 - v3 - e.β6 * y N.mL6 = ext (D.lL - 1 + lFe D + D.lT) (slV' D t) e.r6 := a
    linear_combination b - a'
  have z4 : v4 = 0 := by
    have a := L'.R6
    have b := L.R6
    have a' : e.shR6 - v4 - e.β6 * y N.mR6 = ext (D.lL - 1 + lFe D + D.lT) (upV' D t) e.r6 := a
    linear_combination b - a'
  intro f hf
  unfold gatedCl at hf
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · rw [← e1, z1]
  · rw [← e2, z2]
  · rw [← e3, z3]
  · rw [← e4, z4]

end Claims

section Bill

variable {E : Type} [Field E] [Fintype E] (P : FootPar0 E) {J₂ : Type}

/-- The rows on the four end values give GatedLast at the letters off the outputs. -/
theorem gated_bill_conv (U : GatedReads J₂) (o5 : P.gp.toSum.T.par.Out)
    (o6 : P.rt.L.toSum.T.par.Out) (m : P.J → E) (u : J₂ → E) (h1 : 1 ≤ P.D.lL)
    (h5 : ∀ b, P.gp.toSum.T.par.EHolds o5 m b) (h6 : ∀ b, P.rt.L.toSum.T.par.EHolds o6 m b) :
    GatedLast (gNamesAt P U) (gatedEAt P o5 o6) P.D (P.rd m) (Sum.elim m u) := by
  have hk : P.D.lL - 1 + (lFe P.D + P.D.lT) = P.D.lL - 1 + lFe P.D + P.D.lT :=
    (Nat.add_assoc _ _ _).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : ext (P.D.lL + lF P.D + P.D.lT) (slV P.D (P.rd m)) (gatedEAt P o5 o6).r5 +
        m (P.c5 false) * (gatedEAt P o5 o6).β5 = o5.vals false :=
      (ProdL.kval_iff P.gp o5 m false).1 (h5 false)
    show o5.vals false - (gatedEAt P o5 o6).β5 * m (P.c5 false) = _
    rw [← h]
    ring
  · have h : ext (P.D.lL + lF P.D + P.D.lT) (upV P.D (P.rd m)) (gatedEAt P o5 o6).r5 +
        m (P.c5 true) * (gatedEAt P o5 o6).β5 = o5.vals true :=
      (ProdL.kval_iff P.gp o5 m true).1 (h5 true)
    show o5.vals true - (gatedEAt P o5 o6).β5 * m (P.c5 true) = _
    rw [← h]
    ring
  · have hc : ext (P.D.lL - 1 + (lFe P.D + P.D.lT)) (P.rt.L.vm o6.st m false)
        (gatedEAt P o5 o6).r6 =
        ext (P.D.lL - 1 + (lFe P.D + P.D.lT)) (slV' P.D (P.rd m)) (gatedEAt P o5 o6).r6 := by
      refine Blocks.ext_congr (fun X hX => ?_) _
      show (if P.D.ne * 2 ^ (lFe P.D + P.D.lT) ≤ X then 0 else slV' P.D (P.rd m) X) = _
      rw [if_neg]
      rw [ne_pow P h1, ← pow_add]
      omega
    have h : ext (P.D.lL - 1 + (lFe P.D + P.D.lT)) (P.rt.L.vm o6.st m false)
        (gatedEAt P o5 o6).r6 + m (P.c6 false) * (gatedEAt P o5 o6).β6 = o6.vals false :=
      (ProdL.kval_iff P.rt.L o6 m false).1 (h6 false)
    rw [hc, hk] at h
    show o6.vals false - (gatedEAt P o5 o6).β6 * m (P.c6 false) = _
    rw [← h]
    ring
  · have h : ext (P.D.lL - 1 + (lFe P.D + P.D.lT)) (upV' P.D (P.rd m)) (gatedEAt P o5 o6).r6 +
        m (P.c6 true) * (gatedEAt P o5 o6).β6 = o6.vals true :=
      (ProdL.kval_iff P.rt.L o6 m true).1 (h6 true)
    rw [hk] at h
    show o6.vals true - (gatedEAt P o5 o6).β6 * m (P.c6 true) = _
    rw [← h]
    ring

variable {Nm : Type} [Fintype J₂] [DecidableEq P.J] [DecidableEq J₂]

/-- The pull-back of the ledger of the six claims holds exactly if all output claims of the two
product layers' sumchecks hold. -/
theorem gated_pull_iff
    (hrd : ∀ (a b : E) (m m' : P.J → E) (c : Cell),
      P.rd (fun j => a * m j + b * m' j) c = a * P.rd m c + b * P.rd m' c)
    (Y : LateLay Nm J₂) (ι : GatedNm → Nm) (fm : Nm → TWhole.Aff E P.J)
    (o5 : P.gp.toSum.T.par.Out) (o6 : P.rt.L.toSum.T.par.Out) (m : P.J → E) (s : ℕ)
    (h1 : 1 ≤ P.D.lL) (hs1 : s ≤ lF P.D) (hs2 : s ≤ lFe P.D) (hfe : P.D.fe = 2 ^ lFe P.D)
    (hfm : ∀ x : GatedNm, x.InR P.D s → fm (ι x) = toAff (gatedFm P.rd P.D (gatedEAt P o5 o6) s x))
    (hY : GoodNm Y ι P.D s) :
    TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (gatedLedOf P Y ι o5 o6 s)) m ↔
      P.gp.toSum.T.par.OutHolds o5 m ∧ P.rt.L.toSum.T.par.OutHolds o6 m := by
  refine ⟨gated_pull P hrd Y ι fm o5 o6 m s h1 hs1 hs2 hfe hfm hY, fun h => ?_⟩
  rw [Cb.Sub.pullL_holds]
  unfold gatedLedOf gatedLed
  rw [ledOf_holds]
  have hc := gated_last_conv (gNamesAt P (gReadsAt Y ι)) (gatedEAt P o5 o6) P.D (P.rd m) s
    (Sum.elim m fun j => (lateA Y fm j).val m) hs1 hs2 hfe (gated_tables P hrd Y ι fm _ s hfm hY m)
    (gated_bill_conv P (gReadsAt Y ι) o5 o6 m _ h1 h.1.2 h.2.2)
  intro f hf
  rcases (mem_two_two _ _ _ _).1 hf with rfl | rfl | hf
  · exact (prodU_iff P.gp o5 m _).2 h.1.1
  · exact (prodU_iff P.rt.L o6 m _).2 h.2.1
  · exact hc f hf

end Bill

section Merge

variable {E : Type} [Field E] [Fintype E] (P : FootW0 E) {J₂ : Type} [Fintype J₂]

/-- The pull-back of the merge's ledger and the pending row hold exactly if all output claims of the
merge's sumcheck hold. -/
theorem merge_pull_iff (a : J₂ → TWhole.Aff E P.J) (o : P.wt.L.toSum.T.par.Out) (m : P.J → E) :
    (TWhole.Ledger.Holds (Cb.Sub.pullL a (mergeLed P o)) m ∧
      Pending P (rowW (fun c : Fin P.n => o.st.2 ^ (c : ℕ)) (fun c => P.ten c o.st.1)
          ((noKept P.wt.L.Sm).outPt P.wt.L.Mk o))
        ((noKept P.wt.L.Sm).outPt P.wt.L.Mk o) ((noKept P.wt.L.Sm).outB P.wt.L.Mk o) (o.vals ())
        m) ↔ P.wt.L.toSum.T.par.OutHolds o m := by
  refine ⟨fun h => merge_pull P a o m h.1 h.2, fun h => ⟨?_, (wt_ev_iff P o m).1 (h.2 ())⟩⟩
  rw [Cb.Sub.pullL_holds]
  unfold mergeLed
  rw [ledOf_holds]
  intro f hf
  rw [List.mem_singleton.mp hf]
  exact (mergeU_iff P.wt.L o m _).2 h.1

variable (tenE : St7 E P.n → (Fin P.h → E) × ((Fin P.k → Bool) → E))
  (rhs : St7 E P.n → (P.J → E) → E) (mkE : P.J)

/-- The same in the first group. -/
theorem merge_pull_first_iff (a : J₂ → TWhole.Aff E P.J)
    (o : (P.wf tenE rhs mkE).L.toSum.T.par.Out) (m : P.J → E) :
    (TWhole.Ledger.Holds (Cb.Sub.pullL a (mergeLedF P tenE rhs mkE o)) m ∧
      Pending P (rowWF P tenE o.st.1.1 o.st.2
          ((noKept (P.wf tenE rhs mkE).L.Sm).outPt (P.wf tenE rhs mkE).L.Mk o))
        ((noKept (P.wf tenE rhs mkE).L.Sm).outPt (P.wf tenE rhs mkE).L.Mk o)
        ((noKept (P.wf tenE rhs mkE).L.Sm).outB (P.wf tenE rhs mkE).L.Mk o) (o.vals ()) m) ↔
      (P.wf tenE rhs mkE).L.toSum.T.par.OutHolds o m := by
  refine ⟨fun h => merge_pull_first P tenE rhs mkE a o m h.1 h.2,
    fun h => ⟨?_, (wf_ev_iff P tenE rhs mkE o m).1 (h.2 ())⟩⟩
  rw [Cb.Sub.pullL_holds]
  unfold mergeLedF
  rw [ledOf_holds]
  intro f hf
  rw [List.mem_singleton.mp hf]
  exact (mergeU_iff (P.wf tenE rhs mkE).L o m _).2 h.1

end Merge

end Cb.Pv.Lay.End.Gated
