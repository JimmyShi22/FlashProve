-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/TableTie.lean: THE TIE OF THE TABLES AND WHAT THE FOUR PARTS MEAN, PROVED: TablesStatement,
TieStatement and HeadMeansStatement of HeadTablesLaw.lean. THE BRIDGE (eq_natCast_of_rd): an element that is
written in the one canonical way and is read in the field as the image of a natural n IS (n : E). That every
place of keyTable is so written: okE_keyTable: a corner key is an output of the forms' operations; the padding
key is the image of a natural.
IMPORTED, NOT PROVED HERE: Law/Lemma2a.lean (okE_keyAt, okE_addMul, eq_of_rd); Law/NormProof.lean
(lemma1_whole).
-/
import Mathlib
import Johnson.Desc.Kinds.HeadTablesLaw
import Johnson.Desc.Kinds.Law.OutCall

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E okE)
open OnBytes.Model (Aff)
open Norm (lt ls d S2 T)

/-! ## 1. The bridge -/

theorem okE_natCast (n : Nat) : okE ((n : Nat) : E) = true := by
  have hp : OnBytes.pW.toNat = 18446744069414584321 := by decide
  have hm : n % OnBytes.pW.toNat < OnBytes.pW.toNat := Nat.mod_lt _ (by rw [hp]; norm_num)
  have h0 : OnBytes.okF (natF n) = true := by
    unfold OnBytes.okF natF
    apply decide_eq_true
    rw [UInt64.lt_iff_toNat_lt]
    have h1 : (n % OnBytes.pW.toNat).toUInt64.toNat = n % OnBytes.pW.toNat := by
      simp only [Nat.toUInt64, UInt64.toNat_ofNat']
      apply Nat.mod_eq_of_lt
      rw [hp] at hm ⊢
      omega
    rw [h1]
    exact hm
  show (OnBytes.okF (natF n) && OnBytes.okF 0 && OnBytes.okF 0) = true
  rw [h0]
  decide

/-- **THE BRIDGE.** -/
theorem eq_natCast_of_rd {x : E} (hx : okE x = true) {n : Nat} (h : rd x = (n : K)) :
    x = ((n : Nat) : E) :=
  eq_of_rd hx (okE_natCast n) (by rw [h, rd_natCast])

/-! ## 2. Every place of keyTable is written in the canonical way -/

theorem okE_formSum : ∀ (n : Nat) (f : Nat → Form), okE (sumTo n f).const = true
  | 0, _ => by
    show okE ((0 : Nat) : E) = true
    exact okE_natCast 0
  | n + 1, f => by
    have h : sumTo (n + 1) f = sumTo n f + f n := by
      unfold sumTo
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [h]
    exact okE_addMul _ _ _

section Sized
variable [Sizes] [Policy] [Request] [Token]

theorem okE_keyNAt (c : NCells) (p : NPt) (k : FinalNorm.Key) : okE (keyNAt c p k) = true := by
  cases k
  · exact okE_addMul _ _ _
  · exact okE_addMul _ _ _
  · exact okE_addMul _ _ _
  · exact okE_formSum _ _

theorem okE_keyTable {sT : Nat} (hplan : planOk sT = true) (c : NCells) (call col t : Nat) :
    okE (keyTable c call col t) = true := by
  unfold keyTable callTable
  rw [tableOf_map okE (lens41 hplan call)]
  by_cases h : ∃ s x, x < ((callKeys call).map lenOf).getD s 0
      ∧ column ((callKeys call).map lenOf) s x = col
  · obtain ⟨s, x, hx, rfl⟩ := h
    rw [tableOf_entry (lens41 hplan call) _ _ hx]
    rcases slot (callKeys call) s with k | k
    · exact okE_keyNAt c _ k
    · exact okE_keyAt c.toCells _ k
  · rw [tableOf_pad _ _ _ fun s x hx he => h ⟨s, x, hx, he⟩]
    exact okE_natCast _

end Sized

/-! ## 3. The rows -/

section Rows
variable [Sizes]

theorem rowsOk_spec {row : Nat → Nat → Nat} (h : rowsOk row = true) :
    (∀ u, u < 2 ^ 16 → row 0 u = u ∧ row 1 u = u ∧ row 3 u % 2 ^ 16 = u ∧ 1 ≤ row 3 u / 2 ^ 16 ∧
      row 3 u / 2 ^ 16 ≤ 2 ^ F ∧ row 4 u = row 3 u ∧ row 5 u = clampRow u) ∧
    (∀ u, u < 2 ^ 8 → row 2 u = u) ∧ row 3 0 / 2 ^ 16 = 2 ^ F := by
  unfold rowsOk at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun u hu => ?_, h2, h3⟩
  have h4 := h1 u hu
  unfold rowsOkAt at h4
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h4
  obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := h4
  exact ⟨a1, a2, a3, a4, a5, a6, a7⟩

end Rows

/-- **Where the test passes the rows are rows.** -/
theorem tables_law : TablesStatement := by
  intro _ row h
  obtain ⟨h16, h8, h0⟩ := rowsOk_spec h
  have hrow3 : ∀ u, u < 2 ^ 16 → row 3 u = u + 2 ^ 16 * tabOf row u := by
    intro u hu
    unfold tabOf
    rw [if_pos hu]
    have h1 := Nat.div_add_mod (row 3 u) (2 ^ 16)
    rw [(h16 u hu).2.2.1] at h1
    omega
  refine ⟨⟨?_, fun u => ?_⟩, ?_⟩
  · unfold tabOf
    rw [if_pos (by norm_num)]
    exact h0
  · unfold tabOf
    split
    · rename_i hu
      exact ⟨(h16 u hu).2.2.2.1, (h16 u hu).2.2.2.2.1⟩
    · exact ⟨le_refl 1, Nat.one_le_two_pow⟩
  · intro call hcall u hu
    interval_cases call
    · exact ⟨u, hu, by rw [(h16 u hu).1]⟩
    · exact ⟨u, hu, by rw [(h16 u hu).2.1]⟩
    · exact ⟨u, hu, by rw [h8 u hu]⟩
    · exact ⟨u, hu, by rw [hrow3 u hu]⟩
    · exact ⟨u, hu, by rw [(h16 u hu).2.2.2.2.2.1, hrow3 u hu]⟩
    · exact ⟨u, hu, by rw [(h16 u hu).2.2.2.2.2.2]; rfl⟩

/-- **THE TIE.** -/
theorem tie_law : TieStatement := by
  intro _ _ _ _ sT row c hplan h call hcall col t u hu he
  rw [eq_natCast_of_rd (okE_keyTable hplan c call col t) he]
  exact (tables_law row h).2 call hcall u hu

/-- **WHAT THE FOUR PARTS MEAN.** -/
theorem head_means : HeadMeansStatement := by
  intro _ _ _ _ sT floor tab c hplan hreq hy htab hW P
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := backCall sT floor tab c hplan P.lookCalls
  exact lemma1_whole sT tab c hplan hreq hy htab hW
    ⟨k1, k2, k3, k4, k5, P.rider, P.idnSums⟩
    ⟨P.small, P.smallS, P.idnRows, k6, k7, k8, k9⟩

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.tables_law
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.tie_law
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.head_means
