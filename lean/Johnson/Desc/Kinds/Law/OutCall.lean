-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/OutCall.lean: OUT AND BACK BY THE CALL, PROVED: OutCallStatement, BackCallStatement and
PadsStatement of HeadOutLaw.lean. OUT: the law of a call's key vector (Law/Call.lean) at the values of the
nine keys' forms in the world: the head's five are spread by the premise, the normalization's four by
Law/NormKeys.lean. BACK: at an entry's column the call's table holds the entry's corner key
(Law/Columns.lean: tableOf_entry), and the column lies below 2^lJ.
IMPORTED, NOT THIS FILE's: Law/NoWrap.lean (planFacts); HeadNormLaw.lean, Law/NormProof.lean.
-/
import Mathlib
import Johnson.Desc.Kinds.HeadOutLaw
import Johnson.Desc.Kinds.Law.Call
import Johnson.Desc.Kinds.Law.NormKeys

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open OnBytes.Model (World)
open Norm (lt ls d S2 T)

/-- A map goes through a call's table. -/
theorem tableOf_map {α β : Type} (f : α → β) {lens : List Nat} (hl : ∀ n ∈ lens, n < 2 ^ 41)
    (g : Nat → Nat → α) (pad : α) (col : Nat) :
    f (tableOf lens g pad col) = tableOf lens (fun s x => f (g s x)) (f pad) col := by
  by_cases h : ∃ s x, x < lens.getD s 0 ∧ column lens s x = col
  · obtain ⟨s, x, hx, rfl⟩ := h
    rw [tableOf_entry hl g pad hx, tableOf_entry hl _ _ hx]
  · have h' : ∀ s x, x < lens.getD s 0 → column lens s x ≠ col :=
      fun s x hx he => h ⟨s, x, hx, he⟩
    rw [tableOf_pad lens g pad h', tableOf_pad lens _ _ h']

section Sized
variable [Sizes] [Policy] [Request] [Token]

theorem JVa_le_JV (hV : 0 < V) : JVa ≤ JV := by
  have hJ : 1 ≤ JV := le_trans pos_S2 (S2_le_JV hV)
  unfold JVa clog2
  split
  · simpa using hJ
  · rename_i h
    have h1 : 2 ^ (JV - 1).log2 ≤ JV - 1 := Nat.log2_self_le (by omega)
    rw [Nat.add_sub_cancel]
    omega

/-- Under the tests on the plan every key's length is below 2^41. -/
theorem lens_small {sT : Nat} (h : planOk sT = true) : ∀ k, lenOf k < 2 ^ 41 := by
  have P := planFacts h
  have hV : 0 < V := by have := P.hV2; omega
  have hd : d < 2 ^ 41 := by have := P.hW; omega
  have hJ : JV < 2 ^ 41 := by
    have h1 := P.hZ
    rw [P.hF] at h1
    omega
  have hA := JVa_le_JV hV
  intro k
  rcases k with k | k <;> cases k <;> simp only [lenOf, len, NR] <;> omega

theorem lens41 {sT : Nat} (h : planOk sT = true) (call : Nat) :
    ∀ n ∈ (callKeys call).map lenOf, n < 2 ^ 41 := by
  intro n hn
  obtain ⟨k, _, rfl⟩ := List.mem_map.1 hn
  exact lens_small h k

theorem lenOf_inl (k : FinalNorm.Key) : lenOf (.inl k) = lenN k := by
  cases k <;> rfl

end Sized

/-- **OUT, BY THE CALL.** -/
theorem outCall : OutCallStatement := by
  intro _ _ _ _ nI hI _ _ _ _ _ sT floor zx zk c W hplan hP hn hh hhead hN call hcall
  subst hn
  subst hh
  letI : FinalNorm.In := (fromLookup floor zx zk).norm
  letI : In := (fromLookup floor zx zk).head
  have P := planFacts hplan
  have hV : 0 < V := by have := P.hV2; omega
  have hlen := lens_small hplan
  have hd : S2 ∣ d := Nat.dvd_of_mod_eq_zero P.hdS
  have L := fromLookup_law floor zx zk hV hlen hP
  have hF : FilledNW W c :=
    { hact := hN.act, hrow := hN.row, hwide := hN.wide, hclaimed := hN.claimed
      hblock := fun k hk x hx => by
        have hl : lenOf (.inl k) = d := by
          cases k
          · rfl
          · rfl
          · rfl
          · exact absurd rfl hk
        exact L.block (.inl k) (by rw [hl]; exact hd) x (by rw [hl]; exact hx)
      hwsum := fun k => by
        have h0 := L.wsum (.inl k)
        rw [lenOf_inl] at h0
        exact h0
      hzt := L.zt }
  have hspread : ∀ k ∈ callKeys call, SpreadAt (fromLookup floor zx zk)
      (fun k x t => rd (cornerKey c k x t)) k
      (val W (match k with
        | .inl k => FinalNorm.key 21 k
        | .inr k => key k)) := by
    intro k _
    rcases k with k | k
    · show val W (FinalNorm.key 21 k) = _
      rw [val_keyN hF hd k, lenOf_inl]
      exact spr_congr fun x hx t ht => (rd_keyNAt_corner c hd k hx ht).symm
    · exact hhead k
  have hc := call_point_law floor zx zk hV hlen hP call hcall _ _ hspread
  unfold keyVector
  rw [val_foldl_add, val_coe, List.map_map]
  refine Eq.trans ?_ (hc.trans ?_)
  · rfl
  · refine Finset.sum_congr rfl fun i _ => ?_
    unfold keyTable callTable
    rw [tableOf_map rd (lens41 hplan call), rd_natCast]

/-- **BACK, BY THE CALL.** -/
theorem backCall : BackCallStatement := by
  intro _ _ _ _ sT floor tab c hplan h
  have hlen := lens_small hplan
  -- at the column of entry x of key k the call's table holds the corner key
  have key : ∀ (k : PlaceKey) (x t : Nat), x < lenOf k → t < T →
      InTable tab (placeOf k).1 (cornerKey c k x t) := by
    intro k x t hx ht
    have hc6 : (placeOf k).1 < 6 := by rcases k with k | k <;> cases k <;> decide
    have hk : callKeys (placeOf k).1 = keysOf k := rfl
    have hx' : x < ((callKeys (placeOf k).1).map lenOf).getD (placeOf k).2 0 := by
      rw [hk, len_keysOf]
      exact hx
    have hs : slot (callKeys (placeOf k).1) (placeOf k).2 = k := by
      rcases k with k | k <;> cases k <;> rfl
    have hcol : column ((callKeys (placeOf k).1).map lenOf) (placeOf k).2 x
        < 2 ^ lJ floor (callKeys (placeOf k).1) :=
      lt_of_lt_of_le ((columns_law _ (lens41 hplan _)).1 _ _ hx')
        (le_trans (le_two_pow_clog2 _) (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)))
    have h0 := h _ hc6 _ hcol t ht
    unfold keyTable callTable at h0
    rw [tableOf_entry (lens41 hplan _) _ _ hx', hs] at h0
    exact h0
  exact ⟨fun t ht x hx => key (.inr .marginTop) x t hx ht,
    fun t ht x hx => key (.inr .marginMid) x t hx ht,
    fun t ht x hx => key (.inr .marginLow) x t hx ht,
    fun t ht x hx => key (.inr .tableA) x t hx ht,
    fun t ht x hx => key (.inr .tableB) x t hx ht,
    fun t ht x hx => key (.inl .remLow) x t hx ht,
    fun t ht x hx => key (.inl .remHigh) x t hx ht,
    fun t ht x hx => key (.inl .clamp) x t hx ht,
    fun t ht x hx => key (.inl .digits) x t hx ht⟩

/-- **The padding keys are rows.** -/
theorem pads : PadsStatement := by
  intro _ tab h0 call hcall
  interval_cases call
  · exact ⟨0, by norm_num, rfl⟩
  · exact ⟨0, by norm_num, rfl⟩
  · exact ⟨0, by norm_num, rfl⟩
  · refine ⟨0, by norm_num, ?_⟩
    rw [h0]
    show ((2 ^ (16 + F) : Nat) : E) = _
    rw [Nat.zero_add, pow_add]
  · refine ⟨0, by norm_num, ?_⟩
    rw [h0]
    show ((2 ^ (16 + F) : Nat) : E) = _
    rw [Nat.zero_add, pow_add]
  · refine ⟨2 ^ 15, by norm_num, ?_⟩
    show ((2 ^ 15 + 2 ^ 39 : Nat) : E) = _
    congr 1

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.outCall
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.backCall
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.pads
