--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/CellsWithCostsNorm.lean.
WHAT IT DOES NOT SHOW. All that Law/CellsWithCosts.lean says it does not show, BUT FOR ONE POINT:
that of the norm's own relation only the 17 identities were carried over to the new cells: here all
of it is. A TOY: weights 0, the stream of zeros, a table of two
values.
WHAT IT IS. BOTH RELATIONS ON CELLS, THE NORM's (HeadNormLaw.lean: CellRelN) AND THE HEAD's
(HeadLaw.lean: CellRel), HOLD WHOLE OF ONE c, AT A REQUEST WITH COSTS.
  wide_old, awZ_withCosts, remZ_withCosts, recZ_withCosts   what the norm's three keys on the
                    features read is c's own.
  cellRelN_withCosts   where CellRelN holds of c it holds of withCosts c: small; the rows; the three
                    keys are c's keys, as elements; the key on the 120 digits: c's below 99, the
                    head's 21 bytes from there on.
  cells_both        planOk, Request.ok, y < V, Admits: there is c with CellRelN c, CellRel c.toCells
                    stepTab, TableOk stepTab, (dataOf c).Holds, paid = cost.
  AtX.cells_both_X  the same at Law/CellsWithCostsAt.lean's letters: no premise is left.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.CellsWithCostsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE)
open Norm (lt ls d lPd T S2)

variable [Sizes] [Policy] [Request] [Token]

theorem wide_old (c : NCells) (t : Nat) {f : Nat} (hf : f < 4 * d) :
    (withCosts c).cell .wide f t = c.cell .wide f t := by
  show (if f < 4 * d then c.cell .wide f t else _) = _
  rw [if_pos hf]

theorem awZ_withCosts (c : NCells) (t : Nat) {x : Nat} (hx : x < d) :
    awZ (withCosts c) t x = awZ c t x := by
  unfold awZ
  rw [wide_old c t (by omega), wide_old c t (by omega)]

theorem remZ_withCosts (c : NCells) (t : Nat) {x : Nat} (hx : x < d) :
    remZ (withCosts c) t x = remZ c t x := by
  unfold remZ
  rw [wide_old c t (by omega), wide_old c t (by omega)]

theorem digZ_withCosts (c : NCells) (t : Nat) {n : Nat} (hn : n < 99) :
    digZ (withCosts c) t n = digZ c t n := by
  unfold digZ
  rw [cell_row_low c t hn]

theorem recZ_withCosts (c : NCells) (t : Nat) : recZ (withCosts c) t = recZ c t := by
  unfold recZ Inst.Model.Ledger.R Inst.Model.Ledger.Rlo Inst.Model.Ledger.Rhi
  rw [b256_congr (fun n hn => digZ_withCosts c t hn) 80 3 (by omega),
    b256_congr (fun n hn => digZ_withCosts c t hn) 83 3 (by omega)]

/-- **THE NORM's RELATION ON CELLS HOLDS OF THE NEW CELLS WHERE IT HOLDS OF THE OLD, WHOLE.** -/
theorem cellRelN_withCosts {sT : Nat} (hplan : planOk sT = true) (A : Admits) (c : NCells)
    (h : CellRelN c) : CellRelN (withCosts c) := by
  have hd : S2 ∣ d := Nat.dvd_of_mod_eq_zero (planFacts hplan).hdS
  refine ⟨small_withCosts hplan A c h.small, h.smallS, fun t ht v hv => ?_, fun t ht x hx => ?_,
    fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht j hj => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv
    have hk' : k < 17 := by rw [rowsAt_length] at hk; exact hk
    apply eq_of_rd (okE_rowsAt _ _ hv) okE_zero
    have e := rd_rowsAt (withCosts c) (bits lt t) (size_bits lt t) hk'
    rw [List.getD_eq_getElem _ _ hk, ext_corner ht] at e
    have hH := holds_withCosts c (holds_of_rows c h.rows) 0 (show 0 < 1 by omega) k hk' t ht
    rw [idAt_eq] at hH
    rw [e, hH, rd_zero]
  · have e : keyNAt (withCosts c) (cornerN x t) .remLow = keyNAt c (cornerN x t) .remLow :=
      eq_of_rd (okE_keyNAt _ _ _) (okE_keyNAt _ _ _) (by
        rw [rd_keyN_remLow ht hd hx, rd_keyN_remLow ht hd hx, recZ_withCosts,
          awZ_withCosts c t hx, remZ_withCosts c t hx]
        rfl)
    rw [e]
    exact h.remLow t ht x hx
  · have e : keyNAt (withCosts c) (cornerN x t) .remHigh = keyNAt c (cornerN x t) .remHigh :=
      eq_of_rd (okE_keyNAt _ _ _) (okE_keyNAt _ _ _) (by
        rw [rd_keyN_remHigh ht hd hx, rd_keyN_remHigh ht hd hx, remZ_withCosts c t hx])
    rw [e]
    exact h.remHigh t ht x hx
  · have e : keyNAt (withCosts c) (cornerN x t) .clamp = keyNAt c (cornerN x t) .clamp :=
      eq_of_rd (okE_keyNAt _ _ _) (okE_keyNAt _ _ _) (by
        rw [rd_keyN_clamp ht hd hx, rd_keyN_clamp ht hd hx, awZ_withCosts c t hx]
        rfl)
    rw [e]
    exact h.clamp t ht x hx
  · by_cases h99 : j < 99
    · have e : keyNAt (withCosts c) (cornerN j t) .digits = keyNAt c (cornerN j t) .digits :=
        eq_of_rd (okE_keyNAt _ _ _) (okE_keyNAt _ _ _) (by
          rw [rd_keyN_digits ht hj, rd_keyN_digits ht hj, digZ_withCosts c t h99])
      rw [e]
      exact h.digits t ht j hj
    · have hm : ((mul j : Nat) : Int) = 1 := by
        unfold mul
        have : ∀ a : Nat, a < 99 → (j == a) = false := fun a ha => by simp; omega
        simp [this]
      have hj' : j - NR < 21 := by unfold NR at hj ⊢; omega
      have hjj : NR + (j - NR) = j := by unfold NR; omega
      have hb := headDigit_byte hplan A t hj'
      have hz : digZ (withCosts c) t j = (headDigit t (j - NR) : Int) := by
        unfold digZ
        rw [← hjj, cell_row c t hj', hjj]
        ring
      refine inBits_of_rd (okE_keyNAt _ _ _) (rd_keyN_digits ht hj) ?_ ?_
      · rw [hm, one_mul, hz]
        omega
      · rw [hm, one_mul, hz]
        norm_num
        omega

/-- **BOTH RELATIONS ON CELLS HOLD WHOLE OF ONE c.** -/
theorem cells_both {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true) (hy : y < V)
    (A : Admits) :
    ∃ c : NCells, CellRelN c ∧ CellRel c.toCells stepTab ∧ TableOk stepTab ∧ (dataOf c).Holds ∧
      (∀ n t, numZ c.toCells n t = (headNum n t : Int)) ∧ (∀ k v, c.Wh k v = 0) ∧
      ∀ t, numZ c.toCells .paid t = cost c.toCells t := by
  obtain ⟨c, hc⟩ := cellRelN_met hplan
  have P := planFacts hplan
  exact ⟨withCosts c, cellRelN_withCosts hplan A c hc,
    cellRel_withCosts hplan hreq hy A c hc.small, tableOk_step P.hF,
    holds_withCosts c (holds_of_rows c hc.rows), numZ_withCosts c, fun _ _ => rfl, fun t => by
      rw [numZ_withCosts, cost_withCosts (by have := P.hV2; omega)]
      rfl⟩

end VerifiableInference.Desc.Kinds.Head.Law

namespace VerifiableInference.Desc.Kinds.Head.Law.AtX

attribute [local instance] sizesX policyX requestX tokenX

/-- **cells_both AT Law/CellsWithCostsAt.lean's LETTERS: NO PREMISE IS LEFT.** -/
theorem cells_both_X :
    ∃ c : NCells, CellRelN c ∧ CellRel c.toCells stepTab ∧ TableOk stepTab ∧ (dataOf c).Holds ∧
      (∀ n t, numZ c.toCells n t = (headNum n t : Int)) ∧ (∀ k v, c.Wh k v = 0) ∧
      ∀ t, numZ c.toCells .paid t = cost c.toCells t :=
  cells_both plan_X request_X token_X admits_X

end VerifiableInference.Desc.Kinds.Head.Law.AtX
