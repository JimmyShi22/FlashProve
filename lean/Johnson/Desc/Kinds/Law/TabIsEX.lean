-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/TabIsEX.lean: WHAT A YES OF THE TEST tabIsEXB (Law/TabIsEXCode.lean) GIVES:
at each row u < 2^16 the table's value is the library's EX u (Inst/Model/Tables.lean). Statements
and proofs.

  tabRun_spec      behind n rows the walk carries exG n, and its verdict is yes just if the first n
                   rows are right.
  tab_of_B         MAIN.

WHAT IT IS NOT. An implication: THE TEST HAS RUN NOWHERE. Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Inst.Model.Tables
import Johnson.Desc.Kinds.Law.TabIsEXCode

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

theorem tabRun_succ (tab : Nat → Nat) (n : Nat) :
    tabRun tab (n + 1) = tabStep tab (tabRun tab n) n := by
  unfold tabRun
  rw [List.range_succ, List.foldl_append]
  rfl

theorem tabRun_spec (tab : Nat → Nat) : ∀ n : Nat,
    (tabRun tab n).2 = Inst.Model.exG n ∧
      ((tabRun tab n).1 = true ↔
        ∀ u, u < n → tab u = (Inst.Model.exG u + (2 ^ 17 - 1)) / 2 ^ 17)
  | 0 => ⟨by norm_num [tabRun, Inst.Model.exG], by simp [tabRun]⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := tabRun_spec tab n
    rw [tabRun_succ]
    refine ⟨?_, ?_⟩
    · show ((tabRun tab n).2 * 484 + (2 ^ 32 - 1)) / 2 ^ 32 = _
      rw [h1]
      rfl
    · show (((tabRun tab n).1 && tab n == ((tabRun tab n).2 + (2 ^ 17 - 1)) / 2 ^ 17) = true) ↔ _
      rw [Bool.and_eq_true, h2, h1, beq_iff_eq]
      constructor
      · rintro ⟨a, b⟩ u hu
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with h | rfl
        · exact a u h
        · exact b
      · intro a
        exact ⟨fun u hu => a u (Nat.lt_succ_of_lt hu), a n (Nat.lt_succ_self n)⟩

/-- **A yes of the test.** -/
theorem tab_of_B {tab : Nat → Nat} (h : tabIsEXB tab = true) :
    ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u := fun u hu => by
  have h' : (tabRun tab 65536).1 = true := h
  have e := (tabRun_spec tab 65536).2.1 h' u (by norm_num at hu; exact hu)
  unfold Inst.Model.EX
  rw [e]

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.tab_of_B
