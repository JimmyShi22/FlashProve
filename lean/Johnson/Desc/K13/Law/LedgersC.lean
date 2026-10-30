-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/LedgersC.lean: THE PROOF OF THE STATEMENT OwedLedgersC THAT
Johnson/Desc/K13/Law/OwedWithin.lean WRITES AS OWED: the layer's test on the ledgers (ledgersFitC,
Johnson/Desc/K13/PubK13.lean: with code, no Mathlib beneath it) says what the laws' word says
(LedgersFit, Johnson/Desc/K13/Law/OwedLedgers.lean).

  nextAtC_eq      the layer's closed form is the laws' recursion (takenNo_eq,
                  OnBytes/Iop/LedgerPlaces.lean).
  ledgerAtC_iff   the test on one ledger: it is that of some number of takes since it was made.
  ledgersC        the owed statement.

What is not claimed. That the test says yes anywhere. Nothing on soundness, on an honest prover or
on hiding.

-/
import Johnson.Desc.K13.Law.OwedWithin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes
open VerifiableInference.Desc.First (S)

/-- The layer's closed form is the laws' recursion. -/
theorem nextAtC_eq {m : ℕ} (hm : 0 < m) : ∀ k, nextAtC m k = nextAt m k
  | 0 => rfl
  | k + 1 => by
    show k % m + 2 ^ ceilLog2 m * (k / m) + 1 = takenNo m k + 1
    rw [takenNo_eq hm k]
    rfl

/-- **The layer's test on one ledger says: it is that of some number of takes.** -/
theorem ledgerAtC_iff {st : Statement} {o : ℕ} {x : OnBytes.Oracle} {l : Ledger}
    (hx : st.oracles[o]? = some x) (hl : x.ledger = some l) :
    ledgerAtC st.codes x l = true ↔ ∃ k, LedgerAt st o k := by
  constructor
  · intro h
    simp only [ledgerAtC, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨hm, ha⟩, hr⟩, hq⟩, hle⟩, hn⟩ := h
    exact ⟨_, x, l, hx, hl, hm, ha, hr, hq, Nat.add_sub_cancel' hle, by rw [hn, nextAtC_eq hm]⟩
  · rintro ⟨k, x', l', hx', hl', hm, ha, hr, hq, hleft, hn⟩
    obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
    obtain rfl : l = l' := Option.some.inj (hl.symm.trans hl')
    simp only [ledgerAtC, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨⟨⟨⟨⟨hm, ha⟩, hr⟩, hq⟩, ?_⟩, ?_⟩
    · rw [← hleft]
      exact Nat.le_add_right _ _
    · rw [← hleft, Nat.add_sub_cancel_left, hn, nextAtC_eq hm]

/-- **THE OWED STATEMENT**: the layer's test on the ledgers says what the laws' word says. -/
theorem ledgersC : OwedLedgersC := by
  intro s
  unfold ledgersFitC
  rw [← Array.all_toList, List.all_eq_true]
  constructor
  · intro h o x hx hs
    have hm : x ∈ s.st.oracles.toList :=
      List.mem_iff_getElem?.2 ⟨o, by rw [Array.getElem?_toList]; exact hx⟩
    have h1 := h x hm
    cases hl : x.ledger with
    | none =>
      rw [hl] at hs
      cases hs
    | some l =>
      simp only [hl] at h1
      exact (ledgerAtC_iff hx hl).1 h1
  · intro h x hm
    obtain ⟨o, ho⟩ := List.mem_iff_getElem?.1 hm
    rw [Array.getElem?_toList] at ho
    cases hl : x.ledger with
    | none => rfl
    | some l => exact (ledgerAtC_iff ho hl).2 (h o x ho (by rw [hl]; rfl))

end VerifiableInference.Desc.K13.Law
