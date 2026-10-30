-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeySampledAt.lean: AT EVERY BORDER OF THE KEY FILE's FIRST CHAIN THE LIBRARY's BOOL ON THE STATE
(`shape₁`, Johnson/Desc/Key/KeyShape.lean) ALREADY SAYS THAT THE MESSAGE AT EVERY OPEN PIN IS IN THE
STATEMENT, SAMPLED, WITH A SAMPLE ROW: behind a sending too. So "sent, sampled, with a row" need not
be carried from border to border: it is read off the Bool, and that is had behind every step
(E2E/KeyStateSide.lean). By unfolding the Bool's text, and one evaluation of the open sets. On the
verifier's state alone. NOTHING IS SHOWN OF ANY PROVER.

  **`sent_of_core`**: GENERAL in the plan, the readers and the book: at two lookups: from border 1
      on message 0 is sent and sampled (`sentB`); from border 2 on message 1; from border 18 on
      message 2
  `pins_when`: which pins are open at a border up to 19, in the library's open sets and in ours: BY
      EVALUATION
  **`sampled_of_shape`**: so at every pin that is open at border b

The library takes the Bool apart at single borders: `c_14_parts` (Johnson/RunOne/KeyThree.lean),
`core15_eq`, `core16_eq` (Johnson/RunOne/Law/K12Shape15.lean).

Limits.
- THAT THE READING RETURNS A SAMPLE AT AN OPEN PIN DOES NOT FOLLOW FROM THIS: at the library's own
  filling the letter that reads a sample off a message's entry answers only where besides the codes
  are the filling's, the shape a member's, the sample rows just one, and a drawn factor reads as a
  unit (`smFam`, Johnson/Desc/Key/KeyFillSrc.lean; `rowIsK`, Johnson/RunOne/KeyFillSeed.lean;
  `ReadsOne`, Johnson/Desc/K1/Law/Port4.lean). (A premise that asks it to answer at every sampled
  entry is false at that filling.)
- "Sampled, with a sample row" says nothing on what the sample is worth.
- The first chain alone; two lookups.

-/
import E2E.KeyRest

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (hasSmp)
open VerifiableInference.Desc.Key (KPlan KReaders KBook KItem Where Xi FirstState sentB core₁ shape₁
  shape₁_iff pinned start₁ ArrOk)
open Johnson.RunOne.KeyRows1 (plan₁ readers₁ book₁ slots₁ open₁)
open Johnson.RunOne.KeyRows23 (BaseSt)
open ProofFile.Honest

section
variable {S : Type} (K : KPlan) (X : KReaders S) (B : KBook S)

/-- **What the book-keeping says of the three messages**, at two lookups. -/
theorem sent_of_core (slots : Nat → Nat) (b : Nat) (s : S)
    (h : core₁ K X B 2 slots b s = true) :
    (1 ≤ b → sentB K X s 0 = true) ∧ (2 ≤ b → sentB K X s 1 = true) ∧
      (18 ≤ b → sentB K X s 2 = true) := by
  unfold core₁ at h
  split at h
  · rename_i e
    have e' : b = 0 := by simpa using e
    subst e'
    exact ⟨fun q => absurd q (by decide), fun q => absurd q (by decide),
      fun q => absurd q (by decide)⟩
  · split at h
    · rename_i _ e
      have e' : b = 1 := by simpa using e
      subst e'
      simp only [Bool.and_eq_true] at h
      exact ⟨fun _ => h.1.1, fun q => absurd q (by decide), fun q => absurd q (by decide)⟩
    · split at h
      · rename_i _ _ e
        simp only [Bool.and_eq_true] at h
        exact ⟨fun _ => h.1.1.1.1.1.1, fun _ => h.1.1.1.1.1.2, fun q => by omega⟩
      · simp only [Bool.and_eq_true] at h
        refine ⟨fun _ => h.1.1.1.1.1, fun _ => h.1.1.1.1.2, fun q => ?_⟩
        have h2 := h.2
        split at h2
        · rename_i e
          have e' : b - (2 + 6 * 2) = 0 := by simpa using e
          omega
        · split at h2
          · rename_i _ e
            have e' : b - (2 + 6 * 2) = 1 := by simpa using e
            omega
          · split at h2
            · rename_i _ _ e
              have e' : b - (2 + 6 * 2) = 2 := by simpa using e
              omega
            · split at h2
              · rename_i _ _ _ e
                have e' : b - (2 + 6 * 2) = 3 := by simpa using e
                omega
              · simp only [Bool.and_eq_true] at h2
                exact h2.1.1.2

end

/-- Which pins are open at a border, in the library's open sets and in ours. -/
theorem pins_when : ∀ b ∈ List.range 20,
    (∀ k ∈ pinned (open₁ 2 b), (k = 0 ∧ 1 ≤ b) ∨ (k = 1 ∧ 2 ≤ b) ∨ (k = 2 ∧ 18 ≤ b)) ∧
      ∀ k ∈ pinned (fwdOpen (start₁ 2) rowsFirst b),
        (k = 0 ∧ 1 ≤ b) ∨ (k = 1 ∧ 2 ≤ b) ∨ (k = 2 ∧ 18 ≤ b) := by decide

section
variable (one : OnBytes.Params.OneTime)

/-- **At every pin that is open at border b.** -/
theorem sampled_of_shape {b : Nat} (hb : b ≤ 19) (s : FirstState)
    (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) b s = true) :
    ∀ k, (k ∈ pinned (open₁ 2 b) ∨ k ∈ pinned (fwdOpen (start₁ 2) rowsFirst b)) →
      sentB (plan₁ one) (readers₁ one) s k = true := by
  intro k hk
  obtain ⟨s0, s1, s2⟩ := sent_of_core (plan₁ one) (readers₁ one) (book₁ one) (slots₁ one) b s
    ((shape₁_iff (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) b s).1 h).2
  have hw := pins_when b (List.mem_range.2 (Nat.lt_succ_of_le hb))
  have hc : (k = 0 ∧ 1 ≤ b) ∨ (k = 1 ∧ 2 ≤ b) ∨ (k = 2 ∧ 18 ≤ b) :=
    hk.elim (hw.1 k) (hw.2 k)
  rcases hc with ⟨rfl, q⟩ | ⟨rfl, q⟩ | ⟨rfl, q⟩
  · exact s0 q
  · exact s1 q
  · exact s2 q

end

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.sent_of_core
#print axioms AtPublicFiles.KeyThread.pins_when
#print axioms AtPublicFiles.KeyThread.sampled_of_shape
