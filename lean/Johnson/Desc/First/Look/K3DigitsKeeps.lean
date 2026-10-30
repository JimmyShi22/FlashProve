-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigitsKeeps.lean: the lookup on the digits of a link's smallness test: THE
TWO STEPS WITHOUT A ROUND THAT STAND BEHIND IT (K3.quietDigits at a layers' or an attention link,
K3.quietHead at the head's: Johnson/Desc/First/Look/K3Whole.lean) KEEP WHAT THE END THEOREM's
CONDITION AND RELATION BEHIND READ: DigKeeps (K3DigitsSeated.lean). So k3_digits_seated's premise
hKeep is paid, but for the samples' reader. Statements and proofs. NO SOUNDNESS IS CLAIMED.

Main names.
  ownOf_putFork: laying a ledger does not turn the record's own five (that it does not turn the
    smallness test's record is tl_putFork, Johnson/Top/H/K3SeatFits.lean).
  later_planClaims: a ledger with another count of planned claims is a later ledger, with the same
    sizes.
  quietDigits_keeps, quietHead_keeps: DigKeeps at a yes of each step.
  quietAt_keeps: at every step that quietAt gives at digits = true.
OBJECT. Desc.K3.quietDigits, Desc.K3.quietHead, Desc.K3.quietAt (K3Whole.lean); the carried record's
readers fork?, tl?, link?, live, putFork (Johnson/Desc/First/State.lean).
USER. k3_digits_seated's hKeep (K3DigitsSeated.lean).
LETTERS. smp, with two premises: it does not turn where a ledger is laid, nor where the head's claim
is laid.
Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)
Limits. The two premises on smp are shown of no reader of samples. Nothing where a step refuses.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsSeated
import Johnson.Desc.First.Look.K3QuietLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-- Laying a ledger does not turn the record's own five. -/
theorem ownOf_putFork (s : Desc.First.S) (Gk : Fork) : ownOf (s.putFork Gk) = ownOf s := by
  cases hh : s.here with
  | between => simp [ownOf, Desc.First.S.putFork, Desc.First.S.link?, hh]
  | fin _ => simp [ownOf, Desc.First.S.putFork, Desc.First.S.link?, hh]
  | mem _ => simp [ownOf, Desc.First.S.putFork, Desc.First.S.link?, hh]
  | lay a => simp [ownOf, Desc.First.S.putFork, Desc.First.S.link?, Desc.First.S.live, hh]
  | att a => simp [ownOf, Desc.First.S.putFork, Desc.First.S.link?, Desc.First.S.live, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [ownOf, Desc.First.S.putFork, Desc.First.S.link?, hh, ho]
    | true => simp [ownOf, Desc.First.S.putFork, Desc.First.S.link?, Desc.First.S.live, hh, ho]

/-- Another count of planned claims: a later ledger. -/
theorem later_planClaims (F : Fork) (c : ℕ) : _root_.Fo.Later F { F with planClaimsF := c } :=
  ⟨Nat.le_refl _, rfl, fun _ h => ⟨h, rfl, rfl⟩⟩

section
variable {x : Desc.First.Look.Place} {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ}
  (smp : Desc.First.S → (i : Fin (digList x D rad).length) → Option ((digSg x D rad).om i).Smp)

/-- **Behind the digits' lookup at a layers' or an attention link.** -/
theorem quietDigits_keeps (hS : ∀ s Gk, smp (Desc.First.S.putFork s Gk) = smp s) (used claims : ℕ)
    (s t : Desc.First.S) (h : Desc.K3.quietDigits used claims s = .ok t) : DigKeeps smp s t := by
  obtain ⟨F₂, hF₂, hG₂⟩ := Desc.K3.quietDigits_fork used claims s t h
  obtain ⟨F, -, -, rfl⟩ := Desc.K3.quietDigits_ok used claims s t h
  refine ⟨fun F' hF' => ?_, ?_, ownOf_putFork s _, hS s _⟩
  · obtain rfl : F₂ = F' := Option.some.inj (hF₂.symm.trans hF')
    exact ⟨_, hG₂, later_planClaims F₂ claims, fun hz => hz⟩
  · rw [tl_putFork]

/-- **Behind it at the head's link.** -/
theorem quietHead_keeps
    (hS : ∀ (s : Desc.First.S) a c, s.here = .head a →
      smp { s with here := .head { a with claim := some c } } = smp s)
    (X : Verify.Public) (s t : Desc.First.S) (h : Desc.K3.quietHead X s = .ok t) :
    DigKeeps smp s t := by
  obtain ⟨a, c, ha, ho, rfl⟩ := Desc.K3.quietHead_ok X s t h
  refine ⟨fun F' hF' => ⟨F', ?_, _root_.Fo.Later.refl F', fun hz => hz⟩, ?_, ?_, hS s a c ha⟩
  · simpa [Desc.First.S.fork?, ha, ho] using hF'
  · simp [Desc.First.S.tl?, ha, ho]
  · simp [ownOf, Desc.First.S.link?, Desc.First.S.live, ha, ho]

/-- **At every step that stands behind the digits' lookup.** -/
theorem quietAt_keeps (hS : ∀ s Gk, smp (Desc.First.S.putFork s Gk) = smp s)
    (hH : ∀ (s : Desc.First.S) a c, s.here = .head a →
      smp { s with here := .head { a with claim := some c } } = smp s)
    (X : Verify.Public) (i : ℕ) (f : Desc.First.S → Except String Desc.First.S)
    (hf : Desc.K3.quietAt X i true = some f) (s t : Desc.First.S) (h : f s = .ok t) :
    DigKeeps smp s t := by
  unfold Desc.K3.quietAt at hf
  simp only [if_true] at hf
  split at hf
  · obtain rfl := Option.some.inj hf
    exact quietHead_keeps smp hH X s t h
  · split at hf <;> split at hf <;>
      (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf
       exact quietDigits_keeps smp hS _ _ s t h)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.quietDigits_keeps
#print axioms VerifiableInference.OnPublicFiles.quietHead_keeps
#print axioms VerifiableInference.OnPublicFiles.quietAt_keeps
#print axioms VerifiableInference.OnPublicFiles.ownOf_putFork
#print axioms VerifiableInference.OnPublicFiles.later_planClaims
