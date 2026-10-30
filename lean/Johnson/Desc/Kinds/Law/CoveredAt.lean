-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/CoveredAt.lean: reads_covered_K06, OUR HALF, AT A HEARING's RETURN: Covered.lean asks that the
variables of what was heard be covered. `heard_slots`: where the head's sumcheck returns, the claimed
sum's variable, the sumcheck's start form and the two end values' variables ARE BARE SLOTS.
`covered_all`: so ALL ELEVEN OF THE HEAD's FORMS (the five keys; clip, table, mean, count; logitForms'
two) name entries of reads below the reads' lengths alone, with no premise on what was heard.
WHAT IT DOES NOT SAY: as in Covered.lean: where `entry r i` lies; that the plan's table of reads gives
each read a stretch of at least readLen.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.Covered
import Johnson.Desc.Kinds.Law.Clamp

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Aff Fork)
open Norm (lt ls d lPd T S2)
open Part.MaskedSum (Sent readAll leadScalars)

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

/-- Where the head's sumcheck returns, what it leaves of variables are bare slots. -/
theorem heard_slots {F0 F1 : Fork} {t : List Fmt.RoundView} {S : Sum}
    (hsum : sumcheck zP 2 F0 t = some (S, F1, [])) :
    (∃ j, S.claimed.var = Aff.slot j) ∧ (∃ j, (S.end_ 0).var = Aff.slot j) ∧
      (∃ j, (S.end_ 1).var = Aff.slot j) ∧ ∃ hd j, S.psc = some hd ∧ hd.start = Aff.slot j := by
  obtain ⟨ld, cA, Fa, G, hd, es, a1, a2, a3, a4, a5, a6, hS⟩ := sumcheck_spec hsum
  rw [kP_eq] at a2 a4 hS
  obtain ⟨_, Tt, R, hpub, hread, hhd, hrun2⟩ := Part.MaskedSum.hear_spec a4
  obtain ⟨r0, used, rv, front, ht, hs0, hfl, hvr, hsv⟩ :=
    Part.MaskedSum.readAll_spec (show readAll ⟨1, vsP, some ⟨2, 2⟩⟩ t = some R from hread)
  obtain ⟨c0, rfl⟩ := List.length_eq_one_iff.mp hfl
  have hs0' : Sent r0 2 1 [c0, R.mu] [R.eps] := hs0
  have hld : ld = [c0] := by
    have h1 : leadScalars ⟨1, vsP, some ⟨2, 2⟩⟩ t = some ld := a2
    rw [ht, lead_of_sent hs0'] at h1
    exact (Option.some.inj h1).symm
  subst hld
  obtain ⟨run1, hcA⟩ := hide_unfold a3
  have hC : cA.getD 0 {} = { var := Aff.slot F0.next, shown := c0 } := by
    rw [hcA]; simp
  obtain ⟨E0, E1⟩ := hiddenFrom_two a6
  refine ⟨⟨F0.next, ?_⟩, ⟨hd.sEnd, ?_⟩, ⟨hd.sEnd + 1, ?_⟩, hd, F0.next, ?_, ?_⟩
  · rw [hS]; show (cA.getD 0 {}).var = _; rw [hC]
  · rw [hS]; show (es.getD 0 {}).var = _; rw [E0]
  · rw [hS]; show (es.getD 1 {}).var = _; rw [E1]
  · rw [hS]
  · rw [hhd]; show (cA.getD 0 {}).var = _; rw [hC]

/-- **ALL ELEVEN OF THE HEAD's FORMS, at a hearing's return.** -/
theorem covered_all [Reads] (hy : y < V) {F0 F1 : Fork} {t : List Fmt.RoundView} {S : Sum}
    (hsum : sumcheck (FinalNorm.zt ++ halves lPd) 2 F0 t = some (S, F1, [])) :
    letI : Heard := { logits := S }
    (∀ k, Covered (key k)) ∧ (∀ f, f ∈ policy → Covered f) ∧ ∀ f, f ∈ logitForms → Covered f := by
  letI : Heard := { logits := S }
  obtain ⟨⟨j0, h0⟩, ⟨j1, h1⟩, _, hd, j3, hp, h3⟩ := heard_slots hsum
  have hV : 0 < V := Nat.lt_of_le_of_lt (Nat.zero_le _) hy
  have hc : Covered logits.claimed.var := by
    show Covered S.claimed.var
    rw [h0]; exact covered_slot _
  refine ⟨covered_key (JVa_le hV) hc, ?_, covered_logitForms ?_ ?_⟩
  · intro f hf
    unfold policy at hf
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact covered_mean
    · exact covered_count
    · exact covered_clip
    · exact covered_table
  · intro h hh
    have hh' : S.psc = some h := hh
    rw [hp] at hh'
    obtain rfl := Option.some.inj hh'
    rw [h3]; exact covered_slot _
  · show Covered (S.end_ 0).var
    rw [h1]; exact covered_slot _

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.covered_all
