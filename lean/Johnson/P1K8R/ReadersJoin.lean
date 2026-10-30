-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ReadersJoin.lean: THE LAST JOIN FOR THE FIELD «readers» OF MgOwes:
FROM «what the seated link's sub-protocols at the lookup's and at the
caller's address state commutes with the draw» TO mg_readers' | mg_readers_head's PREMISE.
General in 𝔇. A closed fact on the table's map of names, and a joining.
  runsOf_front      a pair that the table names at a piece in front of the draw's (k < 5 + the sort's shift) is stated by the sub-protocol number 1 + shift (the lookup on the calls) or 2 + shift (the calling kind).
  k8ShiftB_full     a closed fact: at the written list: pcOf l = 5 + shift and IM.k3Ix l false = 1 + shift, at each of the 25.
  states_of_two     𝔇.lk m = c.links[m]? for all m · at link l: what sub-protocol number IM.k3Ix l false states, and what number IM.k3Ix l false + 1 states, is RunBlind ⟹ for every pair p that the table names at a piece in front of the draw's: every run that sub-protocol number p.1 of 𝔇.lk l states is RunBlind: mg_readers' premise h (and more: whatever the run's name).
LIMITS. A rule over letters. No soundness. Nothing on hiding.
-/
import Johnson.P1K8R.ReadersAtMg
import Johnson.P1K8R.WalkK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart runsOf shift)
open VerifiableInference.Desc.First.K8 (RunBlind)
open VerifiableInference.Desc.K9 (statesOfLink)
open ProofFile (Cl)

theorem runsOf_front (sub : ModelPart) (k : ℕ) (r : String) (p : ℕ × String) (hp : p ∈ runsOf sub k r)
    (hk : k < 5 + shift sub) : p.1 = 1 + shift sub ∨ p.1 = 2 + shift sub := by
  obtain ⟨a, b⟩ := p
  unfold runsOf at hp
  cases sub <;> simp only [] at hp <;> split_ifs at hp <;> simp_all [shift] <;> omega

theorem k8ShiftB_full : ((List.range 25).all fun l =>
    (linksFull[l]?).any fun sub => pcOf l == 5 + shift sub && IM.k3Ix l false == 1 + shift sub) =
      true := by decide

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  {𝔇 : MgData Xi P Tok rows cols nR X}

theorem states_of_two {l : ℕ} (hl : l ≤ 24) (hL : 𝔇.links = linksFull) (c : Chain S Cl)
    (hlk : ∀ m, 𝔇.lk m = c.links[m]?)
    (h3 : ∃ Lk, c.links[l]? = some Lk ∧ ∀ ρ ∈ statesOfLink Lk (IM.k3Ix l false), RunBlind (ρ.2 0))
    (hc : ∃ Lk, c.links[l]? = some Lk ∧
      ∀ ρ ∈ statesOfLink Lk (IM.k3Ix l false + 1), RunBlind (ρ.2 0)) :
    ∀ k r, k < pcOf l → ∀ p ∈ 𝔇.runs l k r, ∀ l', 𝔇.lk l = some l' →
      ∀ ρ ∈ statesOfLink l' p.1, (ρ.1 == p.2) = true → RunBlind (ρ.2 0) := by
  intro k r hk p hp l' hl' ρ hρ _
  have h := List.all_eq_true.1 k8ShiftB_full l (List.mem_range.2 (Nat.lt_succ_of_le hl))
  have hp' : p ∈ runsAt 𝔇.links l k r := hp
  rw [hL] at hp'
  rw [hlk l] at hl'
  obtain ⟨L3, e3, H3⟩ := h3
  obtain ⟨Lc, ec, Hc⟩ := hc
  obtain rfl : L3 = l' := Option.some.inj (e3.symm.trans hl')
  obtain rfl : Lc = L3 := Option.some.inj (ec.symm.trans hl')
  cases hs : linksFull[l]? with
  | none => simp [hs] at h
  | some sub =>
    simp only [hs, Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
    rw [runsAt_of linksFull l sub hs k r] at hp'
    rcases runsOf_front sub k r p hp' (by rw [← h.1]; exact hk) with e | e
    · rw [e, ← h.2] at hρ
      exact H3 ρ hρ
    · have e' : p.1 = IM.k3Ix l false + 1 := by rw [e, h.2]; omega
      rw [e'] at hρ
      exact Hc ρ hρ

end

end P1K8T

#print axioms P1K8T.runsOf_front
#print axioms P1K8T.states_of_two
