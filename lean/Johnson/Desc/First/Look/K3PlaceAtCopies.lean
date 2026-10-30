-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3PlaceAtCopies.lean: THE PREMISE e OF THE CALLS' LAWS AT THE SEATED
CONSTANT (placeAt X i false = some (P.ofPlace (settingOf X.P.frame) false x),
Johnson/Desc/First/Look/K3CallsStatedCap.lean) HOLDS AT attAt's AND AT layAt's PLACE: the copy of
lookAt's own place with the made record laid anew, at which the public tests attBAt and layBAt
(Johnson/Desc/First/Look/K3BoolsAtCalls.lean) speak. Five lemmas and two corollaries. Ties of
texts.

OBJECT: no text that runs in the verifier: placeAt, attAt, layAt.
Used by K3LawOfR.lean (Johnson/Desc/First/Look/).
LETTERS: X, i free.

Why. P.ofPlace does not read the place's field fs. So a run's yes of attBAt (layBAt) meets e AND H
of k3_att_stated_cap (k3_lay_stated_cap) AT ONE x.

Main names: `placeAt_attAt`, `placeAt_layAt` · `att_e_and_H`, `lay_e_and_H`: from the Bool's yes:
one x with e, H, and the planes' tests · `attAt_none_of_layAt`: a layers' link is no attention link
· `attAt_none_at_head`, `layAt_none_at_head`: the head's link is neither.

Limits. Nothing on the other premises of the laws.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3BoolsAtCalls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

theorem placeAt_attAt {X : Verify.Public} {i : ℕ} {x : Place} {A : Attention.Shape} {tl : HTailF2}
    (hx : attAt X i = some (x, A, tl)) :
    placeAt X i false = some (P.ofPlace (Params.settingOf X.P.frame) false x) := by
  unfold attAt at hx
  split at hx
  · obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨a, -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', -, hx⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨rfl, -⟩ := Prod.mk.inj hx
    unfold placeAt
    rw [h1]
    rfl
  · cases hx

theorem placeAt_layAt {X : Verify.Public} {i : ℕ} {x : Place} (hx : layAt X i = some x) :
    placeAt X i false = some (P.ofPlace (Params.settingOf X.P.frame) false x) := by
  unfold layAt at hx
  split at hx
  · obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', -, rfl⟩ := Option.map_eq_some_iff.1 hx
    unfold placeAt
    rw [h1]
    rfl
  · cases hx

/-- A layers' link is no attention link. -/
theorem attAt_none_of_layAt {X : Verify.Public} {i : ℕ} {x : Place} (hx : layAt X i = some x) :
    attAt X i = none := by
  unfold attAt
  split
  · rename_i hc
    exfalso
    unfold layAt at hx
    split at hx
    · rename_i hl
      simp only [Bool.and_eq_true, beq_iff_eq] at hl
      have h0 := hl.1
      unfold stepOf at h0
      rw [if_pos hc.1] at h0
      omega
    · cases hx
  · rfl

/-- The head's link is no attention link. -/
theorem attAt_none_at_head (X : Verify.Public) :
    attAt X ((if X.p4 then 2 else 1) * X.NGr) = none := by
  unfold attAt
  rw [if_neg]
  rintro ⟨h1, h2⟩
  rw [if_pos h1] at h2
  omega

/-- The head's link is no layers' link. -/
theorem layAt_none_at_head (X : Verify.Public) :
    layAt X ((if X.p4 then 2 else 1) * X.NGr) = none := by
  unfold layAt
  rw [if_neg]
  intro hc
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
  exact hc.2 rfl

/-- **A yes of attBAt meets e and H at one x.** -/
theorem att_e_and_H {X : Verify.Public} {i : ℕ} (D : Sent) (rad : OracleShape → Nat)
    (h : attBAt X i = true) :
    ∃ x A tl, placeAt X i false = some (P.ofPlace (Params.settingOf X.P.frame) false x) ∧
      AttOK (Params.settingOf X.P.frame) x A tl D rad ∧ planesInB x A tl = true := by
  obtain ⟨x, A, tl, hx, H, hp⟩ := attOK_of_attBAt D rad h
  exact ⟨x, A, tl, placeAt_attAt hx, H, hp⟩

/-- **A yes of layBAt meets e, H and hpl at one x.** -/
theorem lay_e_and_H {X : Verify.Public} {i : ℕ} (h : layBAt X i = true) :
    ∃ x, placeAt X i false = some (P.ofPlace (Params.settingOf X.P.frame) false x) ∧
      LayOK (Params.settingOf X.P.frame) x ∧ (Forest.planeCols x.fs x.lm).toBool = true := by
  obtain ⟨x, hx, H, hp⟩ := layOK_of_layBAt h
  exact ⟨x, placeAt_layAt hx, H, hp⟩

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.placeAt_attAt
#print axioms VerifiableInference.Desc.First.Look.placeAt_layAt
#print axioms VerifiableInference.Desc.First.Look.attAt_none_of_layAt
#print axioms VerifiableInference.Desc.First.Look.attAt_none_at_head
#print axioms VerifiableInference.Desc.First.Look.layAt_none_at_head
#print axioms VerifiableInference.Desc.First.Look.att_e_and_H
#print axioms VerifiableInference.Desc.First.Look.lay_e_and_H
