-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3PlanLetters.lean: IN THE GOALS' SCOPE, WHAT THE LOOKUPS' READERS OF THE
PUBLIC PARAMETERS ANSWER AT A LINK ARE THE MODEL's OWNER's OWN TERMS: the attention shape that attAt
answers at link 2 g + 1 IS Hd.shapeA X g; the approximate range proof's parameters that attAt and
tlAt answer at link l ARE Meaning.tlAt X l (Johnson/Goal/Meaning/HidPlan.lean); the place's link is
l. So the theorems on the calls that stand at the letters A := Hd.shapeA X g, tl := tls x.link
(Johnson/Desc/Sound/MgAt/K3CallsMean.lean) can be called at whatever attAt, layAt, tlAt answer, at
tls := Meaning.tlAt X. On public data alone. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs in the verifier: sentences on Verify.publicOf's value.
Used by K3CallsLeftR.lean, K3CallsOwedScope.lean (Johnson/Desc/Sound/MgAt/) · MatsAtHead.lean
  (Johnson/K8Q35R/) and 3 more.
LETTERS: Z, pp, lay, X as in the scope's theorems; g: a group below 12.

Main names: `tlAt_is` (no scope: profile 4, twelve groups) · `attAt_letters` · `lay_letters`.

Limits. The full size's scope alone. The links below 24 (not the head's).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3PlanAtt
import Johnson.Desc.First.Look.K3CallsAddress
import Johnson.Goal.Meaning.HidPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model OnBytes.Road

/-- **The two readers of the approximate range proof's parameters are one**, where the lookups'
answers. -/
theorem tlAt_is {X : Verify.Public} {i : ℕ} {tl : HTailF2} (hp4 : X.p4 = true)
    (hN : X.NGr = 12) (hi : i < 24) (h : tlAt X i = some tl) : _root_.Meaning.tlAt X i = tl := by
  have hst : (if X.p4 then 2 else 1) = 2 := if_pos hp4
  unfold tlAt at h
  dsimp only at h
  rw [hst, hN] at h
  have h24 : (i == 2 * 12) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  rw [h24] at h
  simp only [Bool.false_eq_true, if_false] at h
  unfold _root_.Meaning.tlAt
  rw [if_neg (by omega), if_neg (by omega)]
  by_cases he : i % 2 = 0
  · have hb : (i % 2 == 0) = true := by
      rw [he]
      rfl
    rw [hb] at h
    simp only [if_true] at h
    rw [if_pos he, h]
    rfl
  · have hb : (i % 2 == 0) = false := by
      rw [beq_eq_false_iff_ne]
      exact he
    rw [hb] at h
    simp only [Bool.false_eq_true, if_false] at h
    rw [if_neg he, h]
    rfl

section
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}

/-- **At an attention link.** -/
theorem attAt_letters (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : Verify.publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) {x : Place}
    {A : Attention.Shape} {tl : HTailF2} (e : attAt X (2 * g + 1) = some (x, A, tl)) :
    x.link = 2 * g + 1 ∧ A = Hd.shapeA X g ∧ tl = _root_.Meaning.tlAt X x.link ∧
      lookAt X (2 * g + 1) false = some x := by
  obtain ⟨x', a, hlook, ha, e', -, -⟩ := attAt_scope hZ hR h (l := 2 * g + 1) (by omega)
    (by omega) ⟨default, default, default, #[]⟩ fun _ => 0
  rw [e'] at e
  obtain ⟨rfl, rfl, rfl⟩ : x' = x ∧ a.S = A ∧ a.seam.tl = tl := by
    have e1 := Option.some.inj e
    exact ⟨congrArg Prod.fst e1, congrArg (fun t => t.2.1) e1, congrArg (fun t => t.2.2) e1⟩
  have hk : (2 * g + 1) / 2 = g := by omega
  rw [hk] at ha
  have hx := VerifiableInference.OnPublicFiles.lookAt_link hlook
  refine ⟨hx, ?_, ?_, hlook⟩
  · unfold Hd.shapeA
    rw [ha]
    rfl
  · rw [hx]
    unfold _root_.Meaning.tlAt
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), hk, ha]
    rfl

/-- **At a layers' link.** -/
theorem lay_letters (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : Verify.publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) {tl : HTailF2}
    (e : tlAt X (2 * g) = some tl) : tl = _root_.Meaning.tlAt X (2 * g) := by
  obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans hZ hR h
  exact (tlAt_is hp4 hN (by omega) e).symm

end

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.tlAt_is
#print axioms VerifiableInference.Desc.First.Look.attAt_letters
#print axioms VerifiableInference.Desc.First.Look.lay_letters
