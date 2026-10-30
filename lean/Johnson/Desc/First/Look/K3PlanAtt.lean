-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3PlanAtt.lean: THE PUBLIC TEST ON THE PLAN AT AN ATTENTION LINK's CALLS
(attBAt, Johnson/Desc/First/Look/K3BoolsAtCalls.lean) SAYS YES AT ALL TWELVE ATTENTION LINKS, IN THE
GOALS' SCOPE: BY THEOREM: the field "att" of the structure K3Plan (K3Means.lean). Statements
and proofs. A tie of public data: no error term. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs in the verifier: a Bool on Verify.publicOf's value.
Used by K03PlanOf.lean, K3PlanLetters.lean (Johnson/Desc/First/Look/) · K3CallsLeftR.lean
  (Johnson/Desc/Sound/MgAt/) and 1 more.
LETTERS: Z, pp, lay, X as in the scope's theorems; l: an odd link below 24; D, rad: idle letters of
  AttOK, handed through.

Main names:
  `planesInB_of_atB`: the closed callers' test on the planes' cells (planesAtB,
    Johnson/Desc/First/Look/K3CallerCellsIn.lean) gives planesInB
    (Johnson/Desc/First/Look/K3AttGuards.lean): its last three conjuncts.
  `attAt_scope`: in scope attAt answers at an odd link below 24, with lookAt's own place, the plan's
    shape and its record of the smallness test.
  `attBAt_scope`: THE END: attBAt X l = true.

How it goes. Meaning.scope_plans (Johnson/Goal/Meaning/PlanShapes.lean): profile 4, twelve groups,
all twelve attention plans. attOK_scope_link (K3CallerAttScope.lean): AttOK at lookAt's own place:
its fields are four of the Bool's five conjuncts, and its first says that the made record is the
plan's: so attAt's copy is that place. att_planes (K3CallerAtPlan.lean): the fifth.

Limits. The full size's scope alone. Nothing on the layers' or the head's test.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3BoolsAtCalls
import Johnson.Desc.First.Look.K3CallerAttScope
import Johnson.Goal.Meaning.PlanShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- The closed callers' test gives the row's. -/
theorem planesInB_of_atB {x : Place} {A : Attention.Shape} {tl : HTailF2}
    (e : planesAtB tl x.fs x.lm (A.cf.NAs + 2) = true) : planesInB x A tl = true := by
  obtain ⟨-, -, h1, h2, h3⟩ := planesAtB_iff.1 e
  unfold planesInB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨h1, h2⟩, h3⟩

section
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}

/-- **In scope attAt answers at every attention link**, and what it answers meets AttOK and the
planes' test. -/
theorem attAt_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : Verify.publicOf Z.pol Z.KL lay = .ok X) {l : ℕ} (hl : l < 24) (h1 : l % 2 = 1)
    (D : Sent) (rad : OracleShape → Nat) :
    ∃ x a, lookAt X l false = some x ∧ X.A[l / 2]? = some a ∧
      attAt X l = some (x, a.S, a.seam.tl) ∧
      AttOK (Params.settingOf X.P.frame) x a.S a.seam.tl D rad ∧
      planesInB x a.S a.seam.tl = true := by
  obtain ⟨hp4, hN, -, hA⟩ := Meaning.scope_plans hZ hR h
  have hst : (if X.p4 then 2 else 1) = 2 := if_pos hp4
  obtain ⟨a, ha, eS⟩ := hA (l / 2) (by omega)
  have hi : l < (if X.p4 then 2 else 1) * X.NGr := by
    rw [hst, hN]
    omega
  have h0 : l % (if X.p4 then 2 else 1) ≠ 0 := by
    rw [hst]
    omega
  have hn : l ≠ (if X.p4 then 2 else 1) * X.NGr := Nat.ne_of_lt hi
  obtain ⟨x, e⟩ : ∃ x, lookAt X l false = some x := by
    unfold lookAt
    dsimp only
    rw [if_neg (by simpa using hn), if_neg (by simpa using h0), hst, ha]
    exact ⟨_, rfl⟩
  have H := attOK_scope_link hZ hR h e hi h0 (Params.settingOf X.P.frame) a.seam.tl D rad
  rw [hst, ← eS] at H
  obtain ⟨a', tl', ha', ht', hpl⟩ := att_planes h e hn h0
  obtain ⟨a'', ha'', ht'', -⟩ := lookAt_att e hn h0
  rw [hst] at ha' ha''
  obtain rfl : a = a' := Option.some.inj (ha.symm.trans ha')
  obtain rfl : a = a'' := Option.some.inj (ha.symm.trans ha'')
  obtain rfl : a.seam.tl = tl' := Option.some.inj (ht''.symm.trans ht')
  refine ⟨x, a, e, ha, ?_, H, planesInB_of_atB hpl⟩
  unfold attAt
  rw [if_pos ⟨hp4, h1⟩, e, Option.bind_some, ha, Option.bind_some, H.shape, Option.map_some]

/-- **THE PUBLIC TEST SAYS YES AT ALL TWELVE ATTENTION LINKS, IN SCOPE.** -/
theorem attBAt_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : Verify.publicOf Z.pol Z.KL lay = .ok X) {l : ℕ} (hl : l < 24) (h1 : l % 2 = 1)
    (D : Sent) (rad : OracleShape → Nat) : attBAt X l = true := by
  obtain ⟨x, a, -, -, hat, H, hp⟩ := attAt_scope hZ hR h hl h1 D rad
  unfold attBAt
  rw [hat]
  simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨⟨⟨⟨H.four, H.planes⟩, H.fits⟩, H.masksIn⟩, hp⟩

end

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.planesInB_of_atB
#print axioms VerifiableInference.Desc.First.Look.attAt_scope
#print axioms VerifiableInference.Desc.First.Look.attBAt_scope
