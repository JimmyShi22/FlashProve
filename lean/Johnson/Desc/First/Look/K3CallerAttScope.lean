-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerAttScope.lean: WHAT IS ASKED OF THE PUBLIC DATA AT AN ATTENTION
LINK's CALLS (AttOK, Johnson/Desc/First/Look/K3CallerAtt.lean) HOLDS AT ALL PUBLIC FILES IN THE
GOALS' SCOPE, at the place that lookAt makes and the shape Hd.shapeA X g of the link's group. It
joins this folder's theorems with those of Johnson/Goal/Meaning/. NO SOUNDNESS IS CLAIMED.

Whose. `attOK_scope`, statement and proof, is by the writers of
Johnson/Goal/Meaning/AttNumsScope.lean; `attOK_scope_link` by the writers of this folder.

Main names:
  `attOK_scope`: by attOK_public (Johnson/Desc/First/Look/K3CallerAttPublic.lean), whose two
    premises are paid: x.fs.NC = 4 by sameCalls_in_scope (Johnson/Goal/Meaning/AttForInScope.lean),
    attFitsB by attFits_six (Johnson/Goal/Meaning/AttNumsScope.lean); x.fs is the plan's record by
    lookAt_att (Johnson/Desc/First/Look/K3CallerAtPlan.lean). A premise beside these: the group's
    number is below 12.
  `attOK_scope_link`: the same with «the link stands in front of the head's» (i < step * X.NGr) in
    the place of «it is not the head's» and «the group's number is below 12»: in the scope there are
    twelve groups.

Limits. In the scope alone. One direction. Nothing on the guards of the caller's reading. tl, D and
rad are letters that no field of AttOK reads. That Hd.shapeA X g is the plan's own shape is said
elsewhere (Johnson/Goal/Meaning/AttScope.lean: attOrd_iff_in_scope), not here.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerAttPublic
import Johnson.Goal.Meaning.AttNumsScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- **In the goals' scope AttOK holds at every attention link's place.** -/
theorem attOK_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : Verify.publicOf Z.pol Z.KL lay = .ok X) {i : ℕ} {x : Place}
    (e : lookAt X i false = some x) (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr)
    (h0 : i % (if X.p4 then 2 else 1) ≠ 0) (hg : i / (if X.p4 then 2 else 1) < 12)
    (set : Params.Setting) (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat) :
    AttOK set x (Road.Hd.shapeA X (i / (if X.p4 then 2 else 1))) tl D rad := by
  obtain ⟨a, ha, -, e1, -⟩ := lookAt_att e hn h0
  have ef : Meaning.Att.fsA X (i / (if X.p4 then 2 else 1)) = a.fs := by
    unfold Meaning.Att.fsA
    rw [ha]
    rfl
  refine attOK_public h e hn h0 ?_ ?_ set tl D rad
  · rw [e1, ← ef]
    exact (Meaning.Att.sameCalls_in_scope hZ hR h hg).NC
  · rw [e1, ← ef]
    exact decide_eq_true (Meaning.Att.attFits_six hZ hR h hg)

/-- **The same at every attention link in front of the head's.** -/
theorem attOK_scope_link {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : Verify.publicOf Z.pol Z.KL lay = .ok X) {i : ℕ} {x : Place}
    (e : lookAt X i false = some x) (hi : i < (if X.p4 then 2 else 1) * X.NGr)
    (h0 : i % (if X.p4 then 2 else 1) ≠ 0)
    (set : Params.Setting) (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat) :
    AttOK set x (Road.Hd.shapeA X (i / (if X.p4 then 2 else 1))) tl D rad := by
  have hN : X.NGr = 12 := (Road.Hd.public_of_core h (Road.Hd.core_of_scope hZ hR h)).groups
  refine attOK_scope hZ hR h e (Nat.ne_of_lt hi) h0 ?_ set tl D rad
  rw [← hN]
  exact Nat.div_lt_of_lt_mul hi

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.attOK_scope
#print axioms VerifiableInference.Desc.First.Look.attOK_scope_link
