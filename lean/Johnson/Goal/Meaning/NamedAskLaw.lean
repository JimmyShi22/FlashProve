-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/NamedAskLaw.lean: THE LAWS OF THE LIGHT TEST OF
Johnson/Goal/Meaning/NamedAsk.lean, OUTSIDE THE VERIFIER's TOPS (over Mathlib): a yes of namedB at
the full size's shape gives Meaning.namedThere at the library's own sizes. Theorems, proved.

  fullShaped X   attention is there, and twelve groups of layers. full_parts: X.p4 = true and X.NGr
    = 12.
  tlK_eq   at that shape, at k < 25: tlK X k = Meaning.tlAt X k: the tie of the light Look.tlAt to
    Meaning.tlAt.
  linkK_eq, nameK_eq   the two second texts are the first ones'.
  named_of_B   namedB X layout = true gives Meaning.namedThere X (Meaning.sizesOf X) layout = true.
  B_of_named, namedB_eq   the way back: at that shape the two tests say the same: so the light one
    refuses nothing that the other lets pass.
  fullShaped_scope   in the goals' scope the plan has that shape: off scope_plans
    (Johnson/Goal/Meaning/PlanShapes.lean).

OBJECT: namedB; Meaning.namedThere (Johnson/Goal/Meaning/LaidCovered.lean).
LETTERS: X, layout: free.

What is not claimed. That namedB says yes at any files. Nothing on soundness.
-/
import Johnson.Goal.Meaning.NamedAsk
import Johnson.Goal.Meaning.LaidCovered
import Johnson.Goal.Meaning.PlanShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.NamedAsk

open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open OnBytes.Params (ReqLayout)
open VerifiableInference.Desc (arrayOf)

variable {X : Verify.Public}

/-- The plan has the full size's shape: attention is there, and twelve groups of layers. -/
def fullShaped (X : Verify.Public) : Bool := X.p4 && X.NGr == 12

theorem full_parts (h : fullShaped X = true) : X.p4 = true ∧ X.NGr = 12 := by
  unfold fullShaped at h
  rw [Bool.and_eq_true] at h
  exact ⟨h.1, eq_of_beq h.2⟩

/-- **At the full size's shape the two texts of "the plan's parameters of sub-proof k's range check"
are one**, at the 25 sub-proofs. -/
theorem tlK_eq (h : fullShaped X = true) {k : ℕ} (hk : k < 25) : tlK X k = Meaning.tlAt X k := by
  obtain ⟨h4, h12⟩ := full_parts h
  unfold tlK VerifiableInference.Desc.First.Look.tlAt Meaning.tlAt
  simp only [h4, h12, if_true]
  rw [if_neg (by omega : ¬ 24 < k)]
  by_cases e : k = 24
  · subst e
    rfl
  · rw [if_neg e, if_neg (by simpa using e)]
    by_cases ev : k % 2 = 0
    · rw [if_pos ev, if_pos (by simpa using ev)]
    · rw [if_neg ev, if_neg (by simpa using ev)]

/-- The two second texts are the first ones': so that they cannot drift. -/
theorem linkK_eq (id : ℕ) : linkK id = Meaning.linkOf id := rfl

theorem nameK_eq (a : ℕ) : nameK a = Meaning.nameOf a := rfl

/-- **A yes of the light test gives the test of Johnson/Goal/Meaning/LaidCovered.lean.** -/
theorem named_of_B (h : fullShaped X = true) {layout : ReqLayout}
    (T : namedB X layout = true) : Meaning.namedThere X (Meaning.sizesOf X) layout = true := by
  unfold namedB at T
  unfold Meaning.namedThere
  rw [List.all_eq_true] at T ⊢
  intro k hk
  have hk' : k < 25 := List.mem_range.1 hk
  have Tk := T k hk
  rw [tlK_eq h hk'] at Tk
  rw [List.all_eq_true] at Tk ⊢
  intro a ha
  have Ta := Tk a ha
  have eL : labK X k a = Meaning.labAt X k a := by
    unfold labK Meaning.labAt Meaning.matsAt
    rw [tlK_eq h hk']
  rw [eL] at Ta
  exact Ta

/-- **The way back: so the light test is no stronger than the other**: at the full size's shape the
two say the same. -/
theorem B_of_named (h : fullShaped X = true) {layout : ReqLayout}
    (T : Meaning.namedThere X (Meaning.sizesOf X) layout = true) : namedB X layout = true := by
  unfold Meaning.namedThere at T
  unfold namedB
  rw [List.all_eq_true] at T ⊢
  intro k hk
  have hk' : k < 25 := List.mem_range.1 hk
  have Tk := T k hk
  rw [tlK_eq h hk']
  rw [List.all_eq_true] at Tk ⊢
  intro a ha
  have Ta := Tk a ha
  have eL : labK X k a = Meaning.labAt X k a := by
    unfold labK Meaning.labAt Meaning.matsAt
    rw [tlK_eq h hk']
  rw [eL]
  exact Ta

theorem namedB_eq (h : fullShaped X = true) (layout : ReqLayout) :
    namedB X layout = Meaning.namedThere X (Meaning.sizesOf X) layout :=
  Bool.eq_iff_iff.2 ⟨named_of_B h, B_of_named h⟩

section Scope
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}

/-- In the goals' scope the plan has the full size's shape. -/
theorem fullShaped_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : fullShaped X = true := by
  obtain ⟨h4, h12, -⟩ := Meaning.scope_plans hZ hR h
  unfold fullShaped
  rw [h4, h12]
  rfl

end Scope

#print axioms linkK_eq
#print axioms nameK_eq
#print axioms tlK_eq
#print axioms named_of_B
#print axioms namedB_eq
#print axioms fullShaped_scope

end Meaning.NamedAsk
