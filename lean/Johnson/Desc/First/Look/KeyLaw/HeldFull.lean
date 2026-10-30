-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/KeyLaw/HeldFull.lean: AT THE PUBLIC FILES IN SCOPE THE PLANNER'S OWN ROUNDS
FOR EACH LOOKUP HOLD: LookHeld (BelowAt.lean) at the sized key's setting and at the face of each of
its lookups, at the matrix's size that the shape of the test on the table gives. From InScope and
the planner's yes alone.

How. LookHeld follows from a test on the planner's list (listHeldB). At the public files in scope
the key's sizes are a written value (key_eq_at_scope, Johnson/Goal/PlanValues/KeyFullAtScope.lean).
There the test is evaluated in Lean's kernel.

Main names:
  listHeldB s x: the format's field; degree 3; each round of the planner's list at the size x, at
    the scope "once", passes sideR and holds at the target.
  lookHeld_of_list: its yes at the face's size gives LookHeld.
  held_full: the test at the written sizes of a key of full size, at each of its lookups: an
    evaluation in Lean's kernel.
    held_full_two: they are two. held_full_no: a trial: at a target raised by 64 the test says no.
    target_full: the target is 128.
  lookHeld_at_scope: THE LAW IN SCOPE.

Limits. One size. That the setting, the lookups and the shape which a key file's description reads
are the sized key's is not shown here. The target counts a round's proof of work.

-/
import Johnson.Desc.First.Look.KeyLaw.HeldAtScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Params OnBytes.Plan
open OnBytes.Flat.Held (sideR)

/-- The test on the planner's list. -/
def listHeldB (s : Setting) (x : LookupSize) : Bool :=
  decide (s.p = 2 ^ 64 - 2 ^ 32 + 1) && decide (s.degree = 3) &&
    (lookupList s x).all fun y =>
      sideR s.target (y.round s .once) && roundHolds s (capped s) (y.round s .once)

theorem lookHeld_of_list {s : Setting} {f : Face} (h : listHeldB s f.size = true) :
    LookHeld s f := by
  unfold listHeldB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun Q hQ => ?_⟩
  obtain ⟨-, hr, -⟩ := finish_rounds (runs_lookup f.size) hQ
  rw [hr]
  refine ⟨List.all_eq_true.2 fun r hr' => ?_, List.all_eq_true.2 fun r hr' => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hr'
    exact (Bool.and_eq_true_iff.1 (List.all_eq_true.1 h3 y hy)).1
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hr'
    exact (Bool.and_eq_true_iff.1 (List.all_eq_true.1 h3 y hy)).2

/-- The test at the written sizes of a key of full size, at each of its lookups. -/
theorem held_full : (Lk6.AtPlan.keyFull.ranges.x.lookups.all fun l =>
    listHeldB Lk6.AtPlan.keyFull.set (faceOfLkp (Wf.lookupOf
      Lk6.AtPlan.keyFull.ranges.x.messageId (Wf.matrixOf Lk6.AtPlan.keyFull.once.shape) l)).size) =
      true := by
  decide +kernel

/-- The list over which held_full runs has two members. -/
theorem held_full_two : Lk6.AtPlan.keyFull.ranges.x.lookups.length = 2 := by decide +kernel

/-- A trial that the test can say no: at a target raised by 64 no lookup's list passes. -/
theorem held_full_no : (Lk6.AtPlan.keyFull.ranges.x.lookups.any fun l =>
    listHeldB { Lk6.AtPlan.keyFull.set with target := Lk6.AtPlan.keyFull.set.target + 64 }
      (faceOfLkp (Wf.lookupOf Lk6.AtPlan.keyFull.ranges.x.messageId
        (Wf.matrixOf Lk6.AtPlan.keyFull.once.shape) l)).size) = false := by
  decide +kernel

/-- The target at the written sizes. -/
theorem target_full : Lk6.AtPlan.keyFull.set.target = 128 := by decide +kernel

/-- **At every three public files in scope the planner's own rounds for each lookup hold.** -/
theorem lookHeld_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p) :
    ∀ l ∈ p.chains.made.sized.key.ranges.x.lookups,
      LookHeld p.chains.made.sized.key.set (faceOfLkp (Wf.lookupOf
        p.chains.made.sized.key.ranges.x.messageId
        (Wf.matrixOf p.chains.made.sized.key.once.shape) l)) := by
  rw [Lk6.AtPlan.key_eq_at_scope hZ hp]
  exact fun l hl => lookHeld_of_list (List.all_eq_true.1 held_full l hl)

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.lookHeld_of_list
#print axioms VerifiableInference.Desc.K3.KeyLaw.held_full
#print axioms VerifiableInference.Desc.K3.KeyLaw.held_full_two
#print axioms VerifiableInference.Desc.K3.KeyLaw.held_full_no
#print axioms VerifiableInference.Desc.K3.KeyLaw.target_full
#print axioms VerifiableInference.Desc.K3.KeyLaw.lookHeld_at_scope
