-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/KeyLaw/HeldAtPlan.lean: WHERE THE PLANNER FINISHES THE PLAN OF A KEY'S
ONE-TIME CHAIN, ITS OWN ROUNDS FOR EACH LOOKUP HOLD: LookHeld (BelowAt.lean) at the face of every
lookup of the sized key, from two facts on public values: oneTimePlan z = .ok P
(OnBytes/Plan/KeyOneTime.lean: the plan is finished and its own verdict is yes) and sideB P = true
(OnBytes/Flat/HeldAll.lean).

How. The plan's rounds are the list oneTimeListAt (oneTimePlan_is, OnBytes/Plan/PlanListsKey.lean),
of which each lookup's list is a stretch; every member of that list holds at the target. The
planner's list at the face's size is its list at the size that the planner's own caller makes of the
lookup's public record (list_size, BelowAt.lean; lookupList_port,
OnBytes/Tie/Pv/KeyLookup/LamSpec.lean).

Main names:
  mem_oneTime: a round of a lookup's list is a round of the one-time chain's list.
  lookHeld_of_oneTime: see above.

Limits. That a key file's description is made of such a z, with z.set its setting and z.ranges its
lookups, is not shown here. Premises on the lookup: Adm, d ≤ 64, the face passes its own test.

-/
import OnBytes.Plan.PlanListsKey
import Johnson.Desc.First.Look.KeyLaw.BelowAt
import Johnson.Desc.First.Look.KeyLaw.Closed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Params OnBytes.Plan
open OnBytes.Flat.Held (sideR sideB)
open Lk6 (pubOf sizeOfPort sizeOfPub)

/-- A round of a lookup's list is a round of the one-time chain's list. -/
theorem mem_oneTime (z : KeySized) (n : ℕ) (L : LinSize) (p : Lkp.Public)
    (hp : p ∈ Wf.lookupsOf z.ranges.x z.ranges.matrix) (y : RoundSpec)
    (hy : y ∈ lookupList z.set (sizeOfPort p)) : y ∈ oneTimeListAt z n L := by
  unfold oneTimeListAt rangesListAt
  refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_append_left _ ?_))))
  exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨sizeOfPort p, List.mem_map.2 ⟨p, hp, rfl⟩, rfl⟩, hy⟩

/-- **Where the planner finishes the one-time chain's plan, its rounds for each lookup hold.** -/
theorem lookHeld_of_oneTime (z : KeySized) (P : Planned) (h : oneTimePlan z = .ok P)
    (hside : sideB P = true) (l : WfLookup) (hl : l ∈ z.ranges.x.lookups)
    (hadm : (pubOf (Wf.lookupOf z.ranges.x.messageId z.ranges.matrix l)).Adm Cb.Gl.p)
    (hd : l.d ≤ 64)
    (hok : (faceOfLkp (Wf.lookupOf z.ranges.x.messageId z.ranges.matrix l)).ok = true) :
    LookHeld z.set (faceOfLkp (Wf.lookupOf z.ranges.x.messageId z.ranges.matrix l)) := by
  obtain ⟨n, L, -, -, -, hP⟩ := oneTimePlan_is h
  unfold sideB at hside
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hside
  obtain ⟨⟨c1, c2⟩, c3⟩ := hside
  rw [hP.set] at c1 c2 c3
  refine ⟨c1, c2, fun Q hQ => ?_⟩
  obtain ⟨-, hr, -⟩ := finish_rounds (runs_lookup _) hQ
  have hmu : (Wf.lookupOf z.ranges.x.messageId z.ranges.matrix l).mu ≤ 6 := by
    have hok' := hok
    unfold Face.ok at hok'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok'
    exact hok'.1.1.1.1.1.1.1.2
  have e : lookupList z.set (faceOfLkp (Wf.lookupOf z.ranges.x.messageId z.ranges.matrix l)).size =
      lookupList z.set (sizeOfPort (Wf.lookupOf z.ranges.x.messageId z.ranges.matrix l)) :=
    (list_size z.set (datK Unit z.ranges.x.messageId z.ranges.matrix l []) () _
      (faceIsK Unit z.ranges.x.messageId z.ranges.matrix l [] () hadm hd) hok hadm).trans
      (Lk6.lookupList_port z.set _ hmu).symm
  have hmem : ∀ y ∈ lookupList z.set
      (faceOfLkp (Wf.lookupOf z.ranges.x.messageId z.ranges.matrix l)).size,
      y ∈ oneTimeListAt z n L := fun y hy =>
    mem_oneTime z n L _ (List.mem_map.2 ⟨l, hl, rfl⟩) y (e ▸ hy)
  rw [hr]
  refine ⟨List.all_eq_true.2 fun r hr' => ?_, List.all_eq_true.2 fun r hr' => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hr'
    exact List.all_eq_true.1 c3 _ (by rw [hP.rounds]; exact List.mem_map_of_mem (hmem y hy))
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hr'
    exact hP.holds y (hmem y hy)

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.mem_oneTime
#print axioms VerifiableInference.Desc.K3.KeyLaw.lookHeld_of_oneTime
