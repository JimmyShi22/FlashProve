-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/FrontOfParts.lean: THE WHOLE LISTING "front" FROM ITS SEVEN PARTS: a part of
the law "behind K4's hearing its two runs of claims return" (Johnson/Road/K4/Total/Returns.lean):
FrontSkel follows from NormsSkel, RowsSkel, TermsSkel, GatedSkel, OneHotSkel, PlanesSkel, EmbedSkel.
Statements and proofs.

THE TEXT (front, OnBytes/Desc/First/K4/Claims.lean), BIND BY BIND: seven binds, one a listing, in
the order norms, rows, terms, gated, one-hot, planes, embedding; the seventh is asked in the first
group alone (g == 0: one g on both sides) and is some [] elsewhere. What is bound goes into the list
alone: no later bind reads it. The two forms rowV and rowL, and the switch rows, go into the list
alone.

  `front_of_parts`: from all seven parts as premises.
  `front_of_two`: from NormsSkel and RowsSkel, with the other five paid by TermsGatedSkel.lean and
    RestSkel.lean.
  `front_skel : FrontSkel`: THE PART, under no premise: the two paid by NormsRowsSkel.lean.
No new argument.
**Limits.** front_skel has no premise beside the sentence's own (Skel o o₀). A CONGRUENCE: "front"
is not said to return anywhere: that is the law's premise "member", which no theorem of this file
pays (`member_of_plan`, Johnson/Road/K4/Total/PlanMember.lean, has it from a return of the hearing
and an accept of `frontB`). Nothing on what a form is worth, nothing on soundness. K04_law, the law
of K4's block itself, IS NOT PROVED. Met through Lean at no member; by a run at one honest proof of
each of two sizes both runs of claims return at all 2 and 12 layers' places: that run is the member.


-/
import Johnson.Road.K4.Total.TermsGatedSkel
import Johnson.Road.K4.Total.RestSkel
import Johnson.Road.K4.Total.NormsRowsSkel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model

/-- **The whole listing, from its seven parts.** -/
theorem front_of_parts (hN : NormsSkel) (hR : RowsSkel) (hT : TermsSkel) (hG : GatedSkel)
    (hO : OneHotSkel) (hP : PlanesSkel) (hE : EmbedSkel) : FrontSkel := by
  intro rows P g o o₀ a b a₀ b₀ S
  unfold front
  refine bind_both (hN P o o₀ S) fun _ _ => bind_both (hR o o₀ S) fun _ _ =>
    bind_both (hT o o₀ S) fun _ _ => bind_both (hG P o o₀ S) fun _ _ =>
      bind_both (hO o o₀ S) fun _ _ => bind_both (hP o o₀ S) fun _ _ => ?_
  dsimp only
  by_cases h : (g == 0) = true
  · rw [if_pos h, if_pos h]
    refine bind_both ?_ fun _ _ => pure_both _ _
    rw [Option.isSome_map, Option.isSome_map]
    exact hE o o₀ S
  · rw [if_neg h, if_neg h]
    exact bind_both rfl fun _ _ => pure_both _ _

/-- The whole listing, from the two parts that are not paid beside this file. -/
theorem front_of_two (hN : NormsSkel) (hR : RowsSkel) : FrontSkel :=
  front_of_parts hN hR terms_skel gated_skel oneHot_skel planes_skel embed_skel

/-- **The part FrontSkel.** -/
theorem front_skel : FrontSkel := front_of_two norms_skel rows_skel

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.front_of_parts
#print axioms OnBytes.Desc.First.K4.Total.front_of_two
#print axioms OnBytes.Desc.First.K4.Total.front_skel
