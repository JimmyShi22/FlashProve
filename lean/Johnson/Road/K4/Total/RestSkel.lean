-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/RestSkel.lean: THREE PARTS OF THE LAW "behind K4's hearing its two runs of
claims return" (Johnson/Road/K4/Total/Returns.lean): OneHotSkel, EmbedSkel and PlanesSkel, to the
letter: at two records of one skeleton the listing returns at both or at neither: oneHotForms (group
10 of OnBytes/Desc/First/K4/Claims.lean), embeddingForm (group 12), planesParts (group 11).
Statements and proofs.

WHAT EACH LISTING's RETURN READS, BIND BY BIND.
oneHotForms: a list of LamM items, each a sum of NE terms shA "sel" "zt" lm e: the environment.
embeddingForm: tabAt "xbI@Z_E"; a sum of d / S2 terms xbA t kh: the environment. The point tkh and
  the slot sVE go into the form alone.
planesParts: three tabAt; the public condition planeCols on THE LOOKUP's SHAPE and the layout's lmb;
  two sums planesAt and one count, each over NC * 2 ^ (kT + 5 - lmb) columns (the shape's numbers),
  of U3at under the test x < kbm (the layout's). The lookup's points zb and its element leavesA go
  into weights alone.
NO VALUE THAT IS SENT OR DRAWN IS TESTED in any of the three.

  `oneHotForms_skel`, `embeddingForm_skel`, `planesAt_skel`, `planesParts_skel`: over two
    environments of one skeleton (and, for the planes, two lookups of one shape).
  `oneHot_skel : OneHotSkel`, `embed_skel : EmbedSkel`, `planes_skel : PlanesSkel`: the parts.
No new argument: walks over SkelReaders.lean and IsSomeKit.lean.
**Limits.** The one premise is Skel o o₀ (of it: EnvSkel; for the planes the shape too); in the law
its payers are Asks.skel's. CONGRUENCES: no listing is said to return anywhere: that is the law's
premise "member", which no theorem of this file pays (`member_of_plan`,
Johnson/Road/K4/Total/PlanMember.lean, has it from a return of the hearing and an accept of
`frontB`). Nothing on what a form is worth, nothing on soundness. K04_law, the law of K4's block
itself, IS NOT PROVED. Met through Lean at no member; by a run at one honest proof of each of two
sizes both runs of claims return at all 2 and 12 layers' places: that run is the member.


-/
import Johnson.Road.K4.Total.SkelReaders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Heard)

variable {v v₀ : Env}

/-- Group 10, over two environments of one skeleton. -/
theorem oneHotForms_skel (S : EnvSkel v v₀) :
    (oneHotForms v).isSome = (oneHotForms v₀).isSome := by
  unfold oneHotForms
  rw [S.y]
  refine mapM_same _ fun lm _ => ?_
  rw [Option.isSome_map, Option.isSome_map]
  refine sumForms_same _ fun e _ => ?_
  rw [Option.isSome_map, Option.isSome_map]
  exact shA_skel S "sel" "zt" lm e

/-- Group 12, over two environments of one skeleton: at any two hearings and slots. -/
theorem embeddingForm_skel (S : EnvSkel v v₀) (H H₀ : Heard) (s s₀ : ℕ) :
    (embeddingForm v H s).isSome = (embeddingForm v₀ H₀ s₀).isSome := by
  unfold embeddingForm
  rw [tabAt_skel S, S.y]
  refine bind_same _ fun t => bind_both (sumForms_same _ fun kh _ => ?_) fun _ _ => pure_both _ _
  rw [Option.isSome_map, Option.isSome_map]
  exact xbA_skel S t kh

/-- A sum over the planes' columns, at two lookups of one shape. -/
theorem planesAt_skel {g g₀ : Forest.Heard} (hs : g.shape = g₀.shape) (lm e : ℕ)
    {bit bit₀ : ℕ → ℕ → Option Aff} (hb : ∀ col, (bit e col).isSome = (bit₀ e col).isSome) :
    (planesAt g lm e bit).isSome = (planesAt g₀ lm e bit₀).isSome := by
  unfold planesAt
  rw [hs]
  exact foldlM_same _ _ _ (fun col _ => hb col) _ _

/-- Group 11, over two environments of one skeleton and two lookups of one shape. -/
theorem planesParts_skel (S : EnvSkel v v₀) {fo fo₀ : Forest.Heard}
    (hs : fo.shape = fo₀.shape) : (planesParts v fo).isSome = (planesParts v₀ fo₀).isSome := by
  have col : ∀ t x, (if x < v₀.y.kbm then v.U3at t x else none).isSome =
      (if x < v₀.y.kbm then v₀.U3at t x else none).isSome := by
    intro t x
    by_cases hx : x < v₀.y.kbm
    · rw [if_pos hx, if_pos hx]
      exact U3at_skel S t x
    · rw [if_neg hx, if_neg hx]
  unfold planesParts
  rw [tabAt_skel S, tabAt_skel S, tabAt_skel S, S.y, hs]
  exact bind_same _ fun tB0 => bind_same _ fun tB1 => bind_same _ fun tP => bind_same _ fun _ =>
    bind_both (planesAt_skel hs _ 0 fun c => col _ c) fun _ _ =>
      bind_both (planesAt_skel hs _ 1 fun c => col _ c) fun _ _ =>
        bind_both (foldlM_same _ _ _ (fun c _ => col tP c) _ _) fun _ _ => pure_both _ _

/-- **The part OneHotSkel.** -/
theorem oneHot_skel : OneHotSkel := fun _ _ S => oneHotForms_skel S.v

/-- **The part EmbedSkel.** -/
theorem embed_skel : EmbedSkel := fun o o₀ S => embeddingForm_skel S.v o.H o₀.H o.sVE o₀.sVE

/-- **The part PlanesSkel.** -/
theorem planes_skel : PlanesSkel := fun _ _ S => planesParts_skel S.v S.shape

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.oneHotForms_skel
#print axioms OnBytes.Desc.First.K4.Total.embeddingForm_skel
#print axioms OnBytes.Desc.First.K4.Total.planesAt_skel
#print axioms OnBytes.Desc.First.K4.Total.planesParts_skel
#print axioms OnBytes.Desc.First.K4.Total.oneHot_skel
#print axioms OnBytes.Desc.First.K4.Total.embed_skel
#print axioms OnBytes.Desc.First.K4.Total.planes_skel
