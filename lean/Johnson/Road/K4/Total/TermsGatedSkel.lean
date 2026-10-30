-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/TermsGatedSkel.lean: TWO PARTS OF THE LAW "behind K4's hearing its two runs of
claims return" (Johnson/Road/K4/Total/Returns.lean): TermsSkel and GatedSkel, to the letter: at two
records of one skeleton the listing of the second token sumcheck's shown values (termsForms, group
7 of OnBytes/Desc/First/K4/Claims.lean) returns at both or at neither; and so does the listing of
the gated products' claims (gatedForms, groups 8 and 9). Statements and proofs.

WHAT EACH LISTING's RETURN READS, BIND BY BIND.
termsForms: (1) H.tT: whether the record is there; its field sEnd goes into the forms alone.
  (2) to (4) three lists made item by item, of lengths NN Lam, LamM, LamM NE (the layout's): rowR
  "rt" i; shA "sc" "rt" lm 0; shA "sel" "rt" (x / NE) (x % NE): readers of the environment.
gatedForms: (1), (5) hiTab of the two layers' points: THE LENGTH of the point against numbers of the
  plan's layout; the point's elements go into the weights alone. (2), (6) tabAt. (4) hd2: whether
  the second layer is there. (3), (7) endsForms: T_ "s", T_ "u" (the layout), and two sums of longA.
NO VALUE THAT IS SENT OR DRAWN IS TESTED in either: no comparison of elements, no inverse.

  `bind_tied`: a bind whose two sides are both there or both not, with the two values at hand.
  `termsForms_skel`, `endsForms_skel`, `gatedForms_skel`: over two environments of one skeleton.
  `terms_skel : TermsSkel`, `gated_skel : GatedSkel`: the parts.
No new argument: walks over SkelReaders.lean and IsSomeKit.lean.
**Limits.** The one premise is Skel o o₀ (in the first three: EnvSkel and the clauses that are
read); in the law its payers are Asks.skel's: HearSkel for two returns of the hearing. CONGRUENCES:
neither listing is said to return anywhere: that is the law's premise "member", which no theorem
of this file pays (`member_of_plan`, Johnson/Road/K4/Total/PlanMember.lean, has it from a return of
the hearing and an accept of `frontB`). Nothing on what a form is worth, nothing on soundness.
K04_law, the law of K4's block itself, IS NOT PROVED. Met through Lean at no member; by a run at one
honest proof of each of two sizes both runs of claims return at all 2 and 12 layers' places: that
run is the member.


-/
import Johnson.Road.K4.Total.SkelReaders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Ten Pub Own Heard)

/-- A bind whose two sides are both there or both not, with the two values at hand. -/
theorem bind_tied {α α' β β' : Type} {x : Option α} {y : Option α'} {f : α → Option β}
    {g : α' → Option β'} (hx : x.isSome = y.isSome)
    (h : ∀ a b, x = some a → y = some b → (f a).isSome = (g b).isSome) :
    (x.bind f).isSome = (y.bind g).isSome := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some b => cases hx
  | some a =>
    cases y with
    | none => cases hx
    | some b => exact h a b rfl rfl

variable {v v₀ : Env}

/-- Group 7, over two environments of one skeleton. -/
theorem termsForms_skel (S : EnvSkel v v₀) {H H₀ : Heard} (hT : H.tT.isSome = H₀.tT.isSome) :
    (termsForms v H).isSome = (termsForms v₀ H₀).isSome := by
  unfold termsForms
  rw [S.y]
  refine bind_both hT fun tT tT₀ => ?_
  refine bind_both (mapM_same _ fun i _ => ?_) fun _ _ => ?_
  · rw [Option.isSome_map, Option.isSome_map]
    exact rowR_skel S "rt" i
  refine bind_both (mapM_same _ fun lm _ => ?_) fun _ _ => ?_
  · rw [Option.isSome_map, Option.isSome_map]
    exact shA_skel S "sc" "rt" lm 0
  refine bind_both (mapM_same _ fun x _ => ?_) fun _ _ => pure_both _ _
  rw [Option.isSome_map, Option.isSome_map]
  exact shA_skel S "sel" "rt" _ _

/-- The two claims on a product layer's end values, over two environments of one skeleton: at any
two layers and any two tables of weights. -/
theorem endsForms_skel (S : EnvSkel v v₀) (o o₀ : Level) (e e₀ : Array E)
    (t rows blocks stride : ℕ) (lamOf : ℕ → ℕ) (first : ℕ) :
    (endsForms v o e t rows blocks stride lamOf first).isSome =
      (endsForms v₀ o₀ e₀ t rows blocks stride lamOf first).isSome := by
  have sum : ∀ X : Ten,
      (Layer.sumForms (rows * blocks) fun x =>
        (v.longA t X (lamOf (x / blocks)) (first + x % blocks)).map fun a =>
          (a, e.getD (x / blocks * stride + x % blocks) zeroE)).isSome =
      (Layer.sumForms (rows * blocks) fun x =>
        (v₀.longA t X (lamOf (x / blocks)) (first + x % blocks)).map fun a =>
          (a, e₀.getD (x / blocks * stride + x % blocks) zeroE)).isSome := by
    intro X
    refine sumForms_same _ fun x _ => ?_
    rw [Option.isSome_map, Option.isSome_map]
    exact longA_skel S t X _ _
  unfold endsForms
  rw [S.y]
  exact bind_same _ fun ts => bind_same _ fun tu =>
    bind_both (sum ts) fun _ _ => bind_both (sum tu) fun _ _ => pure_both _ _

/-- Groups 8 and 9, over two environments of one skeleton. -/
theorem gatedForms_skel (S : EnvSkel v v₀) (P : Pub) {hd hd₀ : Level} {hd2 hd2₀ : Option Level}
    (h1 : hd.r.size = hd₀.r.size) (h2 : hd2.map (·.r.size) = hd2₀.map (·.r.size)) :
    (gatedForms P v hd hd2).isSome = (gatedForms P v₀ hd₀ hd2₀).isSome := by
  have h3 : hd2.isSome = hd2₀.isSome := by
    have h := congrArg Option.isSome h2
    rwa [Option.isSome_map, Option.isSome_map] at h
  unfold gatedForms
  rw [tabAt_skel S, tabAt_skel S]
  refine bind_both (hiTab_same h1 _ _) fun e e₀ => bind_same _ fun t =>
    bind_both (endsForms_skel S hd hd₀ e e₀ t _ _ _ _ _) fun _ _ =>
      bind_tied h3 fun o o₀ ho ho₀ => ?_
  have h4 : o.r.size = o₀.r.size := by
    rw [ho, ho₀] at h2
    exact Option.some.inj h2
  exact bind_both (hiTab_same h4 _ _) fun e2 e2₀ => bind_same _ fun t2 =>
    bind_both (endsForms_skel S o o₀ e2 e2₀ t2 _ _ _ _ _) fun _ _ => pure_both _ _

/-- **The part TermsSkel.** -/
theorem terms_skel : TermsSkel := fun _ _ S => termsForms_skel S.v S.tT

/-- **The part GatedSkel.** -/
theorem gated_skel : GatedSkel := fun P _ _ S => gatedForms_skel S.v P S.hd S.hd2

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.bind_tied
#print axioms OnBytes.Desc.First.K4.Total.termsForms_skel
#print axioms OnBytes.Desc.First.K4.Total.endsForms_skel
#print axioms OnBytes.Desc.First.K4.Total.gatedForms_skel
#print axioms OnBytes.Desc.First.K4.Total.terms_skel
#print axioms OnBytes.Desc.First.K4.Total.gated_skel
