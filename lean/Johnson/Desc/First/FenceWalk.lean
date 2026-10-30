-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/FenceWalk.lean: THE TABLE's TEST `fenceFit` (Johnson/Desc/First/FenceFit.lean)
FROM ONE WALK OVER THE OPEN SETS: a Bool that goes once through the list of open sets, border by
border, and that gives `fenceFit` at the numbers filled off what the sub-protocols tell. Two
definitions, two theorems. A file beside the table: it turns nothing of it.
Why. `fenceFit` asks, at each of the borders, for member k of `openSets links ps (start links)`:
as it is written that list is made anew at every border. At the full size there are 359 borders:
an evaluation by Lean's kernel would make the list 359 times. Here the list is an argument and is
walked once; the general step to `fenceFit` is a theorem, with no evaluation.
  `fenceFrom N told k Os`: at each member O of Os, the first standing at border k: every sampled
  tenant of a pin that is open in O sits in a tree below `treesTold told` of that border.
  `fenceCount N Os`: over how many (border, tenant) pairs that test ranges: so that an accept can
  be seen not to be empty.
  `fenceFrom_at`: what an accept says at member i.
  `fenceFit_of_walk`: **where the places are different from each other and the walk from border 0
  accepts, `fenceFit (N.withTold ps told) links ps = true`**: by `fenceFit_withTold`
  (Johnson/Desc/First/FenceFitTold.lean).
Limits. One direction alone. Nothing is evaluated here. WHERE THE NUMBERS NAME NO SAMPLED TENANT
THE WALK ACCEPTS FOR WANT OF MEMBERS: `fenceCount` is there to show it. No probability: no
soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.FenceFitTold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc

/-- One walk over the open sets: the first member stands at border k. -/
def fenceFrom (N : Numbers) (told : List (List Oracle)) : Nat → List (List Item) → Bool
  | _, [] => true
  | k, O :: Os =>
    ((sampledIn N O).all fun x => decide (x.1 < treesTold told k)) && fenceFrom N told (k + 1) Os

/-- Over how many (border, tenant) pairs the walk ranges. -/
def fenceCount (N : Numbers) (Os : List (List Item)) : Nat :=
  (Os.map fun O => (sampledIn N O).length).sum

/-- What an accept of the walk says at member i. -/
theorem fenceFrom_at (N : Numbers) (told : List (List Oracle)) :
    ∀ (Os : List (List Item)) (k : Nat), fenceFrom N told k Os = true →
      ∀ (i : Nat) (O : List Item), Os[i]? = some O → ∀ x ∈ sampledIn N O,
        x.1 < treesTold told (k + i)
  | [], _, _, _, _, hO, _, _ => by simp at hO
  | O' :: Os, k, h, 0, O, hO, x, hx => by
    have e : O' = O := by simpa using hO
    subst e
    unfold fenceFrom at h
    rw [Bool.and_eq_true] at h
    exact of_decide_eq_true (List.all_eq_true.1 h.1 x hx)
  | O' :: Os, k, h, i + 1, O, hO, x, hx => by
    unfold fenceFrom at h
    rw [Bool.and_eq_true] at h
    have hO' : Os[i]? = some O := by simpa using hO
    have t := fenceFrom_at N told Os (k + 1) h.2 i O hO' x hx
    rwa [Nat.add_assoc, Nat.add_comm 1 i] at t

/-- **From one walk to the table's test, at the numbers filled off what is told.** -/
theorem fenceFit_of_walk (N : Numbers) (links : List ModelPart) (ps : List Place)
    (told : List (List Oracle)) (hn : ps.Nodup)
    (h : fenceFrom N told 0 (openSets links ps (start links)) = true) :
    fenceFit (N.withTold ps told) links ps = true :=
  (fenceFit_withTold N links ps told hn).2 fun k _ x hx => by
    cases hO : (openSets links ps (start links))[k]? with
    | none =>
      rw [hO] at hx
      simp [sampledIn] at hx
    | some O =>
      rw [hO] at hx
      have t := fenceFrom_at N told _ 0 h k O hO x hx
      rwa [Nat.zero_add] at t

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.fenceFrom_at
#print axioms VerifiableInference.Desc.First.fenceFit_of_walk
