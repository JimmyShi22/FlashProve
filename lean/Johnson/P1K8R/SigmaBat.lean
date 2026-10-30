-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/SigmaBat.lean: the proofs of the three statements of
Johnson/P1K8R/SigmaBatStatement.lean, to the letter, and one helper. Lemmas; none of the library's
goals.

How. `sigmaBat_cons2`: the definition's first arm, by unfolding. `sigmaBat_append`: by induction on
the first list, the list of one member apart. `sigmaBat_mid`: the law twice. `sigmaBat_family`: by
induction on the family.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.P1K8R.SigmaBatStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8

/-- The definition's first arm. -/
theorem sigmaBat_cons2 (a b : Fmt.Entry) (t : List Fmt.Entry) :
    sigmaBat (a :: b :: t) =
      (if a.name == "BAT-sigma" && b.name == "BAT" then [a.rows] else []) ++ sigmaBat (b :: t) :=
  rfl

/-- **Joining takes no pair away.** -/
theorem sigmaBat_append : SigmaBatAppend := by
  intro A
  induction A with
  | nil => exact fun B => List.Sublist.refl _
  | cons a A' ih =>
    intro B
    cases A' with
    | nil =>
      cases B with
      | nil => exact List.Sublist.refl _
      | cons b t =>
        show (sigmaBat (b :: t)).Sublist (sigmaBat (a :: b :: t))
        rw [sigmaBat_cons2]
        exact List.sublist_append_right _ _
    | cons b t =>
      show (sigmaBat (a :: b :: t) ++ sigmaBat B).Sublist (sigmaBat (a :: b :: (t ++ B)))
      rw [sigmaBat_cons2, sigmaBat_cons2, List.append_assoc]
      exact (List.Sublist.refl _).append (ih B)

/-- **One pair.** -/
theorem sigmaBat_mid : SigmaBatMid := by
  intro pre post x b hx hb
  have e : sigmaBat (x :: b :: post) = [x.rows] ++ sigmaBat (b :: post) := by
    rw [sigmaBat_cons2, hx, hb]
    rfl
  have s1 : [x.rows].Sublist (sigmaBat (x :: b :: post)) := by
    rw [e]
    exact List.sublist_append_left _ _
  exact (s1.trans (List.sublist_append_right _ _)).trans (sigmaBat_append pre (x :: b :: post))

/-- **A family.** -/
theorem sigmaBat_family : SigmaBatFamily := by
  intro α f r l
  induction l with
  | nil => exact fun _ rest => List.nil_sublist _
  | cons x l ih =>
    intro h rest
    rw [List.flatMap_cons, List.append_assoc, List.map_cons]
    exact ((h x List.mem_cons_self).append
      (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) rest)).trans (sigmaBat_append _ _)

end P1K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms P1K8.sigmaBat_cons2
#print axioms P1K8.sigmaBat_append
#print axioms P1K8.sigmaBat_mid
#print axioms P1K8.sigmaBat_family
