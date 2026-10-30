-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/K4/RowsLaws.lean: the members of groups 4 to 6 of the layers' own rounds, norm by
norm.

`rowsForms` (OnBytes/Desc/First/K4/Claims.lean) lists, for all norms of a group, four claims on the
shown end values, nine carries and eight lines. Here: where the list is there, each norm's row of
digits is there at both token points, and that norm's 21 forms are members of the list.

  `mapM_get`: member i of a list made by mapM is made of member i.
  `rowsForms_mem`: the 21 forms of norm i.

Limits. Membership in a list: nothing on what a form is worth, on a draw, on soundness.

-/
import OnBytes.Desc.First.K4.Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest

theorem mapM_get {α β : Type} (f : α → Option β) : ∀ (xs : List α) (L : List β),
    xs.mapM f = some L → ∀ (i : Nat) (a : α), xs[i]? = some a →
      ∃ b, f a = some b ∧ L[i]? = some b
  | [], _, _, i, a, hi => by simp at hi
  | x :: xs, L, h, i, a, hi => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨bs, hbs, h2⟩ := Option.bind_eq_some_iff.mp h1
    have e : L = b :: bs := (Option.some.inj h2).symm
    subst e
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact ⟨b, hb, by simp⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨c, hc, hl⟩ := mapM_get f xs bs hbs j a hi
      exact ⟨c, hc, by simpa using hl⟩

theorem mapM_range_get {β : Type} (f : Nat → Option β) {n : Nat} {L : List β}
    (h : (List.range n).mapM f = some L) {i : Nat} (hi : i < n) :
    ∃ b, f i = some b ∧ L[i]? = some b :=
  mapM_get f _ L h i i (by simp [hi])

/-- The 21 forms of norm i are members of the list. Dr, Dp: the norm's digits at the token
sumcheck's end point and at the norms' token point. -/
theorem rowsForms_mem {v : Env} {H : Heard} {l : List Aff} (h : rowsForms v H = some l) {i : Nat}
    (hi : i < v.y.NI) :
    ∃ Dr Dp, digitsAt v "r_tV" i = some Dr ∧ digitsAt v "P_V" i = some Dp ∧
      (∀ f ∈ ([(P6.Row.ofDigits Dr).a, (P6.Row.ofDigits Dr).b, (P6.Row.ofDigits Dr).Rlo,
          (P6.Row.ofDigits Dr).Rhi].zipIdx.map fun x =>
            Aff.slot (H.tV.sEnd + 4 * i + x.2) - x.1), f ∈ l) ∧
      (∀ f ∈ P6.carries (P6.Row.ofDigits Dp) Dp (fun s => Aff.slot (H.sW + 9 * i + s)), f ∈ l) ∧
      (∀ f ∈ P6.lines (P6.Row.ofDigits Dp) (fun j => Aff.slot (H.sPv + 7 * i + j)) (epsOf v.y i)
          (twoM v i), f ∈ l) := by
  unfold rowsForms at h
  obtain ⟨ends, a1, h1⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Ds, a2, h2⟩ := Option.bind_eq_some_iff.mp h1
  have e := (Option.some.inj h2).symm
  obtain ⟨b, hb, gb⟩ := mapM_range_get _ a1 hi
  obtain ⟨Dr, hDr, eb⟩ := Option.map_eq_some_iff.mp hb
  obtain ⟨Dp, hDp, gD⟩ := mapM_range_get _ a2 hi
  have mD : (Dp, i) ∈ Ds.zipIdx := List.mem_zipIdx_iff_getElem?.mpr gD
  refine ⟨Dr, Dp, hDr, hDp, ?_, ?_, ?_⟩
  · intro f hf
    rw [e]
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_flatten.mpr ⟨b, ?_, ?_⟩))
    · exact List.mem_of_getElem? gb
    · rw [← eb]; exact hf
  · intro f hf
    rw [e]
    refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, ?_, hf⟩))
    exact List.mem_map.mpr ⟨(Dp, i), mD, rfl⟩
  · intro f hf
    rw [e]
    refine List.mem_append_right _ (List.mem_flatten.mpr ⟨_, ?_, hf⟩)
    exact List.mem_map.mpr ⟨(Dp, i), mD, rfl⟩

end OnBytes.Desc.First.K4
