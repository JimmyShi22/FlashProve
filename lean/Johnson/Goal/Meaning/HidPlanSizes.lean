-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidPlanSizes.lean: sizes that follow the verifier's plans have, at an attention
sub-proof, the sizes PlanSizes; so in scope every valid name's place lies within them.

inside_of_plan (Johnson/Goal/Meaning/HidLaws.lean) asks PlanSizes s S: the sizes s are those of the
list that the verifier's function matrices (OnBytes/Model/AttentionPlan.lean) lays for the shape S.
Johnson/Goal/Meaning/HidPlan.lean has Follows X s: the sizes s k are those of the lists in X's own
plans. This file joins the two.

Main names:
  matsAt_att   in scope the list in the plan X.A[g] is what matrices lays for Hd.shapeA X g, but for
    two fields (foreign, ttOff) of the borrowed entry (the library's plan_mats, owners_plan,
    groups_of_public).
  planSizes_of_follows   Follows X s gives PlanSizes (s (2 g + 1)) (Hd.shapeA X g), in scope.
  inside_of_follows   so Inside (s (2 g + 1)) (Hd.shapeA X g).
  attOrd_follows   so the library's record on an attention sub-proof goes from zsOf pl (mzAt (y k))
    to ownOf s y k under PlaceOK and Follows alone.

What is not claimed. That a real signature follows the plans (Follows). The full size alone. The
program does not import this file.
-/
import Johnson.Goal.Meaning.HidPlan
import Johnson.Goal.Meaning.HidFills
import Johnson.Road.Lane5AttOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes OnBytes.Road OnBytes.Road.L5
open OnBytes.Model (TMat)
open OnBytes.Model.Verify (publicOf layerShape)
open Cb.Pv.Tail (Size Syms JCell)

theorem fixed_m (M : TMat) : (fixed M).m = M.m := by
  unfold fixed
  split <;> rfl

theorem fixed_k (M : TMat) : (fixed M).k = M.k := by
  unfold fixed
  split <;> rfl

/-- A member that is there is what getD returns. -/
theorem getD_of {a : Array TMat} {n : ℕ} {M : TMat} (h : a[n]? = some M) : a.getD n {} = M := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- A part of as in the list. -/
theorem matrices_as (S : Attention.Shape) (i : Attention.In) {q : ℕ} (hq : q < S.cf.NAs) :
    ∃ M, (Attention.matrices S i)[q]? = some M ∧ M.m = 2 ^ S.cf.lmS ∧ M.k = S.kAs / S.cf.NAs := by
  refine ⟨Attention.ownMatrix i ("as" ++ toString q) (2 ^ S.cf.lmS) (S.kAs / S.cf.NAs) q i.wpS, ?_,
    rfl, rfl⟩
  unfold Attention.matrices
  rw [Array.getElem?_append_left (by simpa using hq)]
  simp [hq]

/-- The four entries behind the parts of as. -/
theorem matrices_tail (S : Attention.Shape) (i : Attention.In) (j : ℕ) :
    (Attention.matrices S i)[S.cf.NAs + j]? =
      (#[Attention.ownMatrix i "ah" (S.cf.wcH * S.T) (S.fillH / S.cf.wcH) S.cf.NAs i.wph,
        Attention.ownMatrix i "ao" (S.cf.wcO * S.T) (S.fillO / S.cf.wcO) (S.cf.NAs + 1) i.wpo,
        Attention.ownMatrix i "bA" (2 ^ S.cf.lmb) S.kbA (S.cf.NAs + 2) i.wpbA,
        { name := "qa", m := S.cf.wcQ * S.T, k := S.fillQ / S.cf.wcQ, kind := 1, foreign := some 0,
          aId := i.midQ, wp := i.wpq }] : Array TMat)[j]? := by
  unfold Attention.matrices
  exact append_at _ _ j (by simp)

theorem matrices_size (S : Attention.Shape) (i : Attention.In) :
    (Attention.matrices S i).size = S.cf.NAs + 4 := by
  unfold Attention.matrices
  simp

section Core
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **In scope the list in the plan X.A[g] is what the verifier's function matrices lays for the
shape.** -/
theorem matsAt_att (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {g : ℕ} (hg : g < 12) :
    ∃ i : Attention.In,
      matsAt X (2 * g + 1) = (Attention.matrices (Hd.shapeA X g) i).map fixed := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨lines, A0, seenG, seenA, hO, H⟩ := Hd.groups_of_public h B.p4
  obtain ⟨Xg, Ag, s, hG, h0, hs, hA, -, -, -, etl, eS⟩ := H g (by rw [B.groups]; exact hg)
  obtain ⟨cf, -, hp, -⟩ := group_plan hG
  have e : matsAt X (2 * g + 1) = Ag.seam.tl.mats := by
    unfold matsAt tlAt
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      show (2 * g + 1) / 2 = g by omega, hA]
    rfl
  exact ⟨Xg.inp, by rw [e, etl, owners_plan hO h0 hs, plan_mats hp, eS]⟩

/-- **Sizes that follow the plans are the sizes of the plan's list.** -/
theorem planSizes_of_follows (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    {s : ℕ → Size} (F : Follows X s) {g : ℕ} (hg : g < 12) :
    PlanSizes (s (2 * g + 1)) (Hd.shapeA X g) := by
  obtain ⟨i, e⟩ := matsAt_att h C hg
  have at' : ∀ {n : ℕ} {M : TMat}, (Attention.matrices (Hd.shapeA X g) i)[n]? = some M →
      (s (2 * g + 1)).m n = M.m ∧ (s (2 * g + 1)).k n = M.k := by
    intro n M hM
    have k : (matsAt X (2 * g + 1)).getD n {} = fixed M := getD_of (by
      rw [e, Array.getElem?_map, hM]
      rfl)
    have hn : n < (matsAt X (2 * g + 1)).size := by
      rw [e, Array.size_map]
      exact (Array.getElem?_eq_some_iff.1 hM).1
    rw [F.m _ (by omega) n hn, F.k _ (by omega) n hn, k, fixed_m, fixed_k]
    exact ⟨rfl, rfl⟩
  have t := matrices_tail (Hd.shapeA X g) i
  refine ⟨?_, fun q hq => ?_, fun q hq => ?_, (at' (t 0)).1, (at' (t 0)).2, (at' (t 1)).1,
    (at' (t 1)).2, (at' (t 3)).1, (at' (t 3)).2⟩
  · rw [F.NM _ (by omega), e, Array.size_map, matrices_size]
  · obtain ⟨M, hM, h1, -⟩ := matrices_as (Hd.shapeA X g) i hq
    rw [(at' hM).1, h1]
  · obtain ⟨M, hM, -, h2⟩ := matrices_as (Hd.shapeA X g) i hq
    rw [(at' hM).2, h2]

/-- **In scope every valid name's place lies within sizes that follow the plans.** -/
theorem inside_of_follows (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {s : ℕ → Size}
    (F : Follows X s) {g : ℕ} (hg : g < 12) : Inside (s (2 * g + 1)) (Hd.shapeA X g) :=
  inside_of_core h C hg (planSizes_of_follows h C F hg)

/-- **The library's record on an attention sub-proof, from the map of places to the list behind the
committed symbols**, under PlaceOK and Follows alone. -/
theorem attOrd_follows (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {s : ℕ → Size}
    (F : Follows X s) {y : ∀ k, Syms Cb.Gl.E (s k)} {g : ℕ} (hg : g < 12)
    {pl : ℕ → ℕ → ℕ → JCell (s (2 * g + 1))} (hp : Rows.PlaceOK pl)
    (O : AttOrd (Hd.shapeA X g) (Rows.zsOf pl (Rows.mzAt (y (2 * g + 1))))) :
    AttOrd (Hd.shapeA X g) (ownOf s y (2 * g + 1)) :=
  attOrd_ownOf hp (inside_of_follows h C F hg) O

end Core

end Meaning

#print axioms Meaning.fixed_m
#print axioms Meaning.fixed_k
#print axioms Meaning.getD_of
#print axioms Meaning.matrices_as
#print axioms Meaning.matrices_tail
#print axioms Meaning.matrices_size
#print axioms Meaning.matsAt_att
#print axioms Meaning.planSizes_of_follows
#print axioms Meaning.inside_of_follows
#print axioms Meaning.attOrd_follows
