-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPlaceNumber.lean.
The number of the place at which each link of a request's chain stands.

`layer_place` and `att_place` (OnBytes/Tie/Pv/Lookup/Ends/FoPlaces.lean) say that the link of a
group's layers, and of its
attention, stands at some place of the chain. Here the place is a number. Write step for 2 if the
proof covers attention and for 1 if not.

 * `linksPiece`: the one or two links that a pass of the loop of `listLinksH` adds. `fold_pieces`:
   the loop's result as a list: what was there, then the pieces in their order.
 * `pieces_at`: in a list made of pieces of one length n, member r of piece j stands at place
   n · j + r. `pieces_length`: such a list's length.
 * `listLinksH_sizes`: a call of `listLinksH` that returns has tested the numbers of plans.
 * `links_flat`: the links of a request's chain as a list: the pieces of the groups, then the head's
   link.
 * `layer_placeN`: the link of the layers of group g stands at place step · g. `att_placeN`: the
   link of its attention at place 2 · g + 1. `links_sizeN`: there are step · NGr + 1 links, so the
   head's link, which is the last (`linksOf_last`, OnBytes/Tie/Pv/Lookup/Ends/FoBare.lean), stands
     at place step · NGr.
 * `gid_at`: the identifier of the link at each place: 1 + g at step · g, 2 + NGr + g at 2 · g + 1,
   1 + NGr at step · NGr; and every place is one of these.
 * `layer_number`, `att_number`: if the link of the layers, of the attention, of group g stands at
   place i, then i is that number. So the place i of which `passed_places`
     (OnBytes/Tie/Pv/Lookup/Ends/FoPassedPlaces.lean) and
   the statements made of it speak, bound there by the equation on `links[i]`, is named.
 * `layer_tests`, `att_tests`: at these numbers, what the three tests on the number of a place give
   by which the plan of the chain's rounds tells the kinds of links apart: whether it is step · NGr,
   whether step divides it, and its quotient by step. Both are statements on numbers alone: no
   routine of the planner stands in them.
Premise of all statements on links: `linksOf X cov` has returned them. `gid_at` gives of the link at
a place its identifier alone; the whole link: `layer_placeN`, `att_placeN`, `linksOf_last`.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaces

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Model.Verify OnBytes.Model.Stages

/-- What one pass of the loop of `listLinksH` adds. -/
def linksPiece (NGr : Nat) (p4 : Bool) (A : Array SubPlanH) (x : SubPlanH × Nat) : List LinkH :=
  if p4 = true then
    match A[x.2]? with
    | some a =>
      [x.1.link ("G" ++ toString x.2) (1 + x.2) 0 x.2 true,
        a.link ("A" ++ toString x.2) (2 + NGr + x.2) 1 x.2 false]
    | none => [x.1.link ("G" ++ toString x.2) (1 + x.2) 0 x.2 true]
  else [x.1.link ("G" ++ toString x.2) (1 + x.2) 0 x.2 true]

theorem step_piece (NGr : Nat) (p4 : Bool) (A : Array SubPlanH) (acc : Array LinkH)
    (x : SubPlanH × Nat) :
    (linksStep NGr p4 A acc x).toList = acc.toList ++ linksPiece NGr p4 A x := by
  unfold linksStep linksPiece
  by_cases h : p4 = true
  · simp only [h, if_true]
    cases A[x.2]? <;> simp
  · simp [h]

theorem fold_pieces (NGr : Nat) (p4 : Bool) (A : Array SubPlanH) :
    ∀ (l : List (SubPlanH × Nat)) (acc : Array LinkH),
      (l.foldl (linksStep NGr p4 A) acc).toList = acc.toList ++ l.flatMap (linksPiece NGr p4 A)
  | [], acc => by simp
  | x :: l, acc => by
    rw [List.foldl_cons, fold_pieces NGr p4 A l, step_piece, List.flatMap_cons,
      List.append_assoc]

theorem pieces_at {α β : Type} (f : α → List β) (n : Nat) :
    ∀ (l : List α), (∀ x ∈ l, (f x).length = n) → ∀ (j r : Nat), r < n →
      (l.flatMap f)[n * j + r]? = (l[j]?).bind fun x => (f x)[r]?
  | [], _, j, r, _ => by simp
  | x :: l, h, 0, r, hr => by
    have e : (f x).length = n := h x List.mem_cons_self
    rw [List.flatMap_cons, Nat.mul_zero, Nat.zero_add,
      List.getElem?_append_left (by rw [e]; exact hr)]
    rfl
  | x :: l, h, j + 1, r, hr => by
    have e : (f x).length = n := h x List.mem_cons_self
    rw [List.flatMap_cons, List.getElem?_append_right (by rw [e, Nat.mul_succ]; omega), e,
      show n * (j + 1) + r - n = n * j + r by rw [Nat.mul_succ]; omega,
      pieces_at f n l (fun y hy => h y (List.mem_cons_of_mem _ hy)) j r hr]
    rfl

theorem listLinksH_sizes (NGr : Nat) (p4 : Bool) (G A : Array SubPlanH) (H : SubPlanH)
    (links : Array LinkH) (h : listLinksH NGr p4 G A H = .ok links) :
    G.size = NGr ∧ (p4 = true → A.size = NGr) := by
  unfold listLinksH at h
  dsimp only at h
  split at h
  · exact absurd h (by intro x; cases x)
  · rename_i hn
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, not_or, not_and,
      Decidable.not_not] at hn
    exact hn

/-- Every piece has step members, where the plans for attention are there. -/
theorem piece_length (NGr : Nat) (p4 : Bool) (A : Array SubPlanH) (x : SubPlanH × Nat)
    (hA : p4 = true → x.2 < A.size) :
    (linksPiece NGr p4 A x).length = if p4 = true then 2 else 1 := by
  unfold linksPiece
  by_cases h : p4 = true
  · simp only [h, if_true]
    rw [Array.getElem?_eq_getElem (hA h)]
    rfl
  · simp [h]

/-- The links of a request's chain as a list. -/
theorem links_flat (X : Public) (cov : Head.Covered) (links : Array LinkH)
    (h : linksOf X cov = .ok links) :
    links.toList =
      ((X.G.mapIdx fun g hp => layersPlanOf X cov.tokv g hp).toList.zipIdx.flatMap
        (linksPiece X.NGr X.p4 (X.A.map attentionPlanOf))) ++
      [(headPlanOf X cov).link "H" (1 + X.NGr) 2 0 true] := by
  unfold linksOf at h
  rw [listLinksH_eq _ _ _ _ _ _ h, Array.toList_push, fold_pieces]
  rfl

theorem linksOf_sizes (X : Public) (cov : Head.Covered) (links : Array LinkH)
    (h : linksOf X cov = .ok links) : X.G.size = X.NGr ∧ (X.p4 = true → X.A.size = X.NGr) := by
  unfold linksOf at h
  have e := listLinksH_sizes _ _ _ _ _ _ h
  simpa using e

/-- Member r of the piece of group g. -/
theorem links_at (X : Public) (cov : Head.Covered) (links : Array LinkH)
    (h : linksOf X cov = .ok links) (g : Nat) (hp : Layer.HPlan2) (hg : X.G[g]? = some hp)
    (r : Nat) (Y : LinkH)
    (hY : (linksPiece X.NGr X.p4 (X.A.map attentionPlanOf)
      (layersPlanOf X cov.tokv g hp, g))[r]? = some Y) :
    links[(if X.p4 = true then 2 else 1) * g + r]? = some Y := by
  obtain ⟨sG, sA⟩ := linksOf_sizes X cov links h
  have hl : ∀ x ∈ (X.G.mapIdx fun g hp => layersPlanOf X cov.tokv g hp).toList.zipIdx,
      (linksPiece X.NGr X.p4 (X.A.map attentionPlanOf) x).length =
        if X.p4 = true then 2 else 1 := by
    intro x hx
    refine piece_length _ _ _ _ fun h4 => ?_
    have := (List.mem_zipIdx hx).2.1
    simp only [Array.length_toList, Array.size_mapIdx, Nat.zero_add] at this
    rw [Array.size_map, sA h4, ← sG]
    exact this
  have hr : r < if X.p4 = true then 2 else 1 := by
    rw [← hl (layersPlanOf X cov.tokv g hp, g) (by
      have := mem_zipIdx_of (X.G.mapIdx fun g hp => layersPlanOf X cov.tokv g hp).toList 0 g
        (layersPlanOf X cov.tokv g hp) (by simp [hg])
      simpa using this)]
    exact (List.getElem?_eq_some_iff.1 hY).1
  have e := pieces_at (linksPiece X.NGr X.p4 (X.A.map attentionPlanOf)) _ _ hl g r hr
  have ez : ((X.G.mapIdx fun g hp => layersPlanOf X cov.tokv g hp).toList.zipIdx)[g]? =
      some (layersPlanOf X cov.tokv g hp, g) := by
    simp [List.getElem?_zipIdx, hg]
  rw [ez] at e
  have e2 : (((X.G.mapIdx fun g hp => layersPlanOf X cov.tokv g hp).toList.zipIdx.flatMap
      (linksPiece X.NGr X.p4 (X.A.map attentionPlanOf))))[(if X.p4 = true then 2 else 1) * g + r]? =
      some Y := e.trans hY
  rw [← Array.getElem?_toList, links_flat X cov links h,
    List.getElem?_append_left (List.getElem?_eq_some_iff.1 e2).1]
  exact e2

theorem layer_placeN (X : Public) (cov : Head.Covered) (links : Array LinkH)
    (h : linksOf X cov = .ok links) (g : Nat) (hp : Layer.HPlan2) (hg : X.G[g]? = some hp) :
    links[(if X.p4 = true then 2 else 1) * g]? =
      some ((layersPlanOf X cov.tokv g hp).link ("G" ++ toString g) (1 + g) 0 g true) := by
  refine links_at X cov links h g hp hg 0 _ ?_
  unfold linksPiece
  by_cases h4 : X.p4 = true
  · simp only [h4, if_true]
    cases (X.A.map attentionPlanOf)[g]? <;> rfl
  · simp [h4]

theorem att_placeN (X : Public) (cov : Head.Covered) (links : Array LinkH)
    (h : linksOf X cov = .ok links) (h4 : X.p4 = true) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) (a : Attention.Plan) (ha : X.A[g]? = some a) :
    links[2 * g + 1]? =
      some ((attentionPlanOf a).link ("A" ++ toString g) (2 + X.NGr + g) 1 g false) := by
  have e := links_at X cov links h g hp hg 1
    ((attentionPlanOf a).link ("A" ++ toString g) (2 + X.NGr + g) 1 g false) (by
      unfold linksPiece
      simp [h4, ha])
  simpa [h4] using e

theorem pieces_length {α β : Type} (f : α → List β) (n : Nat) :
    ∀ (l : List α), (∀ x ∈ l, (f x).length = n) → (l.flatMap f).length = n * l.length
  | [], _ => by simp
  | x :: l, h => by
    rw [List.flatMap_cons, List.length_append, h x List.mem_cons_self,
      pieces_length f n l fun y hy => h y (List.mem_cons_of_mem _ hy), List.length_cons,
      Nat.mul_succ, Nat.add_comm]

theorem links_sizeN (X : Public) (cov : Head.Covered) (links : Array LinkH)
    (h : linksOf X cov = .ok links) :
    links.size = (if X.p4 = true then 2 else 1) * X.NGr + 1 := by
  obtain ⟨sG, sA⟩ := linksOf_sizes X cov links h
  have hl : ∀ x ∈ (X.G.mapIdx fun g hp => layersPlanOf X cov.tokv g hp).toList.zipIdx,
      (linksPiece X.NGr X.p4 (X.A.map attentionPlanOf) x).length =
        if X.p4 = true then 2 else 1 := by
    intro x hx
    refine piece_length _ _ _ _ fun h4 => ?_
    have := (List.mem_zipIdx hx).2.1
    simp only [Array.length_toList, Array.size_mapIdx, Nat.zero_add] at this
    rw [Array.size_map, sA h4, ← sG]
    exact this
  rw [← Array.length_toList, links_flat X cov links h, List.length_append,
    pieces_length _ _ _ hl]
  simp [sG]

/-- The identifier of the link at each place. -/
theorem gid_at (X : Public) (cov : Head.Covered) (links : Array LinkH)
    (h : linksOf X cov = .ok links) (i : Nat) (hi : i < links.size) :
    (∃ g, g < X.NGr ∧ i = (if X.p4 = true then 2 else 1) * g ∧ (links[i]).gid = 1 + g) ∨
    (∃ g, g < X.NGr ∧ X.p4 = true ∧ i = 2 * g + 1 ∧ (links[i]).gid = 2 + X.NGr + g) ∨
    (i = (if X.p4 = true then 2 else 1) * X.NGr ∧ (links[i]).gid = 1 + X.NGr) := by
  obtain ⟨sG, sA⟩ := linksOf_sizes X cov links h
  have sz := links_sizeN X cov links h
  have atG : ∀ g, g < X.NGr → ∀ (hj : (if X.p4 = true then 2 else 1) * g < links.size),
      (links[(if X.p4 = true then 2 else 1) * g]).gid = 1 + g := by
    intro g hg hj
    have e := layer_placeN X cov links h g X.G[g] (Array.getElem?_eq_getElem (by omega))
    rw [Array.getElem?_eq_getElem hj] at e
    rw [Option.some.inj e]
    rfl
  have atH : ∀ (hj : (if X.p4 = true then 2 else 1) * X.NGr < links.size),
      (links[(if X.p4 = true then 2 else 1) * X.NGr]).gid = 1 + X.NGr := by
    intro hj
    obtain ⟨hl, el⟩ := linksOf_last X cov links h
    have e : links.size - 1 = (if X.p4 = true then 2 else 1) * X.NGr := by omega
    simp only [e] at el
    rw [el]
    rfl
  by_cases h4 : X.p4 = true
  · simp only [h4, if_true] at sz atG atH ⊢
    obtain ⟨g, rfl | rfl⟩ : ∃ g, i = 2 * g ∨ i = 2 * g + 1 := ⟨i / 2, by omega⟩
    · by_cases hg : g < X.NGr
      · exact Or.inl ⟨g, hg, rfl, atG g hg hi⟩
      · obtain rfl : g = X.NGr := by omega
        exact Or.inr (Or.inr ⟨rfl, atH hi⟩)
    · have hg : g < X.NGr := by omega
      have hG : g < X.G.size := by omega
      have hA : g < X.A.size := by
        rw [sA h4]
        exact hg
      refine Or.inr (Or.inl ⟨g, hg, trivial, rfl, ?_⟩)
      have e := att_placeN X cov links h h4 g X.G[g] (Array.getElem?_eq_getElem hG)
        X.A[g] (Array.getElem?_eq_getElem hA)
      rw [Array.getElem?_eq_getElem hi] at e
      rw [Option.some.inj e]
      rfl
  · have hf : X.p4 = false := by simpa using h4
    simp only [hf, Bool.false_eq_true, ↓reduceIte, Nat.one_mul] at sz atG atH ⊢
    by_cases hg : i < X.NGr
    · exact Or.inl ⟨i, hg, rfl, atG i hg hi⟩
    · obtain rfl : i = X.NGr := by omega
      exact Or.inr (Or.inr ⟨rfl, atH hi⟩)

/-- The place of the link of a group's layers is named. -/
theorem layer_number (X : Public) (cov : Head.Covered) (links : Array LinkH)
    (h : linksOf X cov = .ok links) (g : Nat) (hp : Layer.HPlan2) (hg : X.G[g]? = some hp)
    (i : Nat) (hi : i < links.size)
    (ei : links[i] = (layersPlanOf X cov.tokv g hp).link ("G" ++ toString g) (1 + g) 0 g true) :
    i = (if X.p4 = true then 2 else 1) * g := by
  have sG := (linksOf_sizes X cov links h).1
  have hgN : g < X.NGr := by
    rw [← sG]
    exact (Array.getElem?_eq_some_iff.1 hg).1
  have eg : (links[i]).gid = 1 + g := by
    rw [ei]
    rfl
  rcases gid_at X cov links h i hi with ⟨g', _, e, k⟩ | ⟨g', _, _, _, k⟩ | ⟨_, k⟩
  · obtain rfl : g' = g := by omega
    exact e
  · omega
  · omega

/-- The place of the link of a group's attention is named. -/
theorem att_number (X : Public) (cov : Head.Covered) (links : Array LinkH)
    (h : linksOf X cov = .ok links) (g : Nat) (a : Attention.Plan)
    (i : Nat) (hi : i < links.size)
    (ei : links[i] = (attentionPlanOf a).link ("A" ++ toString g) (2 + X.NGr + g) 1 g false) :
    i = 2 * g + 1 := by
  have eg : (links[i]).gid = 2 + X.NGr + g := by
    rw [ei]
    rfl
  rcases gid_at X cov links h i hi with ⟨g', hg', _, k⟩ | ⟨g', _, _, e, k⟩ | ⟨_, k⟩
  · omega
  · obtain rfl : g' = g := by omega
    exact e
  · omega

/-- The three tests on the number of a place, at the place of a group's layers. -/
theorem layer_tests (X : Public) (g : Nat) (hg : g < X.NGr) :
    ((if X.p4 = true then 2 else 1) * g == (if X.p4 = true then 2 else 1) * X.NGr) = false ∧
    ((if X.p4 = true then 2 else 1) * g % (if X.p4 = true then 2 else 1) == 0) = true ∧
    (if X.p4 = true then 2 else 1) * g / (if X.p4 = true then 2 else 1) = g := by
  by_cases h4 : X.p4 = true
  · simp only [h4, if_true, beq_eq_false_iff_ne, beq_iff_eq]
    omega
  · have hf : X.p4 = false := by simpa using h4
    simp only [hf, Bool.false_eq_true, ↓reduceIte, Nat.one_mul, beq_eq_false_iff_ne, beq_iff_eq]
    omega

/-- The same at the place of a group's attention. -/
theorem att_tests (X : Public) (h4 : X.p4 = true) (g : Nat) :
    (2 * g + 1 == (if X.p4 = true then 2 else 1) * X.NGr) = false ∧
    ((2 * g + 1) % (if X.p4 = true then 2 else 1) == 0) = false ∧
    (2 * g + 1) / (if X.p4 = true then 2 else 1) = g := by
  simp only [h4, if_true, beq_eq_false_iff_ne]
  omega

end Fo
