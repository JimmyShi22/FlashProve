-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/LinksOrder.lean: the order of the program's own list of links, place by place.

listLinksH (OnBytes/Model/StagesLinks.lean) makes the links of a request's chain from the plans of
the sub-proofs, in a loop; Verify.linksOf (OnBytes/Model/VerifyLinks.lean) calls it with the plans
of the public record. This file says which link stands at which place.

Main names:
  `stepL`, `listLinksH_fold`: the loop as a fold without refusal.
  `linkG`, `linkA`, `linkHd`: the link of the layers of group g, of the attention of group g, and of
    the head, from their plans, with the names, identifiers and kinds that listLinksH gives.
  `listLinksH_with`: where listLinksH succeeds and the proof covers attention: there are NGr plans
    of either kind; the list has 2 NGr + 1 links; at the place 2 g stands the link of the layers of
    group g, at 2 g + 1 that of its attention, at 2 NGr the head's.
  `listLinksH_without`: where the proof does not cover attention: NGr + 1 links; at the place g the
    layers of group g, at NGr the head.
  `linksOf_layers`, `linksOf_attention`, `linksOf_head`, `linksOf_size`: the same for
    Verify.linksOf, with the plans named by their index in the public record: the layers' link at
    the place `layersLink` p4 g.

Limits: on the list that listLinksH returns alone. The stage request zips that list with the links
as built and takes the routine alone from it: of the zipped list's other fields nothing is said
here.
-/
import OnBytes.Model.VerifyLinks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.L5.LinksOrder
open OnBytes OnBytes.Model OnBytes.Model.Stages

/-- the link of the layers of group g -/
def linkG (s : SubPlanH) (g : Nat) : LinkH := s.link ("G" ++ toString g) (1 + g) 0 g true

/-- the link of the attention of group g -/
def linkA (NGr : Nat) (a : SubPlanH) (g : Nat) : LinkH :=
  a.link ("A" ++ toString g) (2 + NGr + g) 1 g false

/-- the head's link -/
def linkHd (NGr : Nat) (H : SubPlanH) : LinkH := H.link "H" (1 + NGr) 2 0 true

/-- One step of the loop. -/
def stepL (NGr : Nat) (p4 : Bool) (A : Array SubPlanH) (links : Array LinkH)
    (x : SubPlanH × Nat) : Array LinkH :=
  if p4 then
    match A[x.2]? with
    | some a => (links.push (linkG x.1 x.2)).push (linkA NGr a x.2)
    | none => links.push (linkG x.1 x.2)
  else links.push (linkG x.1 x.2)

theorem forIn_fold {α β : Type} (f : β → α → β)
    (body : α → β → Except String (ForInStep β)) (hb : ∀ a b, body a b = .ok (.yield (f b a))) :
    ∀ (l : List α) (b : β), forIn l b body = (.ok (l.foldl f b) : Except String β)
  | [], _ => rfl
  | a :: l, b => by
    rw [List.forIn_cons, hb]
    exact forIn_fold f body hb l (f b a)

theorem listLinksH_fold (NGr : Nat) (p4 : Bool) (G A : Array SubPlanH) (H : SubPlanH) :
    listLinksH NGr p4 G A H =
      if G.size != NGr || (p4 && A.size != NGr) then .error "plan-link"
      else .ok ((G.toList.zipIdx.foldl (stepL NGr p4 A) #[]).push (linkHd NGr H)) := by
  unfold listLinksH
  by_cases hc : (G.size != NGr || (p4 && A.size != NGr)) = true
  · rw [if_pos hc, if_pos hc]
    rfl
  · rw [if_neg hc, if_neg hc]
    show (do
      let r ← forIn G.toList.zipIdx (#[] : Array LinkH) _
      pure (r.push (H.link "H" (1 + NGr) 2 0 true)) : Except String (Array LinkH)) = _
    rw [forIn_fold (stepL NGr p4 A) _ (fun x b => by
      obtain ⟨s, g⟩ := x
      unfold stepL
      cases p4 with
      | false => rfl
      | true =>
        show (match A[g]? with
          | some a => _
          | x => _ : Except String (ForInStep (Array LinkH))) = _
        cases A[g]? <;> rfl)]
    rfl

/-! ## The fold, in closed form -/

/-- The links of the groups from g0 on, with attention. -/
def pairs (NGr : Nat) : List SubPlanH → List SubPlanH → Nat → List LinkH
  | s :: G, a :: A, g => linkG s g :: linkA NGr a g :: pairs NGr G A (g + 1)
  | _, _, _ => []

theorem fold_with (NGr : Nat) (A : Array SubPlanH) : ∀ (G : List SubPlanH) (g0 : Nat)
    (acc : Array LinkH), g0 + G.length = A.size →
    ((G.zipIdx g0).foldl (stepL NGr true A) acc).toList =
      acc.toList ++ pairs NGr G (A.toList.drop g0) g0
  | [], g0, acc, _ => by simp [pairs]
  | s :: G, g0, acc, h => by
    have hlt : g0 < A.size := by
      rw [← h, List.length_cons]
      omega
    have hA : A[g0]? = some A[g0] := Array.getElem?_eq_getElem hlt
    have hd : A.toList.drop g0 = A[g0] :: A.toList.drop (g0 + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]
      simp
    rw [List.zipIdx_cons, List.foldl_cons, fold_with NGr A G (g0 + 1) _ (by
      rw [← h, List.length_cons]
      omega), hd]
    show (stepL NGr true A acc (s, g0)).toList ++ _ = _
    unfold stepL
    simp only [if_true, hA, pairs]
    simp

theorem fold_without (NGr : Nat) (A : Array SubPlanH) : ∀ (G : List SubPlanH) (g0 : Nat)
    (acc : Array LinkH),
    ((G.zipIdx g0).foldl (stepL NGr false A) acc).toList =
      acc.toList ++ (G.zipIdx g0).map fun x => linkG x.1 x.2
  | [], _, acc => by simp
  | s :: G, g0, acc => by
    rw [List.zipIdx_cons, List.foldl_cons, fold_without NGr A G (g0 + 1) _]
    show (acc.push (linkG s g0)).toList ++ _ = _
    simp

theorem pairs_at (NGr : Nat) : ∀ (G A : List SubPlanH) (g0 g : Nat) (s a : SubPlanH),
    G[g]? = some s → A[g]? = some a →
    (pairs NGr G A g0)[2 * g]? = some (linkG s (g0 + g)) ∧
      (pairs NGr G A g0)[2 * g + 1]? = some (linkA NGr a (g0 + g))
  | [], _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, h => by simp at h
  | s0 :: G, a0 :: A, g0, 0, s, a, hs, ha => by
    have e1 : s0 = s := by simpa using hs
    have e2 : a0 = a := by simpa using ha
    rw [e1, e2]
    exact ⟨rfl, rfl⟩
  | s0 :: G, a0 :: A, g0, g + 1, s, a, hs, ha => by
    obtain ⟨h1, h2⟩ := pairs_at NGr G A (g0 + 1) g s a (by simpa using hs) (by simpa using ha)
    have e : g0 + 1 + g = g0 + (g + 1) := by omega
    rw [e] at h1 h2
    refine ⟨?_, ?_⟩
    · show (linkG s0 g0 :: linkA NGr a0 g0 :: pairs NGr G A (g0 + 1))[2 * (g + 1)]? = _
      rw [show 2 * (g + 1) = 2 * g + 1 + 1 by omega, List.getElem?_cons_succ,
        List.getElem?_cons_succ]
      exact h1
    · show (linkG s0 g0 :: linkA NGr a0 g0 :: pairs NGr G A (g0 + 1))[2 * (g + 1) + 1]? = _
      rw [show 2 * (g + 1) + 1 = 2 * g + 1 + 1 + 1 by omega, List.getElem?_cons_succ,
        List.getElem?_cons_succ]
      exact h2

theorem pairs_length (NGr : Nat) : ∀ (G A : List SubPlanH) (g0 : Nat), G.length = A.length →
    (pairs NGr G A g0).length = 2 * G.length
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | _ :: G, _ :: A, g0, h => by
    show (pairs NGr G A (g0 + 1)).length + 1 + 1 = _
    rw [pairs_length NGr G A (g0 + 1) (by simpa using h), List.length_cons]
    omega

/-! ## The places -/

theorem listLinksH_with (NGr : Nat) (G A : Array SubPlanH) (H : SubPlanH) (Z : Array LinkH)
    (h : listLinksH NGr true G A H = .ok Z) :
    G.size = NGr ∧ A.size = NGr ∧ Z.size = 2 * NGr + 1 ∧
      (∀ g s a, G[g]? = some s → A[g]? = some a →
        Z[2 * g]? = some (linkG s g) ∧ Z[2 * g + 1]? = some (linkA NGr a g)) ∧
      Z[2 * NGr]? = some (linkHd NGr H) := by
  rw [listLinksH_fold] at h
  by_cases hc : (G.size != NGr || (true && A.size != NGr)) = true
  · rw [if_pos hc] at h
    cases h
  · rw [if_neg hc] at h
    have hZ := (Except.ok.inj h).symm
    have hG : G.size = NGr := Decidable.byContradiction fun e => hc (by simp [e])
    have hA : A.size = NGr := Decidable.byContradiction fun e => hc (by simp [e])
    have hl : Z.toList = pairs NGr G.toList A.toList 0 ++ [linkHd NGr H] := by
      rw [hZ, Array.toList_push, fold_with NGr A G.toList 0 #[] (by simp [hG, hA])]
      simp
    have hlen : (pairs NGr G.toList A.toList 0).length = 2 * NGr := by
      rw [pairs_length NGr _ _ 0 (by simp [hG, hA])]
      simp [hG]
    refine ⟨hG, hA, ?_, ?_, ?_⟩
    · rw [← Array.length_toList, hl, List.length_append, hlen]
      rfl
    · intro g s a hs ha
      obtain ⟨h1, h2⟩ := pairs_at NGr G.toList A.toList 0 g s a (by simpa using hs)
        (by simpa using ha)
      rw [Nat.zero_add] at h1 h2
      have hg : g < NGr := by
        rw [← hG]
        exact (Array.getElem?_eq_some_iff.1 hs).1
      rw [← Array.getElem?_toList, ← Array.getElem?_toList, hl,
        List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
      exact ⟨h1, h2⟩
    · rw [← Array.getElem?_toList, hl, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
      rfl

theorem listLinksH_without (NGr : Nat) (G A : Array SubPlanH) (H : SubPlanH) (Z : Array LinkH)
    (h : listLinksH NGr false G A H = .ok Z) :
    G.size = NGr ∧ Z.size = NGr + 1 ∧ (∀ g s, G[g]? = some s → Z[g]? = some (linkG s g)) ∧
      Z[NGr]? = some (linkHd NGr H) := by
  rw [listLinksH_fold] at h
  by_cases hc : (G.size != NGr || (false && A.size != NGr)) = true
  · rw [if_pos hc] at h
    cases h
  · rw [if_neg hc] at h
    have hZ := (Except.ok.inj h).symm
    have hc : G.size = NGr := Decidable.byContradiction fun e => hc (by simp [e])
    have hl : Z.toList = (G.toList.zipIdx.map fun x => linkG x.1 x.2) ++ [linkHd NGr H] := by
      rw [hZ, Array.toList_push, fold_without NGr A G.toList 0 #[]]
      simp
    have hlen : (G.toList.zipIdx.map fun x => linkG x.1 x.2).length = NGr := by simp [hc]
    refine ⟨hc, ?_, ?_, ?_⟩
    · rw [← Array.length_toList, hl, List.length_append, hlen]
      rfl
    · intro g s hs
      have hg : g < NGr := by
        rw [← hc]
        exact (Array.getElem?_eq_some_iff.1 hs).1
      rw [← Array.getElem?_toList, hl, List.getElem?_append_left (by omega), List.getElem?_map,
        List.getElem?_zipIdx, Array.getElem?_toList, hs]
      simp
    · rw [← Array.getElem?_toList, hl, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
      rfl

/-! ## The request's own list -/

section Request
open OnBytes.Model.Verify
variable {X : Public} {cov : Head.Covered} {ls : Array LinkH}

theorem linksOf_size (h : linksOf X cov = .ok ls) :
    X.G.size = X.NGr ∧ ls.size = (if X.p4 then 2 * X.NGr else X.NGr) + 1 := by
  unfold linksOf at h
  cases hp : X.p4 with
  | true =>
    rw [hp] at h
    obtain ⟨a1, _, a3, _, _⟩ := listLinksH_with _ _ _ _ _ h
    exact ⟨by simpa using a1, a3⟩
  | false =>
    rw [hp] at h
    obtain ⟨a1, a2, _, _⟩ := listLinksH_without _ _ _ _ _ h
    exact ⟨by simpa using a1, a2⟩

/-- The layers of group g. In a proof that covers attention, X.A has a plan for g too. -/
theorem linksOf_layers (h : linksOf X cov = .ok ls) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) :
    ls[layersLink X.p4 g]? = some (linkG (layersPlanOf X cov.tokv g hp) g) := by
  unfold linksOf at h
  have hG : (X.G.mapIdx fun g hp => layersPlanOf X cov.tokv g hp)[g]? =
      some (layersPlanOf X cov.tokv g hp) := by
    rw [Array.getElem?_mapIdx, hg]
    rfl
  unfold layersLink
  cases hq : X.p4 with
  | true =>
    rw [hq] at h
    obtain ⟨a1, a2, _, a4, _⟩ := listLinksH_with _ _ _ _ _ h
    have hlt : g < (X.A.map attentionPlanOf).size := by
      rw [a2, ← a1]
      exact (Array.getElem?_eq_some_iff.1 hG).1
    exact (a4 g _ _ hG (Array.getElem?_eq_getElem hlt)).1
  | false =>
    rw [hq] at h
    obtain ⟨_, _, a3, _⟩ := listLinksH_without _ _ _ _ _ h
    exact a3 g _ hG

/-- The attention of group g. -/
theorem linksOf_attention (h : linksOf X cov = .ok ls) (hq : X.p4 = true) (g : Nat)
    (A : Attention.Plan) (hg : X.A[g]? = some A) :
    ls[2 * g + 1]? = some (linkA X.NGr (attentionPlanOf A) g) := by
  unfold linksOf at h
  rw [hq] at h
  obtain ⟨a1, a2, _, a4, _⟩ := listLinksH_with _ _ _ _ _ h
  have hA : (X.A.map attentionPlanOf)[g]? = some (attentionPlanOf A) := by
    rw [Array.getElem?_map, hg]
    rfl
  have hlt : g < (X.G.mapIdx fun g hp => layersPlanOf X cov.tokv g hp).size := by
    rw [a1, ← a2]
    exact (Array.getElem?_eq_some_iff.1 hA).1
  exact (a4 g _ _ (Array.getElem?_eq_getElem hlt) hA).2

/-- The head: the last link. -/
theorem linksOf_head (h : linksOf X cov = .ok ls) :
    ls[if X.p4 then 2 * X.NGr else X.NGr]? = some (linkHd X.NGr (headPlanOf X cov)) := by
  unfold linksOf at h
  cases hq : X.p4 with
  | true =>
    rw [hq] at h
    exact (listLinksH_with _ _ _ _ _ h).2.2.2.2
  | false =>
    rw [hq] at h
    exact (listLinksH_without _ _ _ _ _ h).2.2.2

end Request

end OnBytes.L5.LinksOrder

#print axioms OnBytes.L5.LinksOrder.listLinksH_fold
#print axioms OnBytes.L5.LinksOrder.listLinksH_with
#print axioms OnBytes.L5.LinksOrder.listLinksH_without
#print axioms OnBytes.L5.LinksOrder.linksOf_size
#print axioms OnBytes.L5.LinksOrder.linksOf_layers
#print axioms OnBytes.L5.LinksOrder.linksOf_attention
#print axioms OnBytes.L5.LinksOrder.linksOf_head
