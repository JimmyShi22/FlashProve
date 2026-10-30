-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLinksKindAt.lean.
Which sub-proof each link of a request's chain holds, with the routine's arguments as the public
record has them.

`Kind` (OnBytes/Tie/Pv/Lookup/Ends/FoLinksKind.lean) says that a link's routine has one of three
forms and leaves the routine's
arguments open. Here they are named, in the letters of OnBytes/Model/VerifyLinks.lean.

 * `listLinksH_all`: what holds of each record that `listLinksH` makes (the link of group g from the
   g-th plan for layers; the link of group g from the g-th plan for attention; the head's link)
   holds of each link that it returns.
 * `KindAt X cov Y`: the link Y is of kind 0, and its routine is that of the layers of group `Y.g`,
   at the plan `X.G[Y.g]`, with the request's tokens in the public record; or of kind 1, and its
   routine is attention's at the plan `X.A[Y.g]`; or of kind 2, and its routine is the output head's
   at X's own records.
 * `linksOf_kindAt`: each link of `Verify.linksOf X cov` is so.
 * `built_kindAt`: each link as the verifier runs them (the records that were built before, each
   with the routine of the link at its place in `Verify.linksOf`) has the routine of a link of
   `Verify.linksOf` that is so; `built_run`: place by place.

Not said: at which place of the array a link of a given kind and group stands; that the record that
was built before has the same kind and group as the link whose routine it is given.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLinksKind

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem listLinksH_all (Q : Stages.LinkH → Prop) (NGr : Nat) (p4 : Bool)
    (G A : Array Stages.SubPlanH) (H : Stages.SubPlanH) (links : Array Stages.LinkH)
    (hG : ∀ (g : Nat) (s : Stages.SubPlanH), G[g]? = some s →
      Q (s.link ("G" ++ toString g) (1 + g) 0 g true))
    (hA : ∀ (g : Nat) (a : Stages.SubPlanH), A[g]? = some a →
      Q (a.link ("A" ++ toString g) (2 + NGr + g) 1 g false))
    (hH : Q (H.link "H" (1 + NGr) 2 0 true))
    (h : Stages.listLinksH NGr p4 G A H = .ok links) : ∀ X ∈ links.toList, Q X := by
  unfold Stages.listLinksH at h
  dsimp only at h
  split at h
  · exact absurd h (by intro x; cases x)
  · obtain ⟨_, _, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨r, hr, h⟩ := (excBind_ok _ _ _).1 h
    cases h
    have push : ∀ (ls : Array Stages.LinkH) (Y : Stages.LinkH),
        (∀ X ∈ ls.toList, Q X) → Q Y → ∀ X ∈ (ls.push Y).toList, Q X := by
      intro ls Y h1 h2 X hX
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hX
      rcases hX with hX | rfl
      · exact h1 X hX
      · exact h2
    have inv : ∀ X ∈ r.toList, Q X := by
      refine loop_inv (fun ls : Array Stages.LinkH => ∀ X ∈ ls.toList, Q X) _ _ _ _
        (by simp) ?_ hr
      rintro ⟨s, g⟩ hs t q ht hq
      have hs' : G[g]? = some s := by
        have := List.mem_zipIdx hs
        simp only [Nat.zero_le, Nat.zero_add, Nat.sub_zero, true_and] at this
        obtain ⟨hl, e⟩ := this
        rw [Array.getElem?_eq_getElem (by simpa using hl)]
        simpa using e.symm
      dsimp only at hq
      split at hq
      · split at hq
        · rename_i a ha
          cases hq
          exact push _ _ (push _ _ ht (hG g s hs')) (hA g a ha)
        · cases hq
          exact push _ _ ht (hG g s hs')
      · cases hq
        exact push _ _ ht (hG g s hs')
    exact push _ _ inv hH

/-- Which sub-proof a link holds. -/
def KindAt (X : Verify.Public) (cov : Head.Covered) (Y : Stages.LinkH) : Prop :=
  (Y.kind = 0 ∧ ∃ hp, X.G[Y.g]? = some hp ∧
    Y.run = some <$> Layer.runForkHidG2 { X.layers with tokv := cov.tokv } hp Y.g) ∨
  (Y.kind = 1 ∧ ∃ a, X.A[Y.g]? = some a ∧ Y.run = (Attention.run a >>= fun _ => pure none)) ∨
  (Y.kind = 2 ∧ Y.run = some <$> Head.runForkHidH2 X.hS X.HLy (Verify.borderOf X.y) X.H X.owner
    cov X.layers.wsLay)

theorem linksOf_kindAt (X : Verify.Public) (cov : Head.Covered) (links : Array Stages.LinkH)
    (h : Verify.linksOf X cov = .ok links) : ∀ Y ∈ links.toList, KindAt X cov Y := by
  unfold Verify.linksOf at h
  refine listLinksH_all (KindAt X cov) _ _ _ _ _ links ?_ ?_ ?_ h
  · intro g s hs
    rw [Array.getElem?_mapIdx] at hs
    obtain ⟨hp, e1, rfl⟩ := Option.map_eq_some_iff.1 hs
    exact Or.inl ⟨rfl, hp, e1, rfl⟩
  · intro g a ha
    rw [Array.getElem?_map] at ha
    obtain ⟨P, e1, rfl⟩ := Option.map_eq_some_iff.1 ha
    exact Or.inr (Or.inl ⟨rfl, P, e1, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- Place by place, a link as the verifier runs them has the routine of the link of
`Verify.linksOf` at that place. -/
theorem built_run (links built : Array Stages.LinkH) (i : Nat)
    (hi : i < (built.zipWith (fun (b l : Stages.LinkH) => { b with run := l.run }) links).size)
    (hl : i < links.size) :
    ((built.zipWith (fun (b l : Stages.LinkH) => { b with run := l.run }) links)[i]'hi).run =
      (links[i]'hl).run := by
  rw [Array.getElem_zipWith]

theorem built_kindAt (X : Verify.Public) (cov : Head.Covered) (links built : Array Stages.LinkH)
    (h : Verify.linksOf X cov = .ok links) :
    ∀ Y' ∈ (built.zipWith (fun b l => { b with run := l.run }) links).toList,
      ∃ Y ∈ links.toList, Y'.run = Y.run ∧ KindAt X cov Y := by
  intro Y' hY
  rw [Array.toList_zipWith] at hY
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hY
  rw [List.getElem_zipWith]
  have hi' : i < links.toList.length := by
    rw [List.length_zipWith] at hi
    omega
  exact ⟨links.toList[i], List.getElem_mem hi', rfl,
    linksOf_kindAt X cov links h _ (List.getElem_mem hi')⟩

end Fo
