-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoBare.lean.
The records of the links that were built before agree, place by place, with the links of the
request, but for the routine and the names of the arrays.

The verifier runs `C.built.links.zipWith (fun b l => { b with run := l.run }) links`, with links
from `Verify.linksOf C.X cov`. The built records come from `Verify.linksOf C.X default`, through
`declareLinks`.

 * `bare Y`: the link's record Y without its routine and without the names of its arrays.
 * `loop_pre`: a loop over a list, in the type of the functions that may refuse under a name, whose
   passes all go on: what holds of the passed part of the list and the state is carried to the whole
   list. `loop_fold`: a loop none of whose passes refuses or ends the loop is a fold.
 * `declareLinks_bare`: `declareLinks` returns the links that it was given, in their order, each
   with the names of its arrays filled in.
 * `listLinksH_eq`: what `listLinksH` returns, written as a fold. `listLinksH_bare`: it depends on
   the plans' routines in the links' routines alone.
 * `linksOf_bare`: the links of two requests under one public record agree but for their routines.
 * `built_bare`: if `builtOf X chains` returns B and `Verify.linksOf X cov` returns links, then B's
   links and links agree place by place but for routine and names: `B.links.toList.map bare =
   links.toList.map bare` (`SameBare`). So they are equally many (`SameBare.size`), and kind, group,
   planned state and list of arrays agree at each place (`SameBare.at`, `bare_fields`).
 * `linksOf_last`: the last link of `Verify.linksOf X cov` is the head's, made of
   `headPlanOf X cov`.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoBuilt

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages

/-- A link's record without its routine and without the names of its arrays. -/
def bare (Y : LinkH) : LinkH := { Y with run := pure none, arrayOf := #[] }

/-- A plan's record without its routine. -/
def barePlan (s : SubPlanH) : SubPlanH := { s with run := pure none }

theorem loop_pre {ε β σ : Type} (Inv : List β → σ → Prop)
    (f : β → σ → Except ε (ForInStep σ))
    (hf : ∀ a t r pre, Inv pre t → f a t = .ok r → ∃ t', r = .yield t' ∧ Inv (pre ++ [a]) t') :
    ∀ (l pre : List β) (s s' : σ), Inv pre s → forIn l s f = .ok s' → Inv (pre ++ l) s'
  | [], pre, s, s', hs, h => by
    rw [List.forIn_nil] at h
    cases h
    rw [List.append_nil]
    exact hs
  | a :: l, pre, s, s', hs, h => by
    rw [List.forIn_cons] at h
    obtain ⟨r, e, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨t', rfl, ht⟩ := hf a s r pre hs e
    have := loop_pre Inv f hf l (pre ++ [a]) t' s' ht h
    rwa [List.append_assoc, List.singleton_append] at this

theorem loop_fold {ε β σ : Type} (f : β → σ → Except ε (ForInStep σ)) (g : σ → β → σ)
    (hf : ∀ a t, f a t = .ok (.yield (g t a))) :
    ∀ (l : List β) (s : σ), forIn l s f = (.ok (l.foldl g s) : Except ε σ)
  | [], s => by
    rw [List.forIn_nil]
    rfl
  | a :: l, s => by
    rw [List.forIn_cons, hf a s]
    exact loop_fold f g hf l (g s a)

theorem map_fst_zipIdx {α β : Type} (g : α → β) :
    ∀ (l : List α) (k : Nat), (l.zipIdx k).map (fun x => g x.1) = l.map g
  | [], _ => rfl
  | a :: l, k => by
    rw [List.zipIdx_cons, List.map_cons, List.map_cons, map_fst_zipIdx g l (k + 1)]

theorem declareLinks_bare (links named : Array LinkH) (declared : Array FrameLink) (NGr : Nat)
    (p4 : Bool) (h : declareLinks links NGr p4 = .ok (named, declared)) :
    named.toList.map bare = links.toList.map bare := by
  unfold declareLinks at h
  dsimp only at h
  obtain ⟨⟨d, n⟩, hr, h⟩ := (excBind_ok _ _ _).1 h
  cases h
  have key := loop_pre
    (fun (pre : List (LinkH × Nat)) (st : MProd (Array FrameLink) (Array LinkH)) =>
      st.snd.toList.map bare = pre.map fun x => bare x.1) _ ?_ _ [] _ _ (by simp) hr
  · rw [List.nil_append] at key
    rw [key]
    exact map_fst_zipIdx bare _ 0
  · rintro ⟨X, l⟩ ⟨dd, nn⟩ r pre hI hq
    dsimp only at hq hI
    obtain ⟨_, _, hq⟩ := (excBind_ok _ _ _).1 hq
    obtain ⟨_, _, hq⟩ := (excBind_ok _ _ _).1 hq
    split at hq
    · obtain ⟨_, e, _⟩ := (excBind_ok _ _ _).1 hq
      cases e
    · cases hq
      refine ⟨_, rfl, ?_⟩
      simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil, hI]
      rfl

/-! ### the order of the links, as a fold -/

/-- One pass of the loop of `listLinksH`. -/
def linksStep (NGr : Nat) (p4 : Bool) (A : Array SubPlanH) (acc : Array LinkH)
    (x : SubPlanH × Nat) : Array LinkH :=
  if p4 = true then
    match A[x.2]? with
    | some a =>
      (acc.push (x.1.link ("G" ++ toString x.2) (1 + x.2) 0 x.2 true)).push
        (a.link ("A" ++ toString x.2) (2 + NGr + x.2) 1 x.2 false)
    | none => acc.push (x.1.link ("G" ++ toString x.2) (1 + x.2) 0 x.2 true)
  else acc.push (x.1.link ("G" ++ toString x.2) (1 + x.2) 0 x.2 true)

theorem listLinksH_eq (NGr : Nat) (p4 : Bool) (G A : Array SubPlanH) (H : SubPlanH)
    (links : Array LinkH) (h : listLinksH NGr p4 G A H = .ok links) :
    links = (G.toList.zipIdx.foldl (linksStep NGr p4 A) #[]).push
      (H.link "H" (1 + NGr) 2 0 true) := by
  unfold listLinksH at h
  dsimp only at h
  split at h
  · exact absurd h (by intro x; cases x)
  · obtain ⟨_, _, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨r, hr, h⟩ := (excBind_ok _ _ _).1 h
    cases h
    rw [loop_fold _ (linksStep NGr p4 A)] at hr
    · cases hr
      rfl
    · rintro ⟨s, g⟩ t
      unfold linksStep
      dsimp only
      split
      · cases A[g]? with
        | none => rfl
        | some a => rfl
      · rfl

/-- Two arrays of links agree but for routines and names. -/
def SameBare (a b : Array LinkH) : Prop := a.toList.map bare = b.toList.map bare

theorem SameBare.push {a b : Array LinkH} {x y : LinkH} (h : SameBare a b) (e : bare x = bare y) :
    SameBare (a.push x) (b.push y) := by
  unfold SameBare at *
  rw [Array.toList_push, Array.toList_push, List.map_append, List.map_append, h]
  simp only [List.map_cons, List.map_nil, e]

theorem bare_link (s s' : SubPlanH) (e : barePlan s = barePlan s') (name : String)
    (gid kind g : Nat) (fv : Bool) :
    bare (s.link name gid kind g fv) = bare (s'.link name gid kind g fv) := by
  have k : ∀ t : SubPlanH, bare (t.link name gid kind g fv) =
      bare ((barePlan t).link name gid kind g fv) := fun _ => rfl
  rw [k s, k s', e]

theorem fold_bare (NGr : Nat) (p4 : Bool) (A : Array SubPlanH) :
    ∀ (l l' : List SubPlanH) (k : Nat) (acc acc' : Array LinkH),
      l.map barePlan = l'.map barePlan → SameBare acc acc' →
      SameBare ((l.zipIdx k).foldl (linksStep NGr p4 A) acc)
        ((l'.zipIdx k).foldl (linksStep NGr p4 A) acc')
  | [], [], _, _, _, _, h => h
  | [], _ :: _, _, _, _, e, _ => by cases e
  | _ :: _, [], _, _, _, e, _ => by cases e
  | s :: l, s' :: l', k, acc, acc', e, h => by
    rw [List.map_cons, List.map_cons] at e
    obtain ⟨e1, e2⟩ := List.cons.inj e
    rw [List.zipIdx_cons, List.zipIdx_cons, List.foldl_cons, List.foldl_cons]
    refine fold_bare NGr p4 A l l' (k + 1) _ _ e2 ?_
    unfold linksStep
    dsimp only
    split
    · split
      · exact (h.push (bare_link s s' e1 _ _ _ _ _)).push rfl
      · exact h.push (bare_link s s' e1 _ _ _ _ _)
    · exact h.push (bare_link s s' e1 _ _ _ _ _)

theorem listLinksH_bare (NGr : Nat) (p4 : Bool) (G G' A : Array SubPlanH) (H H' : SubPlanH)
    (links links' : Array LinkH) (hG : G.toList.map barePlan = G'.toList.map barePlan)
    (hH : barePlan H = barePlan H') (h : listLinksH NGr p4 G A H = .ok links)
    (h' : listLinksH NGr p4 G' A H' = .ok links') : SameBare links links' := by
  rw [listLinksH_eq _ _ _ _ _ _ h, listLinksH_eq _ _ _ _ _ _ h']
  exact (fold_bare NGr p4 A _ _ 0 _ _ hG rfl).push (bare_link H H' hH _ _ _ _ _)

theorem barePlan_layers (X : Public) (t t' : Array Nat) (g : Nat) (hp : Layer.HPlan2) :
    barePlan (layersPlanOf X t g hp) = barePlan (layersPlanOf X t' g hp) := by
  unfold barePlan layersPlanOf
  dsimp only

theorem barePlan_head (X : Public) (cov cov' : Head.Covered) :
    barePlan (headPlanOf X cov) = barePlan (headPlanOf X cov') := by
  unfold barePlan headPlanOf
  dsimp only

theorem linksOf_bare (X : Public) (cov cov' : Head.Covered) (links links' : Array LinkH)
    (h : linksOf X cov = .ok links) (h' : linksOf X cov' = .ok links') :
    SameBare links links' := by
  unfold linksOf at h h'
  refine listLinksH_bare _ _ _ _ _ (headPlanOf X cov) (headPlanOf X cov') _ _ ?_
    (barePlan_head X cov cov') h h'
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, Array.getElem_toList, Array.getElem_mapIdx]
    exact barePlan_layers X _ _ _ _

theorem built_bare {X : Public} {chains : Chains} {B : LinksH} {cov : Head.Covered}
    {links : Array LinkH} (hB : builtOf X chains = .ok B) (hl : linksOf X cov = .ok links) :
    SameBare B.links links := by
  obtain ⟨l0, declared, h0, h1⟩ := builtOf_links hB
  exact (declareLinks_bare _ _ _ _ _ h1).trans (linksOf_bare X default cov l0 links h0 hl)

theorem SameBare.size {a b : Array LinkH} (h : SameBare a b) : a.size = b.size := by
  have := congrArg List.length h
  simpa using this

theorem SameBare.at {a b : Array LinkH} (h : SameBare a b) (i : Nat) (ha : i < a.size)
    (hb : i < b.size) : bare (a[i]) = bare (b[i]) := by
  have e : (a.toList.map bare)[i]? = (b.toList.map bare)[i]? := by rw [h]
  simpa [ha, hb] using e

/-- Kind, group, planned state and list of arrays agree. -/
theorem bare_fields {x y : LinkH} (e : bare x = bare y) :
    x.kind = y.kind ∧ x.g = y.g ∧ x.Fp = y.Fp ∧ x.Tp = y.Tp := by
  have e1 := congrArg LinkH.kind e
  have e2 := congrArg LinkH.g e
  have e3 := congrArg LinkH.Fp e
  have e4 := congrArg LinkH.Tp e
  exact ⟨e1, e2, e3, e4⟩

/-- The last link is the head's. -/
theorem linksOf_last (X : Public) (cov : Head.Covered) (links : Array LinkH)
    (h : linksOf X cov = .ok links) :
    ∃ hs : links.size - 1 < links.size,
      links[links.size - 1] = (headPlanOf X cov).link "H" (1 + X.NGr) 2 0 true := by
  unfold linksOf at h
  rw [listLinksH_eq _ _ _ _ _ _ h]
  refine ⟨by simp, ?_⟩
  simp only [Array.size_push, Nat.add_sub_cancel, Array.getElem_push_eq]

end Fo
