-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/LinksBuilt.lean: the links as built, and the list that the stage request runs,
place by place.

The stage request (OnBytes/Model/VerifyStages.lean, requestRun) runs the links as built, each with
the routine of the link at the same place of the request's own list. The links as built (builtOf)
are the links of Verify.linksOf without a request, as buildLinksH returns them: declareLinks has
filled the field arrayOf and left the other fields. This file says so, and with
OnBytes/Tie/Pv/Keeps/LinksOrder.lean it says which link, with all its fields but arrayOf, stands at
which place of the list that is run.

Main names:
  `Chain`, `forIn_chain`: a loop without a break that succeeds, as a chain of its steps.
  `declareLinks_at`: where declareLinks succeeds: as many links as it was given; the link at each
    place is the given link at that place with arrayOf filled.
  `builtOf_at`: where builtOf succeeds: Verify.linksOf without a request has succeeded, and the
    links as built are its links, place by place, with arrayOf filled.
  `zipped`: the list that the stage request runs.
  `zipped_size`, `zipped_layers`, `zipped_attention`, `zipped_head`: it has as many links as the
    request's own list; at the place `layersLink` p4 g stands the link of the layers of group g made
    from the request's plan, at 2 g + 1 that of the attention of group g, at the last place the
    head's, each with some arrayOf.

Limits: what arrayOf holds is not said. The other tests of buildLinksH are not used.
-/
import OnBytes.Tie.Pv.Keeps.LinksOrder
import OnBytes.Model.VerifyStages

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.L5.LinksOrder
open OnBytes OnBytes.Model OnBytes.Model.Stages

theorem ok_bind {α β : Type} {x : Except String α} {f : α → Except String β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- A chain of steps along a list. -/
def Chain {α β : Type} (R : α → β → β → Prop) : List α → β → β → Prop
  | [], b, r => r = b
  | a :: l, b, r => ∃ b', R a b b' ∧ Chain R l b' r

theorem forIn_chain {α β : Type} (body : α → β → Except String (ForInStep β))
    (R : α → β → β → Prop) (hb : ∀ a b s, body a b = .ok s → ∃ b', s = .yield b' ∧ R a b b') :
    ∀ (l : List α) (b r : β), forIn l b body = .ok r → Chain R l b r
  | [], b, r, h => (Except.ok.inj h).symm
  | a :: l, b, r, h => by
    rw [List.forIn_cons] at h
    obtain ⟨s, h1, h2⟩ := ok_bind h
    obtain ⟨b', rfl, hR⟩ := hb a b s h1
    exact ⟨b', hR, forIn_chain body R hb l b' r h2⟩

/-- One step of declareLinks: a link is added that is the given one with arrayOf filled. -/
def StepD (x : LinkH × Nat) (b b' : MProd (Array FrameLink) (Array LinkH)) : Prop :=
  ∃ ar, b'.snd = b.snd.push { x.1 with arrayOf := ar }

theorem chain_at : ∀ (l : List (LinkH × Nat)) (b r : MProd (Array FrameLink) (Array LinkH)),
    Chain StepD l b r →
    r.snd.size = b.snd.size + l.length ∧
      (∀ j, j < b.snd.size → r.snd[j]? = b.snd[j]?) ∧
      ∀ j x, l[j]? = some x → ∃ ar, r.snd[b.snd.size + j]? = some { x.1 with arrayOf := ar }
  | [], b, r, h => by
    have e : r = b := h
    rw [e]
    exact ⟨rfl, fun _ _ => rfl, fun j x hx => by simp at hx⟩
  | a :: l, b, r, h => by
    obtain ⟨b', ⟨ar, hb'⟩, hc⟩ := h
    obtain ⟨i1, i2, i3⟩ := chain_at l b' r hc
    have hs : b'.snd.size = b.snd.size + 1 := by rw [hb', Array.size_push]
    refine ⟨?_, ?_, ?_⟩
    · rw [i1, hs, List.length_cons]
      omega
    · intro j hj
      rw [i2 j (by omega), hb', Array.getElem?_push_lt hj, Array.getElem?_eq_getElem hj]
    · intro j x hx
      cases j with
      | zero =>
        have e : a = x := by simpa using hx
        refine ⟨ar, ?_⟩
        rw [Nat.add_zero, i2 _ (by omega), hb', Array.getElem?_push_size, e]
      | succ j =>
        obtain ⟨ar', h3⟩ := i3 j x (by simpa using hx)
        refine ⟨ar', ?_⟩
        rw [← h3, hs]
        congr 1
        omega

theorem declareLinks_at (links : Array LinkH) (NGr : Nat) (p4 : Bool) (named : Array LinkH)
    (declared : Array FrameLink) (h : declareLinks links NGr p4 = .ok (named, declared)) :
    named.size = links.size ∧
      ∀ (j : Nat) (Y : LinkH), links[j]? = some Y →
        ∃ ar, named[j]? = some { Y with arrayOf := ar } := by
  unfold declareLinks at h
  obtain ⟨r, h1, h2⟩ := ok_bind h
  have hn : named = r.snd := by
    obtain ⟨d, n⟩ := r
    exact (congrArg Prod.fst (Except.ok.inj h2)).symm
  have hc := forIn_chain _ StepD (fun x b s hs => by
    obtain ⟨X, l⟩ := x
    obtain ⟨d, _, k1⟩ := ok_bind hs
    obtain ⟨s1, _, k2⟩ := ok_bind k1
    dsimp only at k2
    split at k2
    · cases k2
    · exact ⟨_, (Except.ok.inj k2).symm, s1.fst, rfl⟩) _ _ _ h1
  obtain ⟨i1, _, i3⟩ := chain_at _ _ _ hc
  subst hn
  refine ⟨by simpa using i1, fun j Y hY => ?_⟩
  obtain ⟨ar, h3⟩ := i3 j (Y, j) (by
    rw [List.getElem?_zipIdx, Array.getElem?_toList, hY]
    simp)
  exact ⟨ar, by simpa using h3⟩

section Request
open OnBytes.Model.Verify
variable {X : Public} {chains : Chains} {B : LinksH}

theorem builtOf_at (h : builtOf X chains = .ok B) :
    ∃ ls0, linksOf X default = .ok ls0 ∧ B.links.size = ls0.size ∧
      ∀ (j : Nat) (Y : LinkH), ls0[j]? = some Y →
        ∃ ar, B.links[j]? = some { Y with arrayOf := ar } := by
  unfold builtOf at h
  obtain ⟨ls0, h0, h1⟩ := ok_bind h
  unfold buildLinksH at h1
  obtain ⟨_, _, h2⟩ := ok_bind h1
  obtain ⟨_, _, h3⟩ := ok_bind h2
  obtain ⟨⟨named, declared⟩, hd, h4⟩ := ok_bind h3
  obtain ⟨a1, a2⟩ := declareLinks_at ls0 X.NGr X.p4 named declared hd
  have hB : B.links = named := by
    dsimp only at h4
    obtain ⟨_, _, h5⟩ := ok_bind h4
    obtain ⟨_, _, h6⟩ := ok_bind h5
    obtain ⟨_, _, h7⟩ := ok_bind h6
    obtain ⟨_, _, h8⟩ := ok_bind h7
    split at h8
    · cases h8
    · obtain ⟨_, _, h9⟩ := ok_bind h8
      obtain ⟨_, _, h10⟩ := ok_bind h9
      obtain ⟨_, _, h11⟩ := ok_bind h10
      obtain ⟨_, _, h12⟩ := ok_bind h11
      rw [← Except.ok.inj h12]
  rw [hB]
  exact ⟨ls0, h0, a1, a2⟩

/-- The list that the stage request runs. -/
def zipped (B : LinksH) (ls : Array LinkH) : Array LinkH :=
  B.links.zipWith (fun b l => { b with run := l.run }) ls

variable {cov : Head.Covered} {ls : Array LinkH}

theorem zipped_at (hB : builtOf X chains = .ok B) (j : Nat) (Y0 Y : LinkH)
    (ls0 : Array LinkH) (h0 : linksOf X default = .ok ls0) (hj0 : ls0[j]? = some Y0)
    (hj : ls[j]? = some Y) :
    ∃ ar, (zipped B ls)[j]? = some { Y0 with arrayOf := ar, run := Y.run } := by
  obtain ⟨ls0', h0', _, a2⟩ := builtOf_at hB
  have e : ls0' = ls0 := Except.ok.inj (h0'.symm.trans h0)
  rw [e] at a2
  obtain ⟨ar, h1⟩ := a2 j Y0 hj0
  refine ⟨ar, ?_⟩
  unfold zipped
  rw [Array.getElem?_zipWith, h1, hj]

theorem zipped_size (hB : builtOf X chains = .ok B) (h : linksOf X cov = .ok ls) :
    (zipped B ls).size = (if X.p4 then 2 * X.NGr else X.NGr) + 1 := by
  obtain ⟨ls0, h0, a1, _⟩ := builtOf_at hB
  unfold zipped
  rw [Array.size_zipWith, a1, (linksOf_size h0).2, (linksOf_size h).2, Nat.min_self]

/-- The layers of group g, in the list that is run. -/
theorem zipped_layers (hB : builtOf X chains = .ok B) (h : linksOf X cov = .ok ls) (g : Nat)
    (hp : Layer.HPlan2) (hg : X.G[g]? = some hp) :
    ∃ ar, (zipped B ls)[layersLink X.p4 g]? =
      some { linkG (layersPlanOf X cov.tokv g hp) g with arrayOf := ar } := by
  obtain ⟨ls0, h0, _, _⟩ := builtOf_at hB
  obtain ⟨ar, h1⟩ :=
    zipped_at hB _ _ _ ls0 h0 (linksOf_layers h0 g hp hg) (linksOf_layers h g hp hg)
  refine ⟨ar, ?_⟩
  rw [h1]
  simp only [linkG, SubPlanH.link, layersPlanOf]

/-- The attention of group g. -/
theorem zipped_attention (hB : builtOf X chains = .ok B) (h : linksOf X cov = .ok ls)
    (hq : X.p4 = true) (g : Nat) (A : Attention.Plan) (hg : X.A[g]? = some A) :
    ∃ ar, (zipped B ls)[2 * g + 1]? =
      some { linkA X.NGr (attentionPlanOf A) g with arrayOf := ar } := by
  obtain ⟨ls0, h0, _, _⟩ := builtOf_at hB
  exact zipped_at hB _ _ _ ls0 h0 (linksOf_attention h0 hq g A hg) (linksOf_attention h hq g A hg)

/-- The head: the last link. -/
theorem zipped_head (hB : builtOf X chains = .ok B) (h : linksOf X cov = .ok ls) :
    ∃ ar, (zipped B ls)[if X.p4 then 2 * X.NGr else X.NGr]? =
      some { linkHd X.NGr (headPlanOf X cov) with arrayOf := ar } := by
  obtain ⟨ls0, h0, _, _⟩ := builtOf_at hB
  obtain ⟨ar, h1⟩ := zipped_at hB _ _ _ ls0 h0 (linksOf_head h0) (linksOf_head h)
  refine ⟨ar, ?_⟩
  rw [h1]
  simp only [linkHd, SubPlanH.link, headPlanOf]

end Request

end OnBytes.L5.LinksOrder

#print axioms OnBytes.L5.LinksOrder.declareLinks_at
#print axioms OnBytes.L5.LinksOrder.builtOf_at
#print axioms OnBytes.L5.LinksOrder.zipped_size
#print axioms OnBytes.L5.LinksOrder.zipped_layers
#print axioms OnBytes.L5.LinksOrder.zipped_attention
#print axioms OnBytes.L5.LinksOrder.zipped_head
