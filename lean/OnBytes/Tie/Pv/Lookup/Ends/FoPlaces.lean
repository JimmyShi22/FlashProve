-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPlaces.lean.
Where the link of a group of layers, of its attention and of the output head stands, and its run
with the chain before it and behind it.

`LinksRan.cut` (OnBytes/Tie/Pv/Lookup/Ends/FoLinksCut.lean) takes the link at a place out of the
chain and keeps the chain.
`KindAt` (OnBytes/Tie/Pv/Lookup/Ends/FoLinksKindAt.lean) says which sub-proof a link holds.
`built_bare` (OnBytes/Tie/Pv/Lookup/Ends/FoBare.lean) says
that the records built before agree with the links of the request but for routine and names. Here
the three are joined.

 * `mem_zipIdx_of`, `fold_mono`, `fold_memG`, `fold_memA`: what the fold of `listLinksH_eq` holds.
 * `layer_place`, `att_place`: the link of the layers of group g, made of the plan `X.G[g]`, stands
   at some place of `Verify.linksOf X cov`; so does the link of the attention of group g, made of
   `X.A[g]`, if the proof covers attention and there is a group g. (`linksOf_last`,
     OnBytes/Tie/Pv/Lookup/Ends/FoBare.lean: the
   head's link stands at the last place.)
 * `CutAt`: the facts of `LinksRan.cut` at place i of the links as the verifier runs them, with the
   link's routine named by `RanAt` (OnBytes/Tie/Pv/Lookup/Ends/FoLinksEach.lean) and the planned
     state and the list of arrays
   taken from the link of `Verify.linksOf` at that place.
 * `cut_at`: `CutAt` holds at every place, if `LinksRan` holds of these links from number 0, the
   links are those of `Verify.linksOf X cov`, and the records built before agree with them
   (`SameBare`).
 * `ranAt_layer`, `ranAt_att`, `ranAt_head`: of the link of a group's layers, of its attention, of
   the head, `RanAt` is the run of that routine: at the plan hp and the group g; at the plan a; at
   X's own records.

Not said: the number of the place at which a group's link stands.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLinksCut
import OnBytes.Tie.Pv.Lookup.Ends.FoLinksEach
import OnBytes.Tie.Pv.Lookup.Ends.FoBare

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Model.Verify OnBytes.Model.Stages

theorem mem_zipIdx_of {α : Type} : ∀ (l : List α) (k i : Nat) (x : α), l[i]? = some x →
    (x, k + i) ∈ l.zipIdx k
  | [], _, _, _, h => by simp at h
  | a :: l, k, 0, x, h => by
    have e : a = x := by simpa using h
    rw [List.zipIdx_cons, e]
    exact List.mem_cons_self
  | a :: l, k, i + 1, x, h => by
    have e : l[i]? = some x := by simpa using h
    rw [List.zipIdx_cons, show k + (i + 1) = k + 1 + i by omega]
    exact List.mem_cons_of_mem _ (mem_zipIdx_of l (k + 1) i x e)

theorem step_mono (NGr : Nat) (p4 : Bool) (A : Array SubPlanH) (acc : Array LinkH)
    (x : SubPlanH × Nat) (Y : LinkH) (h : Y ∈ acc.toList) :
    Y ∈ (linksStep NGr p4 A acc x).toList := by
  unfold linksStep
  split
  · split <;> simp [h]
  · simp [h]

theorem fold_mono (NGr : Nat) (p4 : Bool) (A : Array SubPlanH) (Y : LinkH) :
    ∀ (l : List (SubPlanH × Nat)) (acc : Array LinkH), Y ∈ acc.toList →
      Y ∈ (l.foldl (linksStep NGr p4 A) acc).toList
  | [], _, h => h
  | x :: l, acc, h => fold_mono NGr p4 A Y l _ (step_mono NGr p4 A acc x Y h)

theorem fold_memG (NGr : Nat) (p4 : Bool) (A : Array SubPlanH) (s : SubPlanH) (g : Nat) :
    ∀ (l : List (SubPlanH × Nat)) (acc : Array LinkH), (s, g) ∈ l →
      s.link ("G" ++ toString g) (1 + g) 0 g true ∈ (l.foldl (linksStep NGr p4 A) acc).toList
  | [], _, h => by cases h
  | x :: l, acc, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · refine fold_mono NGr p4 A _ l _ ?_
      unfold linksStep
      split
      · split <;> simp
      · simp
    · exact fold_memG NGr p4 A s g l _ h'

theorem fold_memA (NGr : Nat) (A : Array SubPlanH) (s a : SubPlanH) (g : Nat)
    (ha : A[g]? = some a) :
    ∀ (l : List (SubPlanH × Nat)) (acc : Array LinkH), (s, g) ∈ l →
      a.link ("A" ++ toString g) (2 + NGr + g) 1 g false ∈
        (l.foldl (linksStep NGr true A) acc).toList
  | [], _, h => by cases h
  | x :: l, acc, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · refine fold_mono NGr true A _ l _ ?_
      unfold linksStep
      simp [ha]
    · exact fold_memA NGr A s a g ha l _ h'

theorem layer_place (X : Public) (cov : Head.Covered) (links : Array LinkH)
    (h : linksOf X cov = .ok links) (g : Nat) (hp : Layer.HPlan2) (hg : X.G[g]? = some hp) :
    ∃ (i : Nat) (hi : i < links.size),
      links[i] = (layersPlanOf X cov.tokv g hp).link ("G" ++ toString g) (1 + g) 0 g true := by
  unfold linksOf at h
  have e := listLinksH_eq _ _ _ _ _ _ h
  have m : (layersPlanOf X cov.tokv g hp).link ("G" ++ toString g) (1 + g) 0 g true ∈
      links.toList := by
    rw [e, Array.toList_push]
    refine List.mem_append_left _ (fold_memG _ _ _ _ g _ _ ?_)
    have := mem_zipIdx_of (X.G.mapIdx fun g hp => layersPlanOf X cov.tokv g hp).toList 0 g
      (layersPlanOf X cov.tokv g hp) (by simp [hg])
    simpa using this
  obtain ⟨i, hi, ei⟩ := List.mem_iff_getElem.1 m
  exact ⟨i, by simpa using hi, by simpa using ei⟩

theorem att_place (X : Public) (cov : Head.Covered) (links : Array LinkH)
    (h : linksOf X cov = .ok links) (h4 : X.p4 = true) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) (a : Attention.Plan) (ha : X.A[g]? = some a) :
    ∃ (i : Nat) (hi : i < links.size),
      links[i] = (attentionPlanOf a).link ("A" ++ toString g) (2 + X.NGr + g) 1 g false := by
  unfold linksOf at h
  have e := listLinksH_eq _ _ _ _ _ _ h
  rw [h4] at e
  have m : (attentionPlanOf a).link ("A" ++ toString g) (2 + X.NGr + g) 1 g false ∈
      links.toList := by
    rw [e, Array.toList_push]
    refine List.mem_append_left _
      (fold_memA _ _ (layersPlanOf X cov.tokv g hp) _ g (by simp [ha]) _ _ ?_)
    have := mem_zipIdx_of (X.G.mapIdx fun g hp => layersPlanOf X cov.tokv g hp).toList 0 g
      (layersPlanOf X cov.tokv g hp) (by simp [hg])
    simpa using this
  obtain ⟨i, hi, ei⟩ := List.mem_iff_getElem.1 m
  exact ⟨i, by simpa using hi, by simpa using ei⟩

/-! ### the run at a place, with the chain around it -/

/-- The links as the verifier runs them: the records that were built before, each with the routine
of the link at its place. -/
abbrev asRun (built links : Array LinkH) : Array LinkH :=
  built.zipWith (fun b l => { b with run := l.run }) links

/-- The facts of `LinksRan.cut` at place i of the links as the verifier runs them. -/
def CutAt (X : Public) (cov : Head.Covered) (links built : Array LinkH) (p : Params.First)
    (wsLay : WsLay) (check : ChainCheck) (c : Ctx) (r : (ChainCheck × Proof.LinksResult) × Ctx)
    (i : Nat) (hb : i < built.size) (hi : i < links.size) (q' : ChainCheck) (d1 d2 : Ctx)
    (D : LinkCtx) (F : Fork) : Prop :=
  ∃ (mid nxt : (ChainCheck × Proof.LinksResult) × Ctx) (hz : i < (asRun built links).size),
    LinksRan (asRun built links) p wsLay ((asRun built links).toList.take i) 0 check {} c mid ∧
    mid.1.1.first mid.2 = .ok (q', d1) ∧ Clean d1 ∧
    RanAt X cov (links[i]) (links[i]).Fp
      { check := q', link := i, arrayOf := (built[i]).arrayOf, list := (links[i]).Tp } d1 D F d2 ∧
    runLinkH (asRun built links) p wsLay i ((asRun built links)[i]) mid.1.1 mid.1.2 mid.2 =
      .ok nxt ∧
    LinksRan (asRun built links) p wsLay ((asRun built links).toList.drop (i + 1)) (i + 1)
      nxt.1.1 nxt.1.2 nxt.2 r

theorem cut_at (X : Public) (cov : Head.Covered) (links built : Array LinkH)
    (hl : linksOf X cov = .ok links) (sb : SameBare built links) (p : Params.First)
    (wsLay : WsLay) (check : ChainCheck) (c : Ctx) (r : (ChainCheck × Proof.LinksResult) × Ctx)
    (h : LinksRan (asRun built links) p wsLay (asRun built links).toList 0 check {} c r)
    (i : Nat) (hb : i < built.size) (hi : i < links.size) :
    ∃ (q' : ChainCheck) (d1 d2 : Ctx) (D : LinkCtx) (F : Fork),
      CutAt X cov links built p wsLay check c r i hb hi q' d1 d2 D F := by
  have hz : i < (asRun built links).size := by
    simp only [asRun, Array.size_zipWith]
    omega
  have hz' : i < (asRun built links).toList.length := by simpa using hz
  obtain ⟨mid, nxt, q', d1, d2, o, D, F, a0, a1, a2, a3, a4, a5⟩ :=
    LinksRan.cut _ _ _ _ _ _ _ _ _ h i hz'
  obtain ⟨_, _, f3, f4⟩ := bare_fields (sb.at i hb hi)
  simp only [Nat.zero_add] at a3 a4 a5
  simp only [Array.getElem_toList] at a3 a4
  have a3' : (links[i]).run
      { check := q', link := i, arrayOf := (built[i]).arrayOf, list := (links[i]).Tp }
      (links[i]).Fp d1 = .ok (((o, D), F), d2) := by
    simp only [asRun, Array.getElem_zipWith] at a3
    rw [f3, f4] at a3
    exact a3
  exact ⟨q', d1, d2, D, F, mid, nxt, hz, a0, a1, a2,
    ranAt_of X cov _ (linksOf_kindAt X cov links hl _ (Array.getElem_mem_toList hi))
      _ _ _ _ _ _ o a3', a4, a5⟩

theorem ranAt_layer (X : Public) (cov : Head.Covered) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) (name : String) (gid : Nat) (fv : Bool) (Fp : Fork) (L C : LinkCtx)
    (F : Fork) (c1 c2 : Ctx)
    (h : RanAt X cov ((layersPlanOf X cov.tokv g hp).link name gid 0 g fv) Fp L c1 C F c2) :
    ∃ w, Layer.runForkHidG2 { X.layers with tokv := cov.tokv } hp g L Fp c1 =
      .ok (((w, C), F), c2) := by
  rcases h with ⟨_, hp', w, e, hw⟩ | ⟨hk, _⟩ | ⟨hk, _⟩
  · have e' : X.G[g]? = some hp' := e
    rw [hg] at e'
    cases e'
    exact ⟨w, hw⟩
  · have e : (0 : Nat) = 1 := hk
    cases e
  · have e : (0 : Nat) = 2 := hk
    cases e

theorem ranAt_att (X : Public) (cov : Head.Covered) (g : Nat) (a : Attention.Plan)
    (ha : X.A[g]? = some a) (name : String) (gid : Nat) (fv : Bool) (Fp : Fork) (L C : LinkCtx)
    (F : Fork) (c1 c2 : Ctx)
    (h : RanAt X cov ((attentionPlanOf a).link name gid 1 g fv) Fp L c1 C F c2) :
    Attention.run a L Fp c1 = .ok ((((), C), F), c2) := by
  rcases h with ⟨hk, _⟩ | ⟨_, a', e, hw⟩ | ⟨hk, _⟩
  · have e : (1 : Nat) = 0 := hk
    cases e
  · have e' : X.A[g]? = some a' := e
    rw [ha] at e'
    cases e'
    exact hw
  · have e : (1 : Nat) = 2 := hk
    cases e

theorem ranAt_head (X : Public) (cov : Head.Covered) (name : String) (gid g : Nat) (fv : Bool)
    (Fp : Fork) (L C : LinkCtx) (F : Fork) (c1 c2 : Ctx)
    (h : RanAt X cov ((headPlanOf X cov).link name gid 2 g fv) Fp L c1 C F c2) :
    ∃ w, Head.runForkHidH2 X.hS X.HLy (borderOf X.y) X.H X.owner cov X.layers.wsLay L Fp c1 =
      .ok (((w, C), F), c2) := by
  rcases h with ⟨hk, _⟩ | ⟨hk, _⟩ | ⟨_, w, hw⟩
  · have e : (2 : Nat) = 0 := hk
    cases e
  · have e : (2 : Nat) = 1 := hk
    cases e
  · exact ⟨w, hw⟩

end Fo
