-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/TieK/LinksAll.lean: all links that the program runs on a request, in their order, as a plain
function of the public part and of the request's covered positions.

"The program" is the Lean program verify-on-bytes. Its stage request runs a list of links that it
joins from two lists, member by member (requestRun in OnBytes/Model/VerifyStages.lean): the records
come from the links as built (builtOf), each link's routine from the links made for the request
(linksOf). Both lists come out of a loop (listLinksH in OnBytes/Model/StagesLinks.lean).
OnBytes/TieK/LinksEnd.lean describes the last link. This file describes all:
 - groupLinks, listedBefore, listed: what the loop returns, as a list without a loop: for each group
   of layers its link, directly followed by attention's link if the proof covers attention and
   attention's plans reach to that group; last the head's. listLinksH_listed: the loop returns that
   list. listLinksH_sizes: there are as many plans for layers as groups, and, if the proof covers
   attention, as many for attention: the program's first test. So attention's plans do reach;
 - beforeHead X cov, listedOf X cov: that list at the public part's own plans. linksOf_listed;
 - bare Z: the link Z with the field arrayOf emptied. joined_bare: the list that the program runs is
   listedOf X cov, member by member, in every field but arrayOf: name, identifier, kind, group,
   plan, planned state, list of arrays, numbers, and the routine;
 - joined_arrays: its fields arrayOf are those of the links as built, member by member.

What is not claimed. What the field arrayOf holds. That the functions return a value is a
hypothesis. It claims nothing on soundness. The program does not import this file.
-/
import OnBytes.TieK.LinksEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK

open OnBytes.Model.Stages (LinkH SubPlanH)

/-! ## Tools on lists -/

/-- Numbering the images of a numbered list anew gives the old numbers. -/
theorem zipIdx_map_zipIdx {α β : Type} (f : α × Nat → β) : ∀ (l : List α) (k : Nat),
    ((l.zipIdx k).map f).zipIdx k = (l.zipIdx k).map fun x => (f x, x.2)
  | [], _ => rfl
  | a :: l, k => by
    rw [List.zipIdx_cons, List.map_cons, List.zipIdx_cons, List.map_cons,
      zipIdx_map_zipIdx f l (k + 1)]

/-- Lists made of the images of a list's members. -/
theorem flatMap_of_map {α β γ : Type} (f : α → β) (g : β → List γ) : ∀ l : List α,
    (l.map f).flatMap g = l.flatMap fun a => g (f a)
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, flatMap_of_map f g l]

/-- Two families of lists with the same images, member by member. -/
theorem map_flatMap_congr {α β γ : Type} (s : β → γ) (f g : α → List β)
    (h : ∀ a, (f a).map s = (g a).map s) : ∀ l : List α,
    (l.flatMap f).map s = (l.flatMap g).map s
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, List.map_append, h a,
      map_flatMap_congr s f g h l]

/-! ## What the loop returns -/

/-- The links of group g: the layers' link, made of the plan s; directly behind it attention's, if
the proof covers attention (p4) and there is a plan for the group. -/
def groupLinks (NGr : Nat) (p4 : Bool) (A : Array SubPlanH) (s : SubPlanH) (g : Nat) :
    List LinkH :=
  s.link ("G" ++ toString g) (1 + g) 0 g true ::
    (if p4 = true then
      (A[g]?).toList.map fun a => a.link ("A" ++ toString g) (2 + NGr + g) 1 g false
    else [])

/-- All links before the head's. -/
def listedBefore (NGr : Nat) (p4 : Bool) (G A : Array SubPlanH) : List LinkH :=
  G.toList.zipIdx.flatMap fun x => groupLinks NGr p4 A x.1 x.2

/-- All links. -/
def listed (NGr : Nat) (p4 : Bool) (G A : Array SubPlanH) (H : SubPlanH) : List LinkH :=
  listedBefore NGr p4 G A ++ [H.link "H" (1 + NGr) 2 0 true]

/-- **The loop returns that list.** -/
theorem listLinksH_listed {NGr : Nat} {p4 : Bool} {G A : Array SubPlanH} {H : SubPlanH}
    {ls : Array LinkH} (h : Model.Stages.listLinksH NGr p4 G A H = .ok ls) :
    ls.toList = listed NGr p4 G A H := by
  unfold Model.Stages.listLinksH at h
  obtain ⟨-, h1⟩ := ok_of_jp h
  obtain ⟨pre, hr, h2⟩ := ok_of_bind h1
  have e : pre.push (H.link "H" (1 + NGr) 2 0 true) = ls := Except.ok.inj h2
  have K : pre.toList = G.toList.zipIdx.flatMap fun x => groupLinks NGr p4 A x.1 x.2 := by
    refine forIn_keeps _ G.toList.zipIdx
      (fun pr (s : Array LinkH) => s.toList = pr.flatMap fun x => groupLinks NGr p4 A x.1 x.2) ?_
      G.toList.zipIdx [] _ _ rfl rfl hr
    intro pr a rest _ s s' hI0 hs
    have hI : s.toList = pr.flatMap fun x => groupLinks NGr p4 A x.1 x.2 := hI0
    obtain ⟨sp, g⟩ := a
    have hfl : ((pr ++ [(sp, g)]).flatMap fun x => groupLinks NGr p4 A x.1 x.2) =
        (pr.flatMap fun x => groupLinks NGr p4 A x.1 x.2) ++ groupLinks NGr p4 A sp g := by
      rw [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    dsimp only at hs
    by_cases h4 : p4 = true
    · rw [if_pos h4] at hs
      cases hA : A[g]? with
      | some a2 =>
        rw [hA] at hs
        refine ⟨_, (Except.ok.inj hs).symm, ?_⟩
        show ((s.push _).push _).toList = _
        have hg : groupLinks NGr p4 A sp g = [sp.link ("G" ++ toString g) (1 + g) 0 g true,
            a2.link ("A" ++ toString g) (2 + NGr + g) 1 g false] := by
          unfold groupLinks
          rw [if_pos h4, hA]
          rfl
        rw [hfl, hg, Array.toList_push, Array.toList_push, hI, List.append_assoc]
        rfl
      | none =>
        rw [hA] at hs
        refine ⟨_, (Except.ok.inj hs).symm, ?_⟩
        show (s.push _).toList = _
        have hg : groupLinks NGr p4 A sp g = [sp.link ("G" ++ toString g) (1 + g) 0 g true] := by
          unfold groupLinks
          rw [if_pos h4, hA]
          rfl
        rw [hfl, hg, Array.toList_push, hI]
    · rw [if_neg h4] at hs
      refine ⟨_, (Except.ok.inj hs).symm, ?_⟩
      show (s.push _).toList = _
      have hg : groupLinks NGr p4 A sp g = [sp.link ("G" ++ toString g) (1 + g) 0 g true] := by
        unfold groupLinks
        rw [if_neg h4]
      rw [hfl, hg, Array.toList_push, hI]
  rw [← e, Array.toList_push, K]
  rfl

/-- **The program's first test on the plans**: as many plans for layers as groups; and as many for
attention, if the proof covers attention. -/
theorem listLinksH_sizes {NGr : Nat} {p4 : Bool} {G A : Array SubPlanH} {H : SubPlanH}
    {ls : Array LinkH} (h : Model.Stages.listLinksH NGr p4 G A H = .ok ls) :
    G.size = NGr ∧ (p4 = true → A.size = NGr) := by
  unfold Model.Stages.listLinksH at h
  obtain ⟨hc, -⟩ := ok_of_jp h
  constructor
  · by_cases e : G.size = NGr
    · exact e
    · exact absurd (by simp [e]) hc
  · intro h4
    by_cases e : A.size = NGr
    · exact e
    · exact absurd (by simp [h4, e]) hc

/-! ## At the public part's own plans -/

/-- All links before the head's, at the public part's own plans: for the group g with the plan hp
the layers' link of Model.Verify.layersPlanOf X cov.tokv g hp; attention's of attentionPlanOf. -/
def beforeHead (X : Model.Verify.Public) (cov : Model.Head.Covered) : List LinkH :=
  X.G.toList.zipIdx.flatMap fun x =>
    groupLinks X.NGr X.p4 (X.A.map Model.Verify.attentionPlanOf)
      (Model.Verify.layersPlanOf X cov.tokv x.2 x.1) x.2

/-- All links, at the public part's own plans. -/
def listedOf (X : Model.Verify.Public) (cov : Model.Head.Covered) : List LinkH :=
  beforeHead X cov ++ [(Model.Verify.headPlanOf X cov).link "H" (1 + X.NGr) 2 0 true]

/-- An array's images under a function of place and member, numbered. -/
theorem mapIdx_zipIdx {α β : Type} (f : Nat → α → β) (G : Array α) :
    (G.mapIdx f).toList.zipIdx = G.toList.zipIdx.map fun x => (f x.2 x.1, x.2) := by
  rw [Array.toList_mapIdx, List.mapIdx_eq_zipIdx_map]
  exact zipIdx_map_zipIdx (fun x => f x.2 x.1) G.toList 0

/-- **The links made for a request are that list.** -/
theorem linksOf_listed {X : Model.Verify.Public} {cov : Model.Head.Covered} {ls : Array LinkH}
    (h : Model.Verify.linksOf X cov = .ok ls) : ls.toList = listedOf X cov := by
  unfold Model.Verify.linksOf at h
  rw [listLinksH_listed h]
  unfold listed listedBefore listedOf beforeHead
  rw [mapIdx_zipIdx, flatMap_of_map]

/-- The public part holds a plan for layers for each group; and one for attention, if the proof
covers attention. -/
theorem linksOf_sizes {X : Model.Verify.Public} {cov : Model.Head.Covered} {ls : Array LinkH}
    (h : Model.Verify.linksOf X cov = .ok ls) :
    X.G.size = X.NGr ∧ (X.p4 = true → X.A.size = X.NGr) := by
  unfold Model.Verify.linksOf at h
  obtain ⟨h1, h2⟩ := listLinksH_sizes h
  rw [Array.size_mapIdx] at h1
  rw [Array.size_map] at h2
  exact ⟨h1, h2⟩

/-! ## The list that the program runs -/

/-- The link with the field arrayOf emptied. -/
def bare (Z : LinkH) : LinkH := { Z with arrayOf := #[] }

/-- The link with the field arrayOf emptied and a fixed routine in the place of its own. -/
def strip (Z : LinkH) : LinkH := { Z with arrayOf := #[], run := pure none }

theorem strip_of_bare {a b : LinkH} (h : bare a = bare b) : strip a = strip b :=
  congrArg (fun Z : LinkH => ({ Z with run := pure none } : LinkH)) h

/-- A record b and a link l: if b is a link l0 but for arrayOf, and l0 is l but for arrayOf and the
routine, then b with l's routine is l but for arrayOf. -/
theorem bare_joined {b l0 l : LinkH} (h1 : bare b = bare l0) (h2 : strip l0 = strip l) :
    bare { b with run := l.run } = bare l := by
  have e : strip b = strip l := (strip_of_bare h1).trans h2
  exact congrArg (fun Z : LinkH => ({ Z with run := l.run } : LinkH)) e

/-- The same for lists, member by member. -/
theorem zip_bare : ∀ (Bs L0 L : List LinkH), Bs.map bare = L0.map bare →
    L0.map strip = L.map strip →
    (List.zipWith (fun (b l : LinkH) => { b with run := l.run }) Bs L).map bare = L.map bare
  | [], [], [], _, _ => rfl
  | [], [], _ :: _, _, h2 => by cases h2
  | [], _ :: _, _, h1, _ => by cases h1
  | _ :: _, [], _, h1, _ => by cases h1
  | _ :: _, _ :: _, [], _, h2 => by cases h2
  | b :: Bs, l0 :: L0, l :: L, h1, h2 => by
    rw [List.map_cons, List.map_cons] at h1 h2
    obtain ⟨a1, a2⟩ := List.cons.inj h1
    obtain ⟨b1, b2⟩ := List.cons.inj h2
    rw [List.zipWith_cons_cons, List.map_cons, List.map_cons, zip_bare Bs L0 L a2 b2,
      bare_joined a1 b1]

/-- The fields arrayOf of the joined list are the first list's, if the lists are of one length. -/
theorem zip_arrays : ∀ (Bs L : List LinkH), Bs.length = L.length →
    (List.zipWith (fun (b l : LinkH) => { b with run := l.run }) Bs L).map (·.arrayOf) =
      Bs.map (·.arrayOf)
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | b :: Bs, l :: L, h => by
    rw [List.zipWith_cons_cons, List.map_cons, List.map_cons,
      zip_arrays Bs L (Nat.succ.inj h)]

/-- A link made of a plan, stripped: the plan's routine is gone. -/
theorem strip_link (s : SubPlanH) (name : String) (gid kind g : Nat) (fv : Bool) :
    strip (s.link name gid kind g fv) =
      { name := name, gid := gid, kind := kind, g := g, tl := s.tl, Fp := s.Fp, Tp := s.Tp,
        ns := s.ns, fv := fv, NCL := s.NCL, arrayOf := #[], run := pure none } := rfl

/-- Two plans that differ in the routine alone give the same link, stripped. -/
theorem strip_link_congr {s t : SubPlanH} (h1 : s.tl = t.tl) (h2 : s.Fp = t.Fp) (h3 : s.Tp = t.Tp)
    (h4 : s.ns = t.ns) (h5 : s.NCL = t.NCL) (name : String) (gid kind g : Nat) (fv : Bool) :
    strip (s.link name gid kind g fv) = strip (t.link name gid kind g fv) := by
  rw [strip_link, strip_link, h1, h2, h3, h4, h5]

/-- The five plain fields of a layers' plan for its link are the sub-proof's plan's. -/
theorem layersPlan_fields (X : Model.Verify.Public) (tokv : Array Nat) (g : Nat)
    (hp : Model.Layer.HPlan2) :
    (Model.Verify.layersPlanOf X tokv g hp).tl = hp.tl ∧
      (Model.Verify.layersPlanOf X tokv g hp).Fp = hp.Fp ∧
      (Model.Verify.layersPlanOf X tokv g hp).Tp = hp.Tp ∧
      (Model.Verify.layersPlanOf X tokv g hp).ns = hp.ns ∧
      (Model.Verify.layersPlanOf X tokv g hp).NCL = hp.NCL :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The five plain fields of the head's plan for its link are the sub-proof's plan's. -/
theorem headPlan_fields (X : Model.Verify.Public) (cov : Model.Head.Covered) :
    (Model.Verify.headPlanOf X cov).tl = X.H.tl ∧ (Model.Verify.headPlanOf X cov).Fp = X.H.Fp ∧
      (Model.Verify.headPlanOf X cov).Tp = X.H.Tp ∧ (Model.Verify.headPlanOf X cov).ns = X.H.ns ∧
      (Model.Verify.headPlanOf X cov).NCL = X.H.NCL :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- But for arrayOf and the routines, the list does not depend on the covered positions. -/
theorem listedOf_strip (X : Model.Verify.Public) (c0 c1 : Model.Head.Covered) :
    (listedOf X c0).map strip = (listedOf X c1).map strip := by
  have e1 := map_flatMap_congr strip
    (fun x : Model.Layer.HPlan2 × Nat =>
      groupLinks X.NGr X.p4 (X.A.map Model.Verify.attentionPlanOf)
        (Model.Verify.layersPlanOf X c0.tokv x.2 x.1) x.2)
    (fun x : Model.Layer.HPlan2 × Nat =>
      groupLinks X.NGr X.p4 (X.A.map Model.Verify.attentionPlanOf)
        (Model.Verify.layersPlanOf X c1.tokv x.2 x.1) x.2)
    (fun x => by
      obtain ⟨a1, a2, a3, a4, a5⟩ := layersPlan_fields X c0.tokv x.2 x.1
      obtain ⟨b1, b2, b3, b4, b5⟩ := layersPlan_fields X c1.tokv x.2 x.1
      unfold groupLinks
      rw [List.map_cons, List.map_cons,
        strip_link_congr (s := Model.Verify.layersPlanOf X c0.tokv x.2 x.1)
          (t := Model.Verify.layersPlanOf X c1.tokv x.2 x.1) (a1.trans b1.symm) (a2.trans b2.symm)
          (a3.trans b3.symm) (a4.trans b4.symm) (a5.trans b5.symm)])
    X.G.toList.zipIdx
  obtain ⟨a1, a2, a3, a4, a5⟩ := headPlan_fields X c0
  obtain ⟨b1, b2, b3, b4, b5⟩ := headPlan_fields X c1
  have e2 : strip ((Model.Verify.headPlanOf X c0).link "H" (1 + X.NGr) 2 0 true) =
      strip ((Model.Verify.headPlanOf X c1).link "H" (1 + X.NGr) 2 0 true) :=
    strip_link_congr (a1.trans b1.symm) (a2.trans b2.symm) (a3.trans b3.symm) (a4.trans b4.symm)
      (a5.trans b5.symm) _ _ _ _ _
  unfold listedOf beforeHead
  rw [List.map_append, List.map_append, e1, List.map_cons, List.map_cons, e2]

/-- **The list that the program runs is listedOf X cov, in every field but arrayOf.** -/
theorem joined_bare {X : Model.Verify.Public} {chains : Model.Verify.Chains}
    {built : Model.Stages.LinksH} {cov : Model.Head.Covered} {ls : Array LinkH}
    (hb : Model.Verify.builtOf X chains = .ok built) (hl : Model.Verify.linksOf X cov = .ok ls) :
    (built.links.zipWith (fun b l => { b with run := l.run }) ls).toList.map bare =
      (listedOf X cov).map bare := by
  unfold Model.Verify.builtOf at hb
  obtain ⟨ls0, hl0, hb1⟩ := ok_of_bind hb
  have kb := buildLinksH_keeps bare (fun _ _ => rfl) hb1
  rw [linksOf_listed hl0] at kb
  rw [Array.toList_zipWith, linksOf_listed hl]
  exact zip_bare _ _ _ kb (listedOf_strip X default cov)

/-- **Its fields arrayOf are those of the links as built.** -/
theorem joined_arrays {X : Model.Verify.Public} {chains : Model.Verify.Chains}
    {built : Model.Stages.LinksH} {cov : Model.Head.Covered} {ls : Array LinkH}
    (hb : Model.Verify.builtOf X chains = .ok built) (hl : Model.Verify.linksOf X cov = .ok ls) :
    (built.links.zipWith (fun b l => { b with run := l.run }) ls).toList.map (·.arrayOf) =
      built.links.toList.map (·.arrayOf) := by
  unfold Model.Verify.builtOf at hb
  obtain ⟨ls0, hl0, hb1⟩ := ok_of_bind hb
  have kb := congrArg List.length (buildLinksH_keeps bare (fun _ _ => rfl) hb1)
  have ks := congrArg List.length (listedOf_strip X default cov)
  rw [linksOf_listed hl0, List.length_map, List.length_map] at kb
  rw [List.length_map, List.length_map] at ks
  rw [Array.toList_zipWith]
  exact zip_arrays _ _ (by rw [kb, ks, linksOf_listed hl])

end OnBytes.TieK
