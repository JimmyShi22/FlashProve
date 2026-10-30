-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Names/NamesAtLinks.lean: THE NAMES' TIE, OVER ANY LIST OF LINKS THAT BEARS THE
LAYERS' PLANS AT THE EVEN PLACES: under the public core, at each of the twelve feed-forward segments
and each of its matrices, the name that the built segment lists at the matrix's tree is (owner,
name) by the public parameters' label. The join of the four files beside it with the laws on
the label.

  `built_declared`: where buildLinksH returns B, declareLinks has returned B.links.
  `mem_zipT`: two entries at one place stand as a pair in the zipped list.
  `GroupAt`, `group_at`: under the public core, what is known of one group's lists: nine matrices;
    which is of kind 1; which has a number in txOf; what the plan lays at the seam.
  **`names_at_links`**: see its statement. PREMISES: h: X is what publicOf returns · C: the public
    core · h4: X.p4 = true · hN: X.NGr = 12 (both: theorems in the goals' scope) · hl0: the list l₀
    bears at place 2 g a link whose field tl is that of the plan X.G[g] · hB: buildLinksH returns B
    at l₀.
Limits. hl0 and hB are premises here: the plain road to the public part's own built segments pays
them in another file. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on
soundness.


-/
import Johnson.Road.K4.Names.DeclaredNames
import Johnson.Road.K4.Names.PlanNames
import Johnson.Road.K4.Names.BorderKinds
import Johnson.Goal.Meaning.HidSeatsOf
import Johnson.Goal.Meaning.HidPlanNM
import Johnson.Goal.Meaning.Pub34Scope
import Johnson.Goal.Meaning.PlanShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Names
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open OnBytes.Model.Layer (matIx tailsOf)
open OnBytes.Model.Stages (LinkH LinksH buildLinksH declareLinks matrixName layersLink)
open OnBytes.L5.LinksOrder (ok_bind)
open Meaning (labAt ownerK ownerA nameOf matsAt tlAt ownerOf)

/-- Where buildLinksH returns B, declareLinks has returned B.links. -/
theorem built_declared {l₀ : Array LinkH} {NGr : Nat} {p4 : Bool} {ws : WsLay}
    {first : Params.First} {B : LinksH} (h1 : buildLinksH l₀ NGr p4 ws first = .ok B) :
    ∃ declared, declareLinks l₀ NGr p4 = .ok (B.links, declared) := by
  unfold buildLinksH at h1
  obtain ⟨_, _, h2⟩ := ok_bind h1
  obtain ⟨_, _, h3⟩ := ok_bind h2
  obtain ⟨⟨named, declared⟩, hd, h4⟩ := ok_bind h3
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
  exact ⟨declared, hd⟩

/-- Two entries at one place stand as a pair in the zipped list. -/
theorem mem_zipT {α β : Type} {A : Array α} {B : Array β} {r : Nat} {a : α} {b : β}
    (ha : A[r]? = some a) (hb : B[r]? = some b) : (a, b) ∈ zipT A.toList B.toList := by
  rw [zipT_eq]
  refine List.mem_of_getElem? (i := r) (List.getElem?_zip_eq_some.2 ⟨?_, ?_⟩)
  · rw [Array.getElem?_toList]
    exact ha
  · rw [Array.getElem?_toList]
    exact hb

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}

/-- What is known of one group's lists, under the public core. -/
structure GroupAt (X : Verify.Public) (g : Nat) (hp : Layer.HPlan2) (mats : Array TMat)
    (txOf : Array (Option Nat)) (ft : Array T2Foreign) (tl0 : HTailF2) : Prop where
  shape : ({ tau := X.layers.set.tau, lidb := X.layers.set.lidb } : HTailF2).shapeF mats txOf ft
    #[false, false, true, false] X.layers.y.h.tau = .ok tl0
  same : SameN tl0 hp.tl
  size : mats.size = 9
  kind : ∀ μ, μ < 9 → (mats.getD μ {}).kind = if (μ == 8 && g != 0) = true then 1 else 0
  tx : ∀ μ, μ < 9 → (txOf.getD μ none).isSome =
    ((mats.getD μ {}).kind == 0 && (μ == 7 || μ == 6))
  foreign : ∀ μ, μ < 9 → (mats.getD μ {}).kind = 1 → ∃ j, (mats.getD μ {}).foreign = some j
  ft1 : hp.tl.ix.FT.size = (if g == 0 then 0 else 1)
  seam : ∀ Oo, (if g = 0 then none else X.G[g - 1]?) = some Oo →
    ∃ pl, hp.tl.plFor[0]? = some pl ∧ pl.owner = some (g - 1) ∧
      pl.rootIndex = some (Oo.tl.pkMat.size + Oo.tl.ix.TX.size - 1)

/-- **Under the public core: one group's lists.** -/
theorem group_at (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) (h4 : X.p4 = true)
    (hN : X.NGr = 12) {g : Nat} (hg : g < 12) {hp : Layer.HPlan2} (hgp : X.G[g]? = some hp) :
    ∃ mats txOf ft tl0, GroupAt X g hp mats txOf ft tl0 := by
  obtain ⟨i6, i7, i8⟩ := Meaning.ix_of_core h C
  obtain ⟨mats, txOf, ft, tl0, hb, hS, N, hFT, hO⟩ := planG_names (Fo.Pub.public_G h g hp hgp)
  obtain ⟨_, eT, _⟩ := Meaning.P34.more_of_public h
  obtain ⟨b, hb', em⟩ := Hd.planG_mats (Fo.Pub.public_G h g hp hgp)
  obtain rfl : b = (mats, txOf, ft) := Except.ok.inj (hb'.symm.trans hb)
  have e9 : mats.size = 9 := by
    have := Meaning.size_even h C hg
    rw [Meaning.matsAt_even hg hgp, em] at this
    exact this
  obtain ⟨s1, _, hk⟩ := bordersOf_kinds hb
  have s9 : (X.layers.tails.getD g {}).mats.size = 9 := by rw [← s1, e9]
  have hkind : ∀ μ, μ < 9 →
      (mats.getD μ {}).kind = if (μ == 8 && g != 0) = true then 1 else 0 := by
    intro μ hμ
    rw [(hk μ (by rw [s9]; exact hμ)).1]
    have t := tails_kind (y := X.y) (g := g) (μ := μ) (by
      show g < X.NGr
      rw [hN]
      exact hg) (by rw [← eT, s9]; exact hμ)
    rw [← eT, i8] at t
    exact t
  refine ⟨mats, txOf, ft, tl0, hS, N, e9, hkind, fun μ hμ => ?_, fun μ hμ => ?_, hFT, hO⟩
  · have t := (hk μ (by rw [s9]; exact hμ)).2.1
    rw [t]
    unfold bord
    show (((X.layers.tails.getD g {}).mats.getD μ {}).kind == 0 &&
      (μ == (matIx X.y).iXO || (X.p4 && μ == (matIx X.y).iQA))) = _
    rw [← (hk μ (by rw [s9]; exact hμ)).1, i7, i6, h4, Bool.true_and]
  · exact (hk μ (by rw [s9]; exact hμ)).2.2

/-- **The names' tie, over a list of links that bears the layers' plans at the even places.** -/
theorem names_at_links (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    (h4 : X.p4 = true) (hN : X.NGr = 12) {l₀ : Array LinkH} {ws : WsLay} {first : Params.First}
    {B : LinksH}
    (hl0 : ∀ g hp, g < 12 → X.G[g]? = some hp → ∃ Y, l₀[2 * g]? = some Y ∧ Y.tl = hp.tl)
    (hB : buildLinksH l₀ X.NGr X.p4 ws first = .ok B) {g : Nat} (hg : g < 12) {μ : Nat}
    (hμ : μ < (_root_.Meaning.sizesOf X (2 * g)).NM) :
    ((B.links.map (·.arrayOf)).getD (2 * g) #[])[(tlAt X (2 * g)).gtTree.getD μ 0]? =
      some (ownerK (labAt X (2 * g) μ), nameOf (ownerA (labAt X (2 * g) μ))) := by
  obtain ⟨_, i7, i8⟩ := Meaning.ix_of_core h C
  obtain ⟨hp, hgp⟩ := Meaning.planG_there h C hg
  have hk : 2 * g < 25 := by omega
  have hμm : μ < (matsAt X (2 * g)).size := by
    rw [← (Meaning.follows_of_core h C).NM _ hk]
    exact hμ
  have hμ9 : μ < 9 := by
    rw [Meaning.size_even h C hg] at hμm
    exact hμm
  have etl : tlAt X (2 * g) = hp.tl := by
    unfold Meaning.tlAt
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show 2 * g / 2 = g by omega, hgp]
    rfl
  obtain ⟨Y, hY, eY⟩ := hl0 g hp hg hgp
  obtain ⟨declared, hd⟩ := built_declared hB
  obtain ⟨ar, har, N1, N2, N3⟩ := declared_names hd hY
  have eL : (B.links.map (·.arrayOf)).getD (2 * g) #[] = ar := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, har]
    rfl
  rw [eY] at N1 N2 N3
  obtain ⟨mats, txOf, ft, tl0, Gg⟩ := group_at h C h4 hN hg hgp
  have ol := Meaning.owner_label h C hk hμm
  obtain ⟨S1, S2, S3⟩ := shapeF_names Gg.shape (μ := μ) (by rw [Gg.size]; exact hμ9)
  rw [← Gg.same.ix, ← Gg.same.gtTree, ← Gg.same.pkMat] at S1
  rw [← Gg.same.ix, ← Gg.same.gtTree, ← Gg.same.pxMat] at S2
  rw [← Gg.same.ix, ← Gg.same.gtTree] at S3
  rw [eL, etl]
  by_cases hc : μ = 8 ∧ g ≠ 0
  · obtain ⟨rfl, hg0⟩ := hc
    have k1 : (mats.getD 8 {}).kind = 1 := by
      rw [Gg.kind 8 hμ9, if_pos (by simp [hg0])]
    obtain ⟨j, hj⟩ := Gg.foreign 8 hμ9 k1
    obtain ⟨f1, _⟩ := S3 k1 j hj
    have hj0 : j = 0 := by
      have hl := (Array.getElem?_eq_some_iff.1 f1).1
      rw [Gg.ft1, if_neg (by simpa using hg0)] at hl
      omega
    subst hj0
    obtain ⟨Oo, hOo⟩ := Meaning.planG_there h C (g := g - 1) (by omega)
    obtain ⟨pl, p1, p2, p3⟩ := Gg.seam Oo (by rw [if_neg hg0]; exact hOo)
    obtain ⟨owner, ri, Yo, mu, a1, a2, a3, a4, a5⟩ := N3 _ (mem_zipT f1 p1)
    obtain rfl : g - 1 = owner := Option.some.inj (p2.symm.trans a1)
    obtain rfl : Oo.tl.pkMat.size + Oo.tl.ix.TX.size - 1 = ri := Option.some.inj (p3.symm.trans a2)
    have eLk : layersLink X.p4 (g - 1) = 2 * (g - 1) := by
      unfold layersLink
      rw [h4, if_pos rfl]
    rw [eLk] at a3 a5
    obtain ⟨Yo', hYo, eYo⟩ := hl0 (g - 1) Oo (by omega) hOo
    obtain rfl : Yo' = Yo := Option.some.inj (hYo.symm.trans a3)
    rw [eYo, show Oo.tl.pkMat.size + Oo.tl.ix.TX.size - 1 - Oo.tl.pkMat.size =
      Oo.tl.ix.TX.size - 1 by omega] at a4
    obtain ⟨matsO, txO, ftO, tlO, Go⟩ := group_at h C h4 hN (g := g - 1) (by omega) hOo
    have k7 : (matsO.getD 7 {}).kind = 0 := by
      rw [Go.kind 7 (by omega), if_neg (by simp)]
    have hlast := shapeF_last Go.shape (μ := 7) (by rw [Go.size]; omega)
      (by
        unfold isPX
        rw [Go.tx 7 (by omega), k7]
        rfl)
      (fun k h1 h2 => by
        rw [Go.size] at h2
        obtain rfl : k = 8 := by omega
        unfold isPX
        rw [Go.tx 8 (by omega)]
        simp)
    rw [← Go.same.ix, ← Go.same.pxMat] at hlast
    obtain rfl : mu = 7 := Option.some.inj (a4.symm.trans hlast)
    have oo : ownerOf X (2 * g) 8 = (2 * (g - 1), 7) := by
      unfold Meaning.ownerOf
      rw [if_neg (by omega), if_neg (by omega), if_pos ⟨i8.symm, by omega⟩, i7,
        show 2 * g - 2 = 2 * (g - 1) by omega]
    rw [oo] at ol
    have eK : ownerK (labAt X (2 * g) 8) = 2 * (g - 1) := congrArg Prod.fst ol
    have eA : ownerA (labAt X (2 * g) 8) = 7 := congrArg Prod.snd ol
    rw [eK, eA]
    exact a5
  · have k0 : (mats.getD μ {}).kind = 0 := by
      rw [Gg.kind μ hμ9, if_neg (by
        intro hx
        rw [Bool.and_eq_true] at hx
        exact hc ⟨by simpa using hx.1, by simpa using hx.2⟩)]
    have oo : ownerOf X (2 * g) μ = (2 * g, μ) := by
      unfold Meaning.ownerOf
      rw [if_neg (by omega), if_neg (by omega), if_neg (by
        rintro ⟨e1, e2⟩
        exact hc ⟨e1.trans i8, by omega⟩)]
    rw [oo] at ol
    have eK : ownerK (labAt X (2 * g) μ) = 2 * g := congrArg Prod.fst ol
    have eA : ownerA (labAt X (2 * g) μ) = μ := congrArg Prod.snd ol
    rw [eK, eA]
    cases ht : txOf.getD μ none with
    | none =>
      obtain ⟨r, r1, r2⟩ := S1 k0 ht
      exact N1 _ (mem_zipT r1 r2)
    | some i =>
      obtain ⟨r1, r2⟩ := S2 k0 i ht
      exact N2 _ (mem_zipT r1 r2)

end OnBytes.Road.K4.Names

#print axioms OnBytes.Road.K4.Names.built_declared
#print axioms OnBytes.Road.K4.Names.group_at
#print axioms OnBytes.Road.K4.Names.names_at_links
