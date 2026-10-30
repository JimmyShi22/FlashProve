-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/PlanShapes.lean: the links of the proof file's first chain alternate, in the
goals' scope, and which records of the public part belong to which link.

WHY. Means (Johnson/Goal/Meaning/Row.lean) speaks of each sub-proof in letters made of the public
part X. A law on a link's blocks speaks in the letters that these blocks are given. This file says,
of the LIST OF LINKS that the planner's two functions make, which link stands at which place, and
which of X's records belong to it; and how what Means reads is got out of these records.

WHAT IS SHOWN, in scope (InScope Z, readFiles Z = ok pp, publicOf = ok X):
  scope_plans       X.p4 = true, X.NGr = 12, X.y.h = layerShape X.P; for g < 12: X.G[g]? and X.A[g]?
                    are there, and the attention plan's shape is Hd.shapeA X g.
  built_at, zipped_place   where buildLinksH returns, its links are the given ones, place by place,
                    with arrayOf filled; so each link of the list that is run is the built link with
                    the routine of the request's link at the same place.
  links_alternate   THE CORE, over the two functions listLinksH and buildLinksH at ANY sub-plans G A
                    H (two lists: one without a request, one with): the list that is run has 25
                    links; at place 2 g stands a link of kind 0 and group g, at 2 g + 1 one of kind
                    1 and group g, at 24 one of kind 2; each with tl, Fp, Tp, ns, NCL of the first
                    list's sub-plan at its place.
  LinkGets, getsAt, getsOf, links_get   a rule that hands X's records out by a link's kind and group
                    (layers: X.layers, X.G[g], g; attention: X.A[g]; the head: X.hS, X.HLy, the
                    border, X.H, X.owner) gives, along that list, the records getsOf X k at each
                    place k < 25.
  MeansReads, readsOf, meansReads, reads_of_gets   THE PROJECTION: what Means reads at link k (2 g:
                    layerShape X.P, X.layers.sc, X.y, g; 2 g + 1: X.y and Hd.shapeA X g; 24: X.y,
                    pp.nf, pp.pol) is got out of getsOf X k: at the head by readings_agree
                    (Johnson/Goal/Meaning/Ties.lean): pp.pol = Hd.polOf X.hS and pp.nf = Hd.npOf
                    X.hS.
  plan_has_shapes, plan_has_shapes_made, link_tails_at   the same on the road planned | madeOf |
                    linksOf, with the links' tl, Fp, Tp as those of X.G[g], X.A[g].seam, X.H.

What is not claimed. THIS IS NOT "the plan has X's shapes" OF ANY DESCRIPTION. No description is
named. That a description's blocks are handed their letters by the rule getsAt is a reading of that
description's own text; a block's parameters may hold more than these records, or be made by the
link's number and not its record. A description that makes its list of links by other callers of
listLinksH and buildLinksH joins at links_alternate, not at plan_has_shapes. An attention plan's
field own (the sizes of its own rounds) against its shape: Johnson/Goal/Meaning/PlanOwn.lean.
Nothing on the plans' rounds. Nothing on soundness.
-/
import Johnson.Goal.Meaning.ScopeCore
import Johnson.Meaning.PlanIsPublic
import Johnson.Goal.Meaning.Ties
import OnBytes.Tie.Pv.Keeps.LinksBuilt
import Johnson.Road.Lane5AttPub
import Johnson.Road.FormsKeysCap

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model
open OnBytes OnBytes.Road OnBytes.Model
open OnBytes.Model.Verify (publicOf planned layerShape borderOf linksOf builtOf)
open OnBytes.Model.Stages (LinkH LinksH SubPlanH listLinksH buildLinksH)
open OnBytes.L5.LinksOrder (zipped linkG linkA linkHd ok_bind)
open VerifiableInference.OnPublicFiles.Flat (scalesAt)

/-! ## 1 The public part in scope -/

/-- **In scope: profile 4, twelve groups, the layout's shape, and all 24 plans.** -/
theorem scope_plans {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    X.p4 = true ∧ X.NGr = 12 ∧ X.y.h = layerShape X.P ∧
      ∀ g < 12, ∃ a, X.A[g]? = some a ∧ a.S = Hd.shapeA X g := by
  have A := Hd.core_of_scope hZ hR h
  have B := (Hd.eleven_of_core h A (Hd.npOf X.hS)).1
  have ey : X.y.h = layerShape X.P := layout_shape B.lay
  refine ⟨?_, B.groups, ey, fun g hg => ?_⟩
  · show X.y.h.p4 = true
    rw [ey]
    exact B.p4
  · obtain ⟨Ag, hA, eS, -⟩ := L5.label_public h B.p4 (g := g) (by rw [B.groups]; exact hg)
    exact ⟨Ag, hA, eS⟩

/-! ## 2 The list that is run, at any sub-plans -/

/-- Where buildLinksH returns, its links are the given ones with arrayOf filled. -/
theorem built_at {l₀ : Array LinkH} {NGr : ℕ} {p4 : Bool} {ws : WsLay} {first : Params.First}
    {B : LinksH} (h1 : buildLinksH l₀ NGr p4 ws first = .ok B) :
    B.links.size = l₀.size ∧
      ∀ (j : ℕ) (Y : LinkH), l₀[j]? = some Y →
        ∃ ar, B.links[j]? = some { Y with arrayOf := ar } := by
  unfold buildLinksH at h1
  obtain ⟨_, _, h2⟩ := ok_bind h1
  obtain ⟨_, _, h3⟩ := ok_bind h2
  obtain ⟨⟨named, declared⟩, hd, h4⟩ := ok_bind h3
  obtain ⟨a1, a2⟩ := OnBytes.L5.LinksOrder.declareLinks_at l₀ NGr p4 named declared hd
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
  exact ⟨a1, a2⟩

/-- A link of the list that is run: the built link with the request's link's routine. -/
theorem zipped_place {l₀ ls : Array LinkH} {NGr : ℕ} {p4 : Bool} {ws : WsLay}
    {first : Params.First} {B : LinksH} (hB : buildLinksH l₀ NGr p4 ws first = .ok B) {j : ℕ}
    {Y0 Y : LinkH} (hj0 : l₀[j]? = some Y0) (hj : ls[j]? = some Y) :
    ∃ ar, (zipped B ls)[j]? = some { Y0 with arrayOf := ar, run := Y.run } := by
  obtain ⟨ar, h1⟩ := (built_at hB).2 j Y0 hj0
  refine ⟨ar, ?_⟩
  unfold zipped
  rw [Array.getElem?_zipWith, h1, hj]

/-- What a link has of a sub-plan, with its kind and group. -/
structure IsLink (l : LinkH) (kind g : ℕ) (s : SubPlanH) : Prop where
  kind : l.kind = kind
  g : l.g = g
  tl : l.tl = s.tl
  Fp : l.Fp = s.Fp
  Tp : l.Tp = s.Tp
  ns : l.ns = s.ns
  NCL : l.NCL = s.NCL

/-- **THE CORE: the links alternate**, at twelve groups with attention, whatever the sub-plans. -/
theorem links_alternate {G₀ A₀ G₁ A₁ : Array SubPlanH} {H₀ H₁ : SubPlanH} {l₀ ls : Array LinkH}
    {ws : WsLay} {first : Params.First} {B : LinksH}
    (h₀ : listLinksH 12 true G₀ A₀ H₀ = .ok l₀) (hB : buildLinksH l₀ 12 true ws first = .ok B)
    (hl : listLinksH 12 true G₁ A₁ H₁ = .ok ls) :
    (zipped B ls).size = 25 ∧
      (∀ g < 12, ∃ s a l l', G₀[g]? = some s ∧ A₀[g]? = some a ∧
        (zipped B ls)[2 * g]? = some l ∧ IsLink l 0 g s ∧
        (zipped B ls)[2 * g + 1]? = some l' ∧ IsLink l' 1 g a) ∧
      ∃ l, (zipped B ls)[24]? = some l ∧ IsLink l 2 0 H₀ := by
  obtain ⟨g0, a0, z0, p0, e0⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  obtain ⟨g1, a1, z1, p1, e1⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ hl
  refine ⟨?_, fun g hg => ?_, ?_⟩
  · unfold zipped
    rw [Array.size_zipWith, (built_at hB).1, z0, z1]
    rfl
  · have s0 : G₀[g]? = some G₀[g] := Array.getElem?_eq_getElem (by omega)
    have t0 : A₀[g]? = some A₀[g] := Array.getElem?_eq_getElem (by omega)
    have s1 : G₁[g]? = some G₁[g] := Array.getElem?_eq_getElem (by omega)
    have t1 : A₁[g]? = some A₁[g] := Array.getElem?_eq_getElem (by omega)
    obtain ⟨q0, q0'⟩ := p0 g _ _ s0 t0
    obtain ⟨q1, q1'⟩ := p1 g _ _ s1 t1
    obtain ⟨ar, e⟩ := zipped_place hB q0 q1
    obtain ⟨ar', e'⟩ := zipped_place hB q0' q1'
    exact ⟨_, _, _, _, s0, t0, e, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, e',
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · obtain ⟨ar, e⟩ := zipped_place hB e0 e1
    exact ⟨_, e, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-! ## 3 Which records of the public part belong to which link -/

/-- Records of the public part, as they belong to a link. -/
inductive LinkGets where
  | layers (P : Layer.Pub) (hp : Layer.HPlan2) (g : ℕ)
  | attention (a : Attention.Plan)
  | head (h : Head.Shape) (L : Head.HL) (b : Head.Border) (H : Head.HPlanH2) (o : Head.Owner)

/-- A rule that hands the records out: by a link's kind and group. -/
def getsAt (W : Verify.Public) (l : LinkH) : Option LinkGets :=
  if l.kind = 0 then (W.G[l.g]?).map fun hp => .layers W.layers hp l.g
  else if l.kind = 1 then (W.A[l.g]?).map .attention
  else some (.head W.hS W.HLy (borderOf W.y) W.H W.owner)

/-- The records of link k: 2 g: group g of layers; 2 g + 1: its attention; 24: the head. -/
def getsOf (X : Verify.Public) (k : ℕ) : Option LinkGets :=
  if k = 24 then some (.head X.hS X.HLy (borderOf X.y) X.H X.owner)
  else if k % 2 = 0 then (X.G[k / 2]?).map fun hp => .layers X.layers hp (k / 2)
  else (X.A[k / 2]?).map .attention

/-- **Along the list that is run the rule gives each link its records**, and they are there. -/
theorem links_get {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (hG : X.G.size = 12)
    {G₀ A₀ G₁ A₁ : Array SubPlanH} {H₀ H₁ : SubPlanH} {l₀ ls : Array LinkH} {ws : WsLay}
    {first : Params.First} {B : LinksH} (h₀ : listLinksH X.NGr X.p4 G₀ A₀ H₀ = .ok l₀)
    (hB : buildLinksH l₀ X.NGr X.p4 ws first = .ok B)
    (hl : listLinksH X.NGr X.p4 G₁ A₁ H₁ = .ok ls) :
    (zipped B ls).size = 25 ∧
      ∀ k < 25, ((zipped B ls)[k]?).bind (getsAt X) = getsOf X k ∧ (getsOf X k).isSome = true := by
  obtain ⟨hq, hN, -, hA⟩ := scope_plans hZ hR h
  rw [hq, hN] at h₀ hB hl
  obtain ⟨sz, alt, l24, e24, I24⟩ := links_alternate h₀ hB hl
  refine ⟨sz, fun k hk => ?_⟩
  by_cases h24 : k = 24
  · subst h24
    rw [e24]
    refine ⟨?_, rfl⟩
    show getsAt X l24 = _
    unfold getsAt
    rw [I24.kind]
    rfl
  · by_cases he : k % 2 = 0
    · obtain ⟨g, rfl⟩ : ∃ g, k = 2 * g := ⟨k / 2, by omega⟩
      obtain ⟨s, a, l, l', -, -, e, I, -, -⟩ := alt g (by omega)
      have hg : X.G[g]? = some X.G[g] := Array.getElem?_eq_getElem (by omega)
      rw [e]
      unfold getsOf
      rw [if_neg h24, if_pos he, show 2 * g / 2 = g by omega, hg]
      refine ⟨?_, rfl⟩
      show getsAt X l = _
      unfold getsAt
      rw [I.kind, I.g, hg]
      rfl
    · obtain ⟨g, rfl⟩ : ∃ g, k = 2 * g + 1 := ⟨k / 2, by omega⟩
      obtain ⟨s, a, l, l', -, -, -, -, e', I'⟩ := alt g (by omega)
      obtain ⟨Ag, hAg, -⟩ := hA g (by omega)
      rw [e']
      unfold getsOf
      rw [if_neg h24, if_neg he, show (2 * g + 1) / 2 = g by omega, hAg]
      refine ⟨?_, rfl⟩
      show getsAt X l' = _
      unfold getsAt
      rw [I'.kind, I'.g, hAg]
      rfl

/-! ## 4 What Means reads, out of the records -/

/-- What Means reads of the public files at a link. -/
inductive MeansReads where
  | layers (h : Layer.Shape) (sc : Layer.Scales) (y : Layer.Lay) (g : ℕ)
  | attention (y : Layer.Lay) (S : Attention.Shape)
  | head (y : Layer.Lay) (nf : NormPar) (pol : AcceptancePolicy)

/-- What Means reads at link k (MeansG; MeansA with its seam; MeansH). -/
def meansReads (X : Verify.Public) (pp : ScalesAndPolicy) (k : ℕ) : MeansReads :=
  if k = 24 then .head X.y pp.nf pp.pol
  else if k % 2 = 0 then .layers (layerShape X.P) X.layers.sc X.y (k / 2)
  else .attention X.y (Hd.shapeA X (k / 2))

/-- The projection. y: the layers' layout, which no record of attention or of the head holds. -/
def readsOf (y : Layer.Lay) : LinkGets → MeansReads
  | .layers P _ g => .layers P.y.h P.sc P.y g
  | .attention a => .attention y a.S
  | .head h _ _ _ _ => .head y (Hd.npOf h) (Hd.polOf h)

/-- **What Means reads at link k is got out of the link's records.** -/
theorem reads_of_gets {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {k : ℕ} (hk : k < 25) {r : LinkGets}
    (hr : getsOf X k = some r) : readsOf X.y r = meansReads X pp k := by
  obtain ⟨-, -, ey, hA⟩ := scope_plans hZ hR h
  have A := Hd.core_of_scope hZ hR h
  obtain ⟨tP, tS⟩ := VerifiableInference.Meaning.readings_agree Z pp lay X hR h
  have tS := tS (A.num 2)
  unfold getsOf at hr
  unfold meansReads
  by_cases h24 : k = 24
  · rw [if_pos h24] at hr ⊢
    obtain rfl := Option.some.inj hr
    have en : pp.nf = (scalesAt X).nf := congrArg Cm.Scales.nf tS
    show MeansReads.head X.y (Hd.npOf X.hS) (Hd.polOf X.hS) = _
    rw [en, tP]
    rfl
  · rw [if_neg h24] at hr ⊢
    by_cases he : k % 2 = 0
    · rw [if_pos he] at hr ⊢
      obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 hr
      show MeansReads.layers X.y.h X.layers.sc X.y (k / 2) = _
      rw [ey]
    · rw [if_neg he] at hr ⊢
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hr
      obtain ⟨Ag, hAg, eS⟩ := hA (k / 2) (by omega)
      obtain rfl : Ag = a := Option.some.inj (hAg.symm.trans ha)
      show MeansReads.attention X.y Ag.S = _
      rw [eS]

/-! ## 5 On the road planned | madeOf | linksOf -/

/-- What planned returns holds the links that builtOf has returned. -/
theorem built_of_planned {pol KL : ByteArray} {layout : Option ByteArray} {p : Verify.Planned}
    (h : planned pol KL layout = .ok p) : builtOf p.X p.chains = .ok p.built := by
  unfold planned at h
  obtain ⟨X, _, h⟩ := bind_ok h
  obtain ⟨chains, _, h⟩ := bind_ok h
  obtain ⟨built, hb, h⟩ := bind_ok h
  cases h
  exact hb

/-- **On that road**: 25 links; the rule gives each its records; they are there. -/
theorem plan_has_shapes {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {p : Verify.Planned}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hp : planned Z.pol Z.KL lay = .ok p) {cov : Head.Covered} {ls : Array LinkH}
    (hl : linksOf p.X cov = .ok ls) :
    (zipped p.built ls).size = 25 ∧
      ∀ k < 25, ((zipped p.built ls)[k]?).bind (getsAt p.X) = getsOf p.X k ∧
        (getsOf p.X k).isSome = true := by
  have h := public_of_planned hp
  have hB := built_of_planned hp
  have hG : p.X.G.size = 12 :=
    (OnBytes.L5.LinksOrder.linksOf_size hl).1.trans (scope_plans hZ hR h).2.1
  unfold builtOf at hB
  obtain ⟨l₀, h₀, hB⟩ := ok_bind hB
  exact links_get hZ hR h hG h₀ hB hl

/-- The same from the call madeOf. -/
theorem plan_has_shapes_made {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hm : Johnson.G.OfPlan.madeOf Z.pol lay Z.KL = .ok m) {cov : Head.Covered} {ls : Array LinkH}
    (hl : linksOf m.p.X cov = .ok ls) :
    (zipped m.p.built ls).size = 25 ∧
      ∀ k < 25, ((zipped m.p.built ls)[k]?).bind (getsAt m.p.X) = getsOf m.p.X k ∧
        (getsOf m.p.X k).isSome = true := by
  have hp : planned Z.pol Z.KL (some lay) = .ok m.p := by
    unfold Johnson.G.OfPlan.madeOf at hm
    obtain ⟨p, hp, hm⟩ := bind_ok hm
    obtain ⟨l, _, hm⟩ := bind_ok hm
    split at hm
    · cases hm
      exact hp
    · cases hm
  exact plan_has_shapes hZ hR hp hl

/-- **On that road a link's closing plan, planned state and list of arrays are its plan's.** -/
theorem link_tails_at {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {p : Verify.Planned}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hp : planned Z.pol Z.KL lay = .ok p) {cov : Head.Covered} {ls : Array LinkH}
    (hl : linksOf p.X cov = .ok ls) :
    (∀ g < 12, ∃ hpl a l l', p.X.G[g]? = some hpl ∧ p.X.A[g]? = some a ∧
      (zipped p.built ls)[2 * g]? = some l ∧ l.tl = hpl.tl ∧ l.Fp = hpl.Fp ∧ l.Tp = hpl.Tp ∧
      (zipped p.built ls)[2 * g + 1]? = some l' ∧ l'.tl = a.seam.tl ∧ l'.Fp = a.seam.Fp ∧
        l'.Tp = a.seam.Tp) ∧
      ∃ l, (zipped p.built ls)[24]? = some l ∧ l.tl = p.X.H.tl ∧ l.Fp = p.X.H.Fp ∧
        l.Tp = p.X.H.Tp := by
  have h := public_of_planned hp
  have hB := built_of_planned hp
  obtain ⟨hq, hN, -, hA⟩ := scope_plans hZ hR h
  have hG : p.X.G.size = 12 := (OnBytes.L5.LinksOrder.linksOf_size hl).1.trans hN
  refine ⟨fun g hg => ?_, ?_⟩
  · have hg' : p.X.G[g]? = some p.X.G[g] := Array.getElem?_eq_getElem (by omega)
    obtain ⟨a, ha, -⟩ := hA g hg
    obtain ⟨ar, e⟩ := OnBytes.L5.LinksOrder.zipped_layers hB hl g _ hg'
    obtain ⟨ar', e'⟩ := OnBytes.L5.LinksOrder.zipped_attention hB hl hq g a ha
    have el : Stages.layersLink p.X.p4 g = 2 * g := by
      unfold Stages.layersLink
      rw [if_pos hq]
    rw [el] at e
    exact ⟨_, a, _, _, hg', ha, e, rfl, rfl, rfl, e', rfl, rfl, rfl⟩
  · obtain ⟨ar, e⟩ := OnBytes.L5.LinksOrder.zipped_head hB hl
    rw [if_pos hq, hN] at e
    exact ⟨_, e, rfl, rfl, rfl⟩

end Meaning

#print axioms Meaning.scope_plans
#print axioms Meaning.built_at
#print axioms Meaning.zipped_place
#print axioms Meaning.links_alternate
#print axioms Meaning.links_get
#print axioms Meaning.reads_of_gets
#print axioms Meaning.built_of_planned
#print axioms Meaning.plan_has_shapes
#print axioms Meaning.plan_has_shapes_made
#print axioms Meaning.link_tails_at
