-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeTable.lean: the honest side of the kind "lookup"
(K3): THE THREE PUBLIC EQUATIONS BETWEEN A SITE AND WHAT THE TABLE OF JOINTS' OWN FILLING READS OF
THE PUBLIC DATA AT THE SITE'S SEGMENT: shape, packing, first slot. They are spent by
Honest/K3/Law/Thread/ExchangeWorth.lean, which calls the three theorems. Theorems with proofs; no
definition.

  `site_place`       a site's parameters are those of the public data's place at its link and
                     sort, and fix its shape
  `table_digits`     at the digits' piece: the site's shape is the shape that the filling lays into
                     the smallness test's structure; the packing is 5; the first slot is the
                     place's
  `table_attention`  at the calls' piece of an attention segment: shape, packing, first slot are the
                     place's as the filling lays it
  `table_layers`     the same at a layers' segment

Each is CONDITIONAL ON the site being one of the public part's, on its sort, and on what the filling
reads at the site's link being there.

Limits. The lookup on the head's calls is not reached HERE (Honest/K3/Law/Thread/ExchangeHead.lean,
ExchangeHeadAll.lean). The theorem on the digits speaks of every link at which the public data hold
the place, the head's among them. No instance of these hypotheses is exhibited in this file.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.SiteShapes
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.Sites
import Johnson.Desc.First.Look.K3At

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc.First.Look (P lookAt placeAt digAt attAt layAt)

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

/-- **A site's parameters are those of the public data's place at its link and sort, and fix its
shape.** -/
theorem site_place (Z : Pub) (s : Site) (hs : s ∈ lookSites Z) :
    ∃ pl, lookAt Z.p.X s.link s.digits = some pl ∧
      s.p = P.ofPlace (OnBytes.Params.settingOf Z.p.X.P.frame) s.digits pl ∧
      s.p.shape = some s.shape := by
  unfold lookSites at hs
  obtain ⟨x, _, hx⟩ := List.mem_filterMap.1 hs
  have h2 := (FastLaw.siteAt_shape _ _ x s hx).2
  unfold siteAt at hx
  obtain ⟨p, hp, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨_, _, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨_, _, hx⟩ := Option.bind_eq_some_iff.1 hx
  unfold placeAt at hp
  obtain ⟨pl, hpl, rfl⟩ := Option.map_eq_some_iff.1 hp
  dsimp only at hx
  split at hx
  · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hx
    exact ⟨pl, hpl, rfl, h2⟩
  · obtain rfl := Option.some.inj hx
    exact ⟨pl, hpl, rfl, h2⟩

/-- **At the digits' piece.** CONDITIONAL ON the site, its sort, and what the filling reads. -/
theorem table_digits (Z : Pub) (s : Site) (hs : s ∈ lookSites Z) (hd : s.digits = true)
    {x : PlaceL} {tl : HTailF2} (hx : digAt Z.p.X s.link = some (x, tl)) :
    s.shape = tl.f9 ∧ s.p.lm = 5 ∧ s.p.first = x.F.next := by
  obtain ⟨pl, h1, h2, h3⟩ := site_place Z s hs
  obtain ⟨_, _, _, h5, _⟩ := Spec.site_digits Z s hs hd
  rw [hd] at h1 h2
  unfold digAt at hx
  obtain ⟨x', e1, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨tl', _, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨h', e3, hx⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
  obtain rfl : pl = x' := Option.some.inj (h1.symm.trans e1)
  rw [h2] at h3
  exact ⟨Option.some.inj (h3.symm.trans e3), h5, by rw [h2]; rfl⟩

/-- **At the calls' piece of an attention segment.** CONDITIONAL ON the same. -/
theorem table_attention (Z : Pub) (s : Site) (hs : s ∈ lookSites Z) (hd : s.digits = false)
    {x : PlaceL} {A : OnBytes.Attention.Shape} {tl : HTailF2}
    (hx : attAt Z.p.X s.link = some (x, A, tl)) :
    s.shape = x.fs ∧ s.p.lm = x.lm ∧ s.p.first = x.F.next := by
  obtain ⟨pl, h1, h2, h3⟩ := site_place Z s hs
  rw [hd] at h1 h2
  unfold attAt at hx
  split at hx
  · obtain ⟨x', e1, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨a, _, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', e3, hx⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨rfl, _⟩ := Prod.mk.inj hx
    obtain rfl : pl = x' := Option.some.inj (h1.symm.trans e1)
    rw [h2] at h3
    exact ⟨Option.some.inj (h3.symm.trans e3), by rw [h2]; rfl, by rw [h2]; rfl⟩
  · exact absurd hx (by simp)

/-- **At the calls' piece of a layers' segment.** CONDITIONAL ON the same. -/
theorem table_layers (Z : Pub) (s : Site) (hs : s ∈ lookSites Z) (hd : s.digits = false)
    {x : PlaceL} (hx : layAt Z.p.X s.link = some x) :
    s.shape = x.fs ∧ s.p.lm = x.lm ∧ s.p.first = x.F.next := by
  obtain ⟨pl, h1, h2, h3⟩ := site_place Z s hs
  rw [hd] at h1 h2
  unfold layAt at hx
  split at hx
  · obtain ⟨x', e1, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', e3, rfl⟩ := Option.map_eq_some_iff.1 hx
    obtain rfl : pl = x' := Option.some.inj (h1.symm.trans e1)
    rw [h2] at h3
    exact ⟨Option.some.inj (h3.symm.trans e3), by rw [h2]; rfl, by rw [h2]; rfl⟩
  · exact absurd hx (by simp)

#print axioms ProofFile.Honest.K3.Law.Exchange.site_place
#print axioms ProofFile.Honest.K3.Law.Exchange.table_digits
#print axioms ProofFile.Honest.K3.Law.Exchange.table_attention
#print axioms ProofFile.Honest.K3.Law.Exchange.table_layers

end ProofFile.Honest.K3.Law.Exchange
