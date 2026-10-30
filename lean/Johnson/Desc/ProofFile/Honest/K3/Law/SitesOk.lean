-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/SitesOk.lean: at every site of a public part the face is the
face of the site's shape, and the shape passes the library's test on its numbers. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the face of a shape h is `faceOf h`
(Johnson/Desc/First/Look/K3LookupGeneral.lean). The library's test on a shape's numbers is `FoNums.ok`
(OnBytes/Tie/Pv/Lookup/Port/FoNums.lean).

What is shown.
  `site_made_shape`: a site that `siteAt` (Honest/K3/Lot.lean) makes has the face of its shape, and
    its shape is the one that the verifier's own public parameters at the place fix.
  `sites_shape_ok`: so, at every site of a public part, the face is the face of the site's shape,
    and the shape passes the library's test.

Hypotheses that remain.
  `hs`: (in `site_made_shape`) `siteAt` returns the site s.
  In `sites_shape_ok`: s is a site of the public part Z (`lookSites Z`, Lot.lean).

How the proof goes. The second theorem calls the first and the library's `k3_shape_ok`
(Johnson/Desc/First/Look/K3RoundsAt.lean).

Users. The two stand in a file of their own so that a caller need not import the files on the
summands that fold tables (Honest/K3/FastLaw/). `site_face_ok` (Honest/K3/Law/SomeKeyAt.lean
[not in this library]) calls the second; Honest/K3/Good/MarksLooks.lean imports this file too, and
so does Johnson/AtFull/Shape/FaceAtSites.lean.
The same two statements stand, with the same proofs, under other names, in
Honest/K3/FastLaw/Sites.lean (`siteAt_shape`, `sites_ok`). The two conjuncts of the first are also
among the eight of `site_facts` (Honest/K3/Law/MemberSite.lean). They are stated once more here for
the sake of the imports: this file imports Honest/K3/Lot.lean and one file of the library, and no
other.

Limits. Both statements are on public data alone. No instance of these hypotheses is exhibited in
this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Lot
import Johnson.Desc.First.Look.K3RoundsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K3 (faceOf)

/-- A site that `siteAt` makes has the face of its shape, and its shape is the one that its public
parameters fix. Conditional on `siteAt` returning the site. -/
theorem site_made_shape (X : OnBytes.Model.Verify.Public) (ps : List Spot)
    (x : Nat × Bool × Place) (s : Site) (hs : siteAt X ps x = some s) :
    s.at_.face = faceOf s.shape ∧ s.p.shape = some s.shape := by
  unfold siteAt at hs
  obtain ⟨p, _, hs⟩ := Option.bind_eq_some_iff.1 hs
  obtain ⟨h, hh, hs⟩ := Option.bind_eq_some_iff.1 hs
  obtain ⟨_, _, hs⟩ := Option.bind_eq_some_iff.1 hs
  dsimp only at hs
  split at hs
  · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hs
    exact ⟨rfl, hh⟩
  · obtain rfl := Option.some.inj hs
    exact ⟨rfl, hh⟩

/-- **At every site of a public part the face is the face of the site's shape, and the shape passes
the library's test.** -/
theorem sites_shape_ok (Z : Pub) : ∀ s ∈ lookSites Z,
    s.at_.face = faceOf s.shape ∧ FoNums.ok s.shape = true := by
  intro s hs
  unfold lookSites at hs
  obtain ⟨x, _, hx⟩ := List.mem_filterMap.1 hs
  obtain ⟨h1, h2⟩ := site_made_shape _ _ x s hx
  exact ⟨h1, VerifiableInference.OnPublicFiles.k3_shape_ok h2⟩

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.site_made_shape
#print axioms ProofFile.Honest.K3.Law.sites_shape_ok
