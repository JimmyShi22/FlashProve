-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/FastLaw/Sites.lean: at every lookup of a public part the two
fillings that are seated there agree at the run. Conditional on `Fit R` alone. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: Honest/K3/LotRow.lean seats, at a site s, the summands
`specJobsF s.shape s.p.lm s.p.first` (`specFill`) or `fastJobs s.at_.face (rowOfFace s.at_.face)`
(`fastFill`).

What is shown.
  `siteAt_shape`: a site that `siteAt` (Honest/K3/Lot.lean) makes has the face of its shape, and its
    shape is the one that the verifier's own public parameters at the place fix.
  `sites_ok`: so, at every site of a public part, the face is the face of the site's shape, and the
    shape passes the library's test `FoNums.ok` (by `k3_shape_ok`,
    Johnson/Desc/First/Look/K3RoundsAt.lean).
  `site_agree`, the main theorem: at a course at such a site, with the summands of `specFill`, that
    passes `Fit`, the summands of `fastFill` agree with the course's at the run.

Hypotheses that remain, in `site_agree`.
  `hs`: s is a site of the public part Z (`lookSites Z`, Lot.lean).
  `ha`, `hJ`: the course stands at the site's place, and its summands are those of `specFill`.
  `F`: `Fit R`.

How the proof goes. `agreeAt_real` (Honest/K3/FastLaw/Lift.lean) takes as hypotheses that the
course's face is `faceOf h`, that its summands are the specification's at shape h, and the library's
test `FoNums.ok h`. An arbitrary value of the structure `Site` need not have its face made of its
shape. The sites of a public part are made by `siteAt`, and of these it holds.

Users. Honest/K3/Law/SpecAtSite.lean imports this file and calls `sites_ok`; `left_site_fast`
(Honest/K3/Law/AtSite.lean) calls `site_agree`. The first two statements stand, with the same
proofs, under other names, in Honest/K3/Law/SitesOk.lean (`site_made_shape`, `sites_shape_ok`).

Limits. `AgreeAt` is defined in Honest/K3/Law/Statements.lean: as read, at the run. What follows
from it (the same rounds; one filling lawful if the other is) is that file's statement `AgreeSame`,
which is not shown here; its second half is shown in `agreeLawful` (Honest/K3/Law/Agree.lean). No
statement of this file says that either filling is right. No instance of the hypotheses of
`site_agree` is exhibited in this file: it lays no course at a site of a public part.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.Lift
import Johnson.Desc.ProofFile.Honest.K3.LotRow
import Johnson.Desc.First.Look.K3RoundsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.FastLaw
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K3 (faceOf)
open ProofFile.Honest.K3.Law

theorem siteAt_shape (X : OnBytes.Model.Verify.Public) (ps : List Spot) (x : Nat × Bool × Place)
    (s : Site) (hs : siteAt X ps x = some s) :
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

theorem sites_ok (Z : Pub) : ∀ s ∈ lookSites Z,
    s.at_.face = faceOf s.shape ∧ FoNums.ok s.shape = true := by
  intro s hs
  unfold lookSites at hs
  obtain ⟨x, _, hx⟩ := List.mem_filterMap.1 hs
  obtain ⟨h1, h2⟩ := siteAt_shape _ _ x s hx
  exact ⟨h1, VerifiableInference.OnPublicFiles.k3_shape_ok h2⟩

/-- **Conditional on `Fit R`: at every lookup of a public part, the summands that fold tables agree,
at the run, with a course at that site whose summands are the specification's.** No instance of
these hypotheses is exhibited in this file: it lays no course at a site of a public part. -/
theorem site_agree {W₀ Rc Xi Tr : Type} (src : Sources W₀ Xi Tr) (Z : Pub) (s : Site)
    (hs : s ∈ lookSites Z) (R : Course Ask) (ha : R.a = s.at_)
    (hJ : R.J = ((specFill (Rc := Rc) src).jobs s).asked) (F : Fit R) :
    AgreeAt R ((fastFill (Rc := Rc) src).jobs s).asked := by
  obtain ⟨h1, h2⟩ := sites_ok Z s hs
  show AgreeAt R (fastJobs s.at_.face (Fast.rowOfFace s.at_.face)).asked
  rw [h1]
  exact agreeAt_real s.shape h2 s.p.lm s.p.first R (by rw [ha, h1]) hJ F

end ProofFile.Honest.K3.FastLaw

#print axioms ProofFile.Honest.K3.FastLaw.siteAt_shape
#print axioms ProofFile.Honest.K3.FastLaw.sites_ok
#print axioms ProofFile.Honest.K3.FastLaw.site_agree
