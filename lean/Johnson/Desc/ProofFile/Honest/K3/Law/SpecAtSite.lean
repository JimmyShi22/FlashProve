-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/SpecAtSite.lean: at every lookup of a public part the
specification's summands are lawful. Conditional on `Fit R`, an input that has settled, and the
relation after the challenge at the structure's keys and bits. Theorems.

Terms. Honest/K3/GLOSSARY.md ("course", "fit", "lawful", "relation after the challenge", "settled").

What is shown, at a course that stands at a site of a public part with the summands that
Honest/K3/LotRow.lean seats there (`specFill`).
  `specAt_site`: `SpecAt` (Honest/K3/Law/SpecLawful.lean) holds of the course.
  `lawful_site`: `Lawful` holds of it, at the planes' values of the structure's own bits and the
    extension of the structure's own keys.

Hypotheses that remain.
  `hs`, `ha`, `hJ`: s is a site of the public part Z (`lookSites Z`, Honest/K3/Lot.lean); the course
    stands at its place; its summands are those of `specFill`.
  `hF`: `Fit R`.
  `hS`: the input has settled (`Ask.Settled` at the place's number of rounds in front: it no longer
    moves from the challenges in front of the lookup on). `askOf_settled` (Honest/K3/WitLaw.lean)
    shows it at the rows' own input, under a hypothesis of its own on the lookups on the digits.
  `hM`: the relation after the challenge (`Data.Mid`) at the structure that the input yields. It is
    what the statements on a trace conclude; the way to it from `LookIn.Meets` is `mid_of_meets`
    (Honest/K3/Law/MeetsMid.lean), conditional on the library's test on the shape.

How the proof goes. Honest/K3/Law/SpecReal.lean (`specAt_real`, `lawful_real`) speaks of a shape h
under the library's test `FoNums.ok h`, of a course whose face is `faceOf h`, and assumes
`Numbered R`. At a site of a public part the test and the face are no hypotheses (`sites_ok`,
Honest/K3/FastLaw/Sites.lean), and `Numbered R` follows from `Fit R` (`numbered_of_fit`,
Honest/K3/Law/NumberedOfFit.lean). This file puts the three together.

Users. `left_site_spec` and `left_site_fast` (Honest/K3/Law/AtSite.lean) call `lawful_site`.

Limits. No instance of these hypotheses is exhibited in this file: it lays no course at a site of a
public part.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecReal
import Johnson.Desc.ProofFile.Honest.K3.Law.NumberedOfFit
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.Sites

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Spec
open VerifiableInference.Desc.K3 (faceOf)

variable {W₀ Rc Xi Tr : Type}

/-- **Conditional on `Fit R`, an input that no longer moves from the challenges in front of the
lookup on, and the relation after the challenge at the structure's keys and bits: `SpecAt` at a
course that stands at a lookup of a public part with the summands that are seated there.** No
instance of these hypotheses is exhibited in this file. -/
theorem specAt_site (src : Sources W₀ Xi Tr) (Z : Pub) (s : Site) (hs : s ∈ lookSites Z)
    (R : Course Ask) (ha : R.a = s.at_) (hJ : R.J = ((specFill (Rc := Rc) src).jobs s).asked)
    (hF : Fit R) (hS : Ask.Settled R.a.base R.t.input)
    (hM : (dataAt (fun theta => _root_.Fo.numsF s.shape s.p.lm s.p.first theta)
      (R.t.input R.t.heard) R.pts).Mid) :
    SpecAt R (fun theta => _root_.Fo.numsF s.shape s.p.lm s.p.first theta)
      (R.t.input R.t.heard) := by
  obtain ⟨h1, h2⟩ := FastLaw.sites_ok Z s hs
  exact specAt_real R s.shape s.p.lm s.p.first
    (by show R.a.face = _; rw [ha, h1]) hJ hF h2 hS hM

/-- **Conditional on the same three: at every lookup of a public part the specification's summands
are lawful**, at the planes' values of the structure's own bits and the extension of the structure's
own keys. No instance of these hypotheses is exhibited in this file. -/
theorem lawful_site (src : Sources W₀ Xi Tr) (Z : Pub) (s : Site) (hs : s ∈ lookSites Z)
    (R : Course Ask) (ha : R.a = s.at_) (hJ : R.J = ((specFill (Rc := Rc) src).jobs s).asked)
    (hF : Fit R) (hS : Ask.Settled R.a.base R.t.input)
    (hM : (dataAt (fun theta => _root_.Fo.numsF s.shape s.p.lm s.p.first theta)
      (R.t.input R.t.heard) R.pts).Mid) :
    Lawful R
      (planesOf (dataAt (fun theta => _root_.Fo.numsF s.shape s.p.lm s.p.first theta)
        (R.t.input R.t.heard) R.pts))
      (keysOf (dataAt (fun theta => _root_.Fo.numsF s.shape s.p.lm s.p.first theta)
        (R.t.input R.t.heard) R.pts)) := by
  obtain ⟨h1, _⟩ := FastLaw.sites_ok Z s hs
  have hp : R.f.parts = [s.shape.v] := by
    show R.a.face.parts = _
    rw [ha, h1]
    rfl
  exact lawfulSpec _ _ _ R hF (numbered_of_fit R s.shape.v hp hF)
    (specAt_site src Z s hs R ha hJ hF hS hM)

#print axioms ProofFile.Honest.K3.Law.Spec.specAt_site
#print axioms ProofFile.Honest.K3.Law.Spec.lawful_site

end ProofFile.Honest.K3.Law.Spec
