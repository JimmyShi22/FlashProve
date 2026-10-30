-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/FastLaw/PartsLift.lean: at any number of parts of keys: the
summands that fold tables agree, at the run, with a course whose summands are the specification's at
parts; and they are lawful where these are. CONDITIONAL. Theorems; no definition.

The matter. Honest/K3/FastLaw/PartsAll.lean (`stages_agreeP`) speaks of an input, points and lists
of challenges as letters, under four premises. At a run that passes `Fit`
(Honest/K3/Law/Statements.lean) three of the four are paid here: the verifier's own tests on the
face give the parts' sizes, the planes' bounds and every order (Honest/K3/Parts/Course.lean);
challenges that the rounds can sample give the shift's words; the points that `ptsOf` lays have
their sizes (Honest/K3/FastLaw/Lift.lean; Honest/K3/Law/SpecCourse.lean). THE FOURTH STAYS: the
face's public factor is the library's at the table's rows and the padding by rows (`FactorFits`),
asked at the points in front of the tie's first step, where alone it is spent; `SpecAtP` and
`NumberedP` pay it too (`factor_of_spec`), so the second theorem does not ask it.

  `sizedP_of_fit`, `ptsSizedP`   the premises paid
  `agreeAt_parts`              `AgreeAt` at such a course
  `factor_of_spec`             the fourth premise out of `SpecAtP` and `NumberedP`
  `lawful_parts_fast`          with Honest/K3/Law/Agree.lean (`agreeLawful`) and
                               Honest/K3/Parts/Proof.lean (`lawfulSpecP`): the folding summands are
                               lawful at parts

Limits. The member lies in Honest/K3/FastLaw/PartsMember.lean [not in this library]: one synthetic
course at three parts, by evaluation. Nothing at the key file's own faces.
Nothing on any property of the protocol.

-/
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.PartsAll
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.Lift
import Johnson.Desc.ProofFile.Honest.K3.Parts.Proof
import Johnson.Desc.ProofFile.Honest.K3.Law.Agree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.FastLaw
open OnBytes (E)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Parts (specJobsPAt specJobsP dataP NumberedP SpecAtP keysOfP lawfulSpecP
  perm_of_okP facts_of_ok)

/-- **CONDITIONAL ON `Fit R`: the premise on numbers and points holds at the points in front of
every stage.** Members of `Fit`: Honest/K3/Law/Members.lean; at three parts
Honest/K3/Parts/Member.lean. -/
theorem sizedP_of_fit {W : Type} (R : Course W) (F : Fit R) (s : Stage) :
    SizedP R.f (ptsOf R.f R.a.base (R.front s).heard) := by
  exact ⟨(facts_of_ok F.ok).1, two_le_planes_of_ok R.f F.ok, (facts_of_ok F.ok).2.2,
    theta_ok R F s⟩

/-- The points that `ptsOf` lays have their sizes, at every part. -/
theorem ptsSizedP (f : LFace) (base : Nat) (heard : List Fmt.Drawn) :
    PtsSizedP f (ptsOf f base heard) :=
  ⟨fun y _ m _ => Spec.size_keyPt f base heard y.2 m, fun l _ => Spec.size_tabPt f base heard l,
    Spec.size_zeroPt f base heard⟩

/-- **CONDITIONAL ON `Fit R` and on `FactorFits` at the points in front of the tie's first step: at
a course whose summands are the specification's at parts, at numbers made of its own face, the
summands that fold tables agree at the run.** Member: Honest/K3/FastLaw/PartsMember.lean
[not in this library]. -/
theorem agreeAt_parts (R : Course Ask) (row : E → Nat → E) (pads : List (Nat × Nat))
    (hJ : R.J = (specJobsPAt R.f row pads).asked) (F : Fit R)
    (A : FactorFits R.f row pads (ptsOf R.f R.a.base (R.front (.tie 0)).heard)) :
    AgreeAt R (fastJobs R.f row).asked := by
  refine agreeAt_of R _ _ hJ F fun s hs k hk w => ?_
  obtain ⟨a1, a2⟩ := stage_agreeP R.f row pads w _ (sizedP_of_fit R F s)
    (ptsSizedP R.f R.a.base _) (fun y hy m hm => perm_of_okP F.ok hy hm) s hs
    (fun e => by subst e; exact A) k hk
  exact ⟨fun rs hl => (a1 rs hl).symm, fun rs mk hl =>
    ⟨((a2 rs mk hl).1).symm, ((a2 rs mk hl).2).symm⟩⟩

/-- **CONDITIONAL ON `Fit R`, `NumberedP R` and `SpecAtP R (numsOf R.f row pads) w`: the premise on
the public factor holds at the points in front of the tie's first step**: there the shift and alpha
are the run's, and `SpecAtP` has the factor at the run's. Member:
Honest/K3/FastLaw/PartsMember.lean [not in this library]. -/
theorem factor_of_spec (R : Course Ask) (row : E → Nat → E) (pads : List (Nat × Nat)) (w : Hidden)
    (F : Fit R) (hW : NumberedP R) (hS : SpecAtP R (numsOf R.f row pads) w) :
    FactorFits R.f row pads (ptsOf R.f R.a.base (R.front (.tie 0)).heard) := by
  have hs0 : Stage.tie 0 ∈ stages R.f := Parts.mem_tie0 hS
  obtain ⟨h1, h2⟩ : _ ∧ _ := hW.same _ hs0
  have ht := theta_ok R F (.tie 0)
  unfold FactorFits
  rw [h1] at ht ⊢
  rw [h2]
  have e : up R.factor = Cb.Lkp.padFac (fun u => up (row (down (up R.pts.theta)) u)) pads
      (up R.pts.alpha) := hS.factor
  rw [down_up _ ht] at e
  exact e

/-- **CONDITIONAL ON `Fit R`, `NumberedP R` and `SpecAtP R (numsOf R.f row pads) w`: at any number
of parts the course with the summands that fold tables in the specification's place is lawful**, at
the planes' values of the structure's own bits and the extension of each part's own keys. Member:
Honest/K3/FastLaw/PartsMember.lean [not in this library]. -/
theorem lawful_parts_fast (R : Course Ask) (row : E → Nat → E) (pads : List (Nat × Nat))
    (w : Hidden) (F : Fit R) (hW : NumberedP R) (hS : SpecAtP R (numsOf R.f row pads) w) :
    Lawful { R with J := (fastJobs R.f row).asked }
      (Spec.planesOf (dataAt (numsOf R.f row pads) w R.pts))
      (keysOfP (dataP (numsOf R.f row pads) R.f.parts R.f.orders w R.pts)) :=
  (agreeLawful Ask R _ _ _ F
    (agreeAt_parts R row pads hS.J F (factor_of_spec R row pads w F hW hS))).2
    (lawfulSpecP Unit _ w R F hW hS)

end ProofFile.Honest.K3.FastLaw

#print axioms ProofFile.Honest.K3.FastLaw.sizedP_of_fit
#print axioms ProofFile.Honest.K3.FastLaw.ptsSizedP
#print axioms ProofFile.Honest.K3.FastLaw.agreeAt_parts
#print axioms ProofFile.Honest.K3.FastLaw.factor_of_spec
#print axioms ProofFile.Honest.K3.FastLaw.lawful_parts_fast
