-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/FastLaw/PartsKey.lean: AT A KEY FILE'S LOOKUP the summands that
fold tables agree, at the run, with the specification's at parts, and are lawful where these are.
CONDITIONAL. Theorems; no definition.

The matter. Honest/K3/Parts/KeyFace.lean and KeyAt.lean lay the face of a key file's lookup
(`faceK`), its table's rows (`rowK`), its padding by rows (`padsK`), tie the face's public factor
and table to the specification's, and conclude `Lawful` for the specification's summands
(`lawful_key`). This file adds the folding side at the same terms:
`fastJobs (faceK id m l) (rowK id m l)`.

  `factorFits_key`    the premise on the public factor (Honest/K3/FastLaw/Tie.lean) holds at such a
                      face
  `agreeAt_key`       `AgreeAt`: no premise on keys or bits
  `lawful_key_fast`   under `lawful_key`'s own premises the folding summands are lawful, at the same
                      values of planes and keys

THE PREMISES. Of `agreeAt_key`: the course's face is `faceK id m l`; its summands are the
specification's at parts there; `Fit R`; an acceptance by the public test `okK` (d at most 64; the
padding's rows below 2 ^ d). Of `lawful_key_fast` besides: the input yields one structure at all the
stages' fronts; THE RELATION AFTER THE CHALLENGE AT PARTS at that structure.

Limits. NO COURSE IS SHOWN THAT MEETS THE PREMISES: a part of a key file's lookup has 2 ^ 36 or 2 ^
35 keys; nothing can be evaluated there. The public premises have members at both lookups of the key
file at full size: the guard lines of Honest/K3/Parts/KeyAt.lean. At small faces of the same form
the equations between the two fillings are evaluated in Honest/K3/FastLaw/PartsGuards.lean
[not in this library].
Nothing on any property of the protocol.

-/
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.PartsLift
import Johnson.Desc.ProofFile.Honest.K3.Parts.KeyAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.FastLaw
open OnBytes (E okE)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Parts (specJobsPAt dataP keysOfP)
open ProofFile.Honest.K3.Parts.Key (faceK rowK padsK numsK okK okK_spec factor_key lawful_key)

/-- **CONDITIONAL ON an acceptance by `okK` and on the shift's words being below the prime: at a key
file's lookup the face's public factor is the library's at the table's rows and the padding by
rows.** Members of `okK`: Honest/K3/Parts/KeyAt.lean. -/
theorem factorFits_key (id : Nat) (m : OnBytes.Wf.Matrix) (l : OnBytes.Params.WfLookup) (p : Pts)
    (hk : okK id m l = true) (ht : okE p.theta = true) :
    FactorFits (faceK id m l) (rowK id m l) (padsK id m l) p := by
  obtain ⟨hd, hp⟩ := okK_spec hk
  have e : up ((faceK id m l).factor p.theta p.alpha) =
      Cb.Lkp.padFac (fun u => up (rowK id m l (down (up p.theta)) u)) (padsK id m l)
        (up p.alpha) := factor_key id m l p.theta p.alpha hd hp
  rw [down_up _ ht] at e
  exact e

/-- **CONDITIONAL ON `Fit R` and an acceptance by `okK`: at a course that stands at a key file's
lookup with the specification's summands at parts, the summands that fold tables agree at the run.**
NO COURSE is shown that meets the premises. -/
theorem agreeAt_key (R : Course Ask) (id : Nat) (m : OnBytes.Wf.Matrix)
    (l : OnBytes.Params.WfLookup) (hf : R.f = faceK id m l)
    (hJ : R.J = (specJobsPAt (faceK id m l) (rowK id m l) (padsK id m l)).asked) (hF : Fit R)
    (hk : okK id m l = true) : AgreeAt R (fastJobs (faceK id m l) (rowK id m l)).asked := by
  have A : FactorFits R.f (rowK id m l) (padsK id m l)
      (ptsOf R.f R.a.base (R.front (.tie 0)).heard) := by
    have h := factorFits_key id m l (ptsOf R.f R.a.base (R.front (.tie 0)).heard) hk
      (theta_ok R hF (.tie 0))
    rw [← hf] at h
    exact h
  have h := agreeAt_parts R (rowK id m l) (padsK id m l) (by rw [hJ, hf]) hF A
  rw [hf] at h
  exact h

/-- **CONDITIONAL ON `Fit R`, an acceptance by `okK`, one structure at all the stages' fronts, AND
THE RELATION AFTER THE CHALLENGE AT PARTS: at a key file's lookup the course with the summands that
fold tables in the specification's place is lawful**, at the values of planes and keys of
`lawful_key`. NO COURSE is shown that meets the premises. -/
theorem lawful_key_fast (R : Course Ask) (id : Nat) (m : OnBytes.Wf.Matrix)
    (l : OnBytes.Params.WfLookup) (w : Hidden) (hf : R.f = faceK id m l)
    (hJ : R.J = (specJobsPAt (faceK id m l) (rowK id m l) (padsK id m l)).asked) (hF : Fit R)
    (hk : okK id m l = true) (hone : ∀ s ∈ stages R.f, R.t.input (R.front s).heard = w)
    (hM : (dataP (numsK id m l) R.f.parts R.f.orders w R.pts).Mid) :
    Lawful { R with J := (fastJobs (faceK id m l) (rowK id m l)).asked }
      (Spec.planesOf (dataAt (numsK id m l) w R.pts))
      (keysOfP (dataP (numsK id m l) R.f.parts R.f.orders w R.pts)) :=
  (agreeLawful Ask R _ _ _ hF (agreeAt_key R id m l hf hJ hF hk)).2
    (lawful_key R id m l w hf hJ hF hk hone hM)

end ProofFile.Honest.K3.FastLaw

#print axioms ProofFile.Honest.K3.FastLaw.factorFits_key
#print axioms ProofFile.Honest.K3.FastLaw.agreeAt_key
#print axioms ProofFile.Honest.K3.FastLaw.lawful_key_fast
