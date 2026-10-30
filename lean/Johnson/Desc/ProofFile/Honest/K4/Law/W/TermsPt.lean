-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/TermsPt.lean: CONDITIONAL.

Not shown here. THAT THE VERIFIER's HEARING HAS RETURNED (the library's LedG) AND THAT ITS TAPE HAS
SAMPLED WHAT THE CHALLENGES HOLD (DrawnIs): hypotheses; Law/PtsAtStand.lean has both at a state
behind the member's step. That the function which makes the second token sumcheck's job returns: a
hypothesis. That they can hold together: no example is known. By a walk of import lines the closure
holds seven modules under Johnson/RecCompile/ (Join, Wire, Pass, CmsGlue, CmsBcs, Cms, Bcs), through
Law/SaidKit.lean's imports; none under Johnson/Goal/ or Johnson/D/; under Johnson/RecCompile/ none
of the names Honest…, Both…, PassH…. Nothing on soundness, on completeness or on any other property.
No property is claimed.

The second token sumcheck's own challenges, laid as a point by the honest side's job (`jobTermsOn`,
Johnson/Desc/K4/Honest/Terms.lean), are the end point that the verifier holds (tT.r): by
`pointOf_default` (Johnson/Desc/K4/Honest/Law/Cube.lean), `led_rt` (Law/PtsHear.lean) and the
rounds' numbers (Law/Starts.lean).

  `jobTerms_cube`   the job's cube: its sizes fit; lt variables in the default order.
  `terms_point`   the point.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsAt
import Johnson.Desc.ProofFile.Honest.K4.Law.Starts
import Johnson.Desc.ProofFile.Honest.K4.Law.SaidKit
import Johnson.Desc.K4.Honest.Terms
import Johnson.Desc.K4.Honest.Law.Cube

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Model (Fork Level Tsc Forest.Heard orderDefault)
open OnBytes.Model.Layer (Own)
open OnBytes.K.Kc (Tape)
open OnBytes.Road.K4 (LedG)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw (pointOf_default)

/-- The cube of the second token sumcheck's job. CONDITIONAL: on the return. -/
theorem jobTerms_cube {S : OnBytes.Desc.First.K4.Honest.Sides} {J : Job}
    (h : jobTermsOn S = some J) :
    J.cube.fits = true ∧ J.cube.n = S.v.y.h.lt ∧ J.cube.order = orderDefault S.v.y.h.lt := by
  unfold jobTermsOn at h
  obtain ⟨rows, _, h⟩ := Option.bind_eq_some_iff.1 h
  dsimp only at h
  split at h
  · simp at h
  · rename_i hc
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true] at hc
    exact ⟨hc.1.1, rfl, rfl⟩

variable {Q : K4Pub} {tk : Array Nat} {t : Tape} {fo : Forest.Heard} {o : Own} {F G : Fork}
  {u : Tape} {H1 : OnBytes.Model.Layer.Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape} {ds : List Fmt.Drawn}

/-- **THE SECOND TOKEN SUMCHECK's CHALLENGES, LAID AS A POINT, ARE THE VERIFIER's END POINT.**
CONDITIONAL: on every hypothesis named. -/
theorem terms_point
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (hD : DrawnIs t ds) (hl : k4StartAt Q 3 ≤ ds.length)
    {S : OnBytes.Desc.First.K4.Honest.Sides} {J : Job}
    (hJ : jobTermsOn S = some J) (hy : S.v.y = Q.P.y) :
    ∀ tT', o.H.tT = some tT' →
      J.cube.pointOf (ownE ds (rJ3 Q.P Q.g + 1) Q.P.y.h.lt) = tT'.r := by
  intro tT' hT
  obtain rfl := Option.some.inj (L.kTT.symm.trans hT)
  obtain ⟨c1, c2, c3⟩ := jobTerms_cube hJ
  obtain ⟨_, _, e2, e3, _, _, _⟩ := k4StartAt_eq Q
  have hlen : (ownE ds (rJ3 Q.P Q.g + 1) Q.P.y.h.lt).length = Q.P.y.h.lt :=
    ownE_length ds _ _ (by rw [e3] at hl; unfold rJ4 at hl; omega)
  rw [pointOf_default J.cube c1 (by rw [c3, c2]) _ (by rw [hlen, c2, hy])]
  show _ = tT.r
  rw [led_rt L ds hD hl, e2]
  rfl

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.jobTerms_cube
#print axioms ProofFile.Honest.K4.W.terms_point
