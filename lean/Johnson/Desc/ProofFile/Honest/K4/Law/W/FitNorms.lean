-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/FitNorms.lean: CONDITIONAL.

What is here. Two more of the fifteen clauses of the public test `k4MakersFit`
(Johnson/Desc/ProofFile/Honest/K4/Part.lean), as laws, at every input w: the list of the sums of
limb products has as many entries as the row states, at all sampled values, with no hypothesis
(`wSums_length`); the honest side's function for the squares' product layer returns, and what it
returns has the public shape of its call, at all sampled values p whose two points have the sizes
named (`squares_fit`), from the plan's nine public facts (`K4Plan`). The test on the squares' cube
follows Law/SumPaid.lean's jobSquares_returns, which stands at the sampled values of a list of
challenges.

  `wSums_length`   ledNS xl times NI entries.
  `squares_fit`   the squares' job.

Not shown here. K4Plan (ITS FIELD sw BARS EVERY SHAPE BUT THOSE WITH THE LIBRARY's ELEVEN SWITCHES);
the sizes of the two points: hypotheses of squares_fit. That the sampled values at the zero
challenges, at which k4MakersFit asks, have these sizes. The other clauses of k4MakersFit. What the
list and the job's table hold. By a walk of import lines the closure holds no module under
Johnson/RecCompile/, Johnson/Goal/ or Johnson/D/. Nothing on soundness, on completeness or on any
other property. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SumPaid
import Johnson.Road.K4.C.GatedNums
import Johnson.Road.FormsKeysFac

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes (E zeroE oneE)
open OnBytes.Model (HTailF2 ledNS orderDefault)
open OnBytes.Model.Layer (normsStart)
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw
open Inst.Model.FFSeg (Dim)

/-- A walk whose every step returns an array of n entries ends in one, from such an array. -/
theorem foldl_size_const {α : Type} {n : ℕ} (f : Array E → α → Array E)
    (hf : ∀ a x, (f a x).size = n) : ∀ (l : List α) (a : Array E), a.size = n →
    (l.foldl f a).size = n
  | [], _, h => h
  | x :: l, a, _ => foldl_size_const f hf l (f a x) (hf a x)

/-- **THE SUMS OF LIMB PRODUCTS ARE AS MANY AS THE ROW STATES.** -/
theorem wSums_length (Q : K4Pub) (w : K4In) (p : Pts) :
    (wSums Q w p).length = ledNS Q.P.y.h.xl * Q.P.y.NI := by
  unfold wSums
  dsimp only
  rw [OnBytes.Road.flatMap_length _ (ledNS Q.P.y.h.xl) _ fun i _ => ?_, List.length_range,
    Nat.mul_comm]
  rw [Array.length_toList]
  exact foldl_size_const _ (fun _ _ => by rw [Array.size_map, Array.size_range]) _ _
    (by rw [Array.size_replicate])

variable {Q : K4Pub} {hS : OnBytes.Model.Layer.Shape} {pc : List (List String)} {tl : HTailF2}
  {D : Dim}

/-- **THE SQUARES' JOB IS MADE AND HAS ITS CALL's SHAPE.** CONDITIONAL: on A and the two sizes. -/
theorem squares_fit (A : K4Plan hS pc Q.P Q.g tl D) (w : K4In) (p : Pts)
    (hI : p.rhoI.size = Q.P.rd.lNI) (hV : p.PV.size = Q.P.y.h.lt) :
    ∃ j, jobSquares Q w p = some j ∧ k4JobFits (k4LevelShape Q.P.rd.muV) j = true := by
  have hmu := (_root_.Fo.readsOf_mu A.reads).1
  have hfit : (sqJobOf Q.P.rd.muV (normsStart Q.P.y 0 p.gp p.rhoI p.PV).2
      (squaresTab Q w p.gp)).cube.fits = true := by
    refine fits_of _ ?_ ?_ ?_ ?_ ?_
    · show (orderDefault Q.P.rd.muV).length = Q.P.rd.muV
      simp [orderDefault]
    · intro v hv
      show v ∈ orderDefault Q.P.rd.muV
      simpa [orderDefault] using hv
    · intro t ht
      have ht' : t ∈ [squaresTab Q w p.gp] := ht
      rw [List.mem_singleton] at ht'
      rw [ht']
      show (squaresTab Q w p.gp).size = 2 ^ Q.P.rd.muV
      simp [squaresTab]
    · intro x hx
      have hx' : x ∈ [((oneE, 0, 0) : E × ℕ × ℕ)] := hx
      rw [List.mem_singleton] at hx'
      rw [hx']
      exact ⟨by show 0 < 1; norm_num, by show 0 < 1; norm_num⟩
    · intro r hr
      have h' : Way.point (normsStart Q.P.y 0 p.gp p.rhoI p.PV).2 = Way.point r := hr
      rw [← Way.point.inj h']
      show (p.rhoI ++ Array.replicate Q.P.y.lPd _ ++ p.PV).size = Q.P.rd.muV
      rw [Array.size_append, Array.size_append, Array.size_replicate, hI, hV, hmu]
  exact ⟨_, by rw [jobSquares_eq, if_pos hfit], sqJob_jobFits _ _ _ hfit⟩

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.foldl_size_const
#print axioms ProofFile.Honest.K4.W.wSums_length
#print axioms ProofFile.Honest.K4.W.squares_fit
