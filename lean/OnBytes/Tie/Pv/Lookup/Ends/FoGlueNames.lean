-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoGlueNames.lean.
Two facts on the verifier's public record, from the equation of `Verify.publicOf` alone: the number
of rounds over the channels in the head's last sumcheck; and that at a member of the record's list
of attention plans the written names of the three own parts, over the verifier's shape, are the
written names over the planner's numbers.

They are the two premises of `headRoad_names` and `attRoad_names`
(OnBytes/Tie/Pv/Lookup/Ends/FoDoorSecondAH.lean) and of `attLink_at`
(OnBytes/Tie/Pv/Lookup/Ends/FoLinkPairs.lean). OnBytes/Tie/Pv/Lookup/Ends/FoPublic.lean (`public_H`)
and OnBytes/Tie/Pv/Lookup/Ends/FoPublicA.lean (`public_A`) say from which plans the record's head
and its attention plans come.

Main names:
 * `planH2_lam`: a plan that `Head.planH2` returns has `lamS = h.lPd`.
 * `public_lam`: `X.H.lamS = X.hS.lPd`.
 * `public_attNames`: at `X.A[g]? = some a`: `scoresNames a.S ++ (divideNames a.S ++ attainNames
   a.S) = attOwnNames a.own`. By `att_names` (OnBytes/Tie/Pv/Tail/TakesAttProved.lean) at the plan
   from which a comes.
The first two are proved too as `glue_lam_H_plan` and `glue_lam_H`
(OnBytes/Tie/Pv/Tail/GlueHProved.lean [not in this library]); what `public_attNames` takes of
`public_A` as `glue_plan_A` (OnBytes/Tie/Pv/Tail/GlueAProved.lean [not in this library]).
Limits. Names and one number. Nothing on a run.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicA
import OnBytes.Tie.Pv.Tail.TakesAttProved

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model Fo.Pub
open OnBytes.Tie.Pv.Tail.TakesRows (scoresNames divideNames attainNames attOwnNames)

/-- A plan that `Head.planH2` returns has the shape's number of feature bits as `lamS`. -/
theorem planH2_lam {g : Settings} {h : Head.Shape} {L : Head.HL} {b : Head.Border}
    {O : Head.Owner} {NGr lkW : ℕ} {hp : Head.HPlanH2}
    (k : Head.planH2 g h L b O NGr lkW = .ok hp) : hp.lamS = h.lPd := by
  unfold Head.planH2 at k
  simp only [bind, Except.bind, pure, Except.pure] at k
  repeat' split at k
  all_goals first
    | (cases k; rfl)
    | cases k

/-- **The number of rounds over the channels in the head's last sumcheck.** -/
theorem public_lam {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) : X.H.lamS = X.hS.lPd := by
  obtain ⟨H0, h0, e⟩ := public_H h
  have a : H0.lamS = X.hS.lPd := planH2_lam h0
  have b : X.H.lamS = H0.lamS := by rw [e]
  exact b.trans a

/-- **At a member of the record's attention plans the written names over the verifier's shape are
the written names over the planner's numbers.** An equation of two written lists. -/
theorem public_attNames {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) {g : ℕ} {a : Attention.Plan}
    (hg : X.A[g]? = some a) :
    scoresNames a.S ++ (divideNames a.S ++ attainNames a.S) = attOwnNames a.own := by
  obtain ⟨_, _, cf, a0, _, _, _, m2, e, _, _⟩ := public_A h g a hg
  have e1 : a.S = a0.S := by rw [e]
  have e2 : a.own = a0.own := by rw [e]
  rw [e1, e2]
  exact OnBytes.Tie.Pv.Tail.TakesProved.att_names _ _ cf a0 m2

end Fo
