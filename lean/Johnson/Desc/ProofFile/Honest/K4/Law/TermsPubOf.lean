-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TermsPubOf.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side, the second token
sumcheck: the eight public premises `TermsPub` (Law/TermsAll.lean) from the plan's public facts,
the layout of the weights and the return of Sides.of: seven clauses from
Johnson/Road/K4/C/TermsPubKit.lean, the public test triPlainB (Law/TripsWhole.lean) from
Johnson/Road/K4/C/TriPlain.lean. Statements and proofs.

  `triPlainB_of_lay`     the public test answers true.
  **`termsPub_of_plan`**   TermsPub.

Not shown here. That a plan with the public facts K4Plan exists, or that the honest side's function
Sides.of returns anywhere: no example is known. K4Plan can hold only at shapes with routed experts,
under the library's eleven switches (its field sw). THAT THE LAYOUT OF THE WEIGHTS IS ONE THAT THE
VERIFIER's FUNCTION wsLayOf RETURNS, for a model with mixtures of experts (hws), is a hypothesis
beside K4Plan, which says nothing of that layout. Nothing on soundness, on completeness or on any
other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TermsAll
import Johnson.Road.K4.C.TermsPubKit
import Johnson.Road.K4.C.TriPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Model (WsShape wsLayOf HTailF2)
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Road.K4.C (sides_seven tri_cd)
open Inst.Model.FFSeg (Dim)
open OnBytes.Desc.First.K4.Honest

variable {Q : K4Pub} {w : K4In} {p : Pts} {S : OnBytes.Desc.First.K4.Honest.Sides}

/-- **The public test answers true** at a layout of the weights that wsLayOf returns. CONDITIONAL:
on hws and h. -/
theorem triPlainB_of_lay {s : WsShape} {lk : ℕ} (hws : wsLayOf s true lk = .ok Q.P.wsLay)
    (h : OnBytes.Desc.First.K4.Honest.Sides.of Q w p = some S) : triPlainB S = true := by
  unfold triPlainB
  cases hx : S.panels #[] with
  | none => rfl
  | some x =>
    show (x.1.all fun b =>
      !(b.tri && b.claim == 1) || b.v0.all fun v0 => (S.opens.getD v0 {}).cd == 0) = true
    rw [← Array.all_toList, List.all_eq_true]
    intro b hb
    cases ht : b.tri with
    | false => rfl
    | true =>
      cases h0 : b.v0 with
      | none => simp
      | some v0 =>
        have e := tri_cd hws h hx b hb ht v0 h0
        show (!(true && b.claim == 1) || ((S.opens.getD v0 {}).cd == 0)) = true
        rw [e]
        exact Bool.or_true _

/-- **THE EIGHT PUBLIC PREMISES ON WHAT THE TWO JOBS SHARE, FROM THE PLAN.** CONDITIONAL: on A, hws
and h. -/
theorem termsPub_of_plan {hS : OnBytes.Model.Layer.Shape} {pc : List (List String)} {tl : HTailF2}
    {D : Dim} (A : K4Plan hS pc Q.P Q.g tl D) {s : WsShape} {lk : ℕ}
    (hws : wsLayOf s true lk = .ok Q.P.wsLay)
    (h : OnBytes.Desc.First.K4.Honest.Sides.of Q w p = some S) : TermsPub S := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := sides_seven A h
  exact ⟨c1, c2, c3, c4, c5, c6, c7, triPlainB_of_lay hws h⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.triPlainB_of_lay
#print axioms ProofFile.Honest.K4.termsPub_of_plan
