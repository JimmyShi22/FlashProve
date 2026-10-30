-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ClosedTurns.lean: WHAT THE STEP THAT CLOSES THE LIST OF TABLES AT A LAYERS' LINK
LEAVES (Johnson/Desc/K8/ReadsQuiet.lean: layers), in the words that cell_of_tie asks
(Johnson/Road/K4/CellOfTie.lean): three of its premises out of that step's accepting.

  `tabAt_of_sizes`: two structures of the approximate range proof (HTailF2) with one number of
    matrices and one list of matrices number the places alike.
  `closing_turns`: where the step accepts: the verifier's state stood in a layers' link a that held
    what K4 has heard (o); the state behind holds tl' with: tl'.funs = o.funs (hfun) · tl' numbers
    the places as the place's parameter P.tl does (half of htab) · tl' has P.tl's number of the
    reads (half of hu3); the link's other fields stay.
No new argument: layers_ok, closed_fields (Johnson/Desc/K8/ReadsQuietLaws.lean). Kin: the
approximate range proof's files have the structure behind written out (layers_lays_tl,
Johnson/Desc/First/K8/LawCondText.lean, not in the build on which this file was written): from
it the three should follow by unfolding: not typed.
Limits. THE OTHER HALVES ARE NOT HERE: that the state in front's copy (a.tl) numbers the places as
P.tl does, and that P.tl's number of the reads is K4's (o.v.iU3): both want "the place's parameter
is the public parameters' own", and the first also what the link's entry lays: by nobody. That the
step is seated behind the second sending's sub-protocol at a layers' link is not said. Met through
Lean at no member. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on
soundness.


-/
import Johnson.Desc.K8.ReadsQuietLaws
import OnBytes.Tie.Pv.Tail.EndsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K8.ReadsQuiet (PG layers layers_ok closed_fields)

/-- One number of matrices and one list of matrices: one numbering of places. -/
theorem tabAt_of_sizes {tl tl' : HTailF2} (hN : tl'.NM = tl.NM) (hm : tl'.mats = tl.mats)
    (Fn : HFun) (c sg : Nat) : tl'.tabAt Fn c sg = tl.tabAt Fn c sg := by
  unfold HTailF2.tabAt
  rw [hN, hm]

/-- **Where the step that closes the list at a layers' link accepts.** -/
theorem closing_turns {P : PG} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (layers P).decide s rs gs = .ok s') :
    ∃ a o tl', s.here = .lay a ∧ a.own = some o ∧
      s' = { s with here := .lay { a with tl := tl' } } ∧ tl'.funs = o.funs ∧
      (∀ Fn c sg, tl'.tabAt Fn c sg = P.tl.tabAt Fn c sg) ∧ u3Of tl' = u3Of P.tl := by
  obtain ⟨a, o, tl', ha, ho, hc, e⟩ := layers_ok h
  obtain ⟨_, f2, f3, f4, _, _, _, _, _, _, f11⟩ := closed_fields hc
  refine ⟨a, o, tl', ha, ho, e, f2, tabAt_of_sizes f3 f4, ?_⟩
  unfold u3Of
  rw [f11]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.tabAt_of_sizes
#print axioms OnBytes.Road.K4.closing_turns
