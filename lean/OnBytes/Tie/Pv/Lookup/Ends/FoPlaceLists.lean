-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPlaceLists.lean.
At the place of each link: the list of rounds that the plan of the chain lays there begins with the
rounds of the lookup at the door's own record.

The plan of a chain's rounds tells the kinds of links apart by three tests on the number of the
place (`linkList`). `TwLaw.link_layer0` … `TwLaw.link_head2`
(OnBytes/Tie/Pv/Lookup/Peel/FoPlanAt.lean) say, under these tests, that the list at a link's moments
0 and 2 begins with the rounds of a lookup of the size of a record of the plan.
OnBytes/Tie/Pv/Lookup/Ends/FoPlaceNumber.lean
names the place of each link of the chain that the verifier runs and decides the tests there. Here
the two are joined. Write step for `if X.p4 then 2 else 1`.

 * `list_layer0`, `list_layer2`: at place step · g, for a group g with the plan hp: the lists begin
   with the rounds of a lookup of the size of `X.y.fo`, of `hp.tl.f9`.
 * `list_att0`, `list_att2`: if the proof covers attention, at place 2 · g + 1, with the plan a: of
   the size of `a.fs`, of `a.seam.tl.f9`.
 * `list_head0`, `list_head2`: at place step · NGr: of the size of `X.HLy.fs`, of `X.H.tl.f9`.

That these six records are those at which the doors of the lookups stand, and these three numbers
those of the places at which the verifier runs the links, is not said in this file:
OnBytes/Tie/Pv/Lookup/Ends/FoZeroLists.lean lays doors, places and lists on one set of witnesses.
`linkList` is the written list of OnBytes/Model/LinkRoundsList.lean: that the planner's routine adds
its rounds is said there (`runs_linkRounds`); that the plan on which the verifier runs is made of it
is not said here. X is any record, not only one that the verifier makes of the public files.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaceNumber
import OnBytes.Tie.Pv.Lookup.Peel.FoPlanAt

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Params OnBytes.Plan TwPlan TwErr TwRound Cb.Fo
open OnBytes.Model OnBytes.Model.Verify

section
variable (s : Setting) (c : Scope) (X : Public)

theorem list_layer0 (g : Nat) (hp : Layer.HPlan2) (hN : g < X.NGr) (hg : X.G[g]? = some hp) :
    linkList s c X ((if X.p4 then 2 else 1) * g) 0 = forestList s (forestSize X.y.fo) ++
      layerOwnList s (layerNumbers X.layers hp g) := by
  obtain ⟨t1, t2, t3⟩ := layer_tests X g hN
  have e := TwLaw.link_layer0 s c X ((if X.p4 then 2 else 1) * g) hp t1 t2 (by rw [t3]; exact hg)
  rw [t3] at e
  exact e

theorem list_layer2 (g : Nat) (hp : Layer.HPlan2) (hN : g < X.NGr) (hg : X.G[g]? = some hp) :
    linkList s c X ((if X.p4 then 2 else 1) * g) 2 = forestList s (forestSize hp.tl.f9) ++
      [batSigmaFrom s hp.nBatched 0] := by
  obtain ⟨t1, t2, t3⟩ := layer_tests X g hN
  exact TwLaw.link_layer2 s c X ((if X.p4 then 2 else 1) * g) hp t1 t2 (by rw [t3]; exact hg)

theorem list_att0 (h4 : X.p4 = true) (g : Nat) (a : Attention.Plan) (ha : X.A[g]? = some a) :
    linkList s c X (2 * g + 1) 0 = forestList s (forestSize a.fs) ++ attentionOwnList s a.own := by
  obtain ⟨t1, t2, t3⟩ := att_tests X h4 g
  exact TwLaw.link_attention0 s c X (2 * g + 1) a t1 t2 (by rw [t3]; exact ha)

theorem list_att2 (h4 : X.p4 = true) (g : Nat) (a : Attention.Plan) (ha : X.A[g]? = some a) :
    linkList s c X (2 * g + 1) 2 = forestList s (forestSize a.seam.tl.f9) ++
      [batSigmaFrom s a.own.rows 0] := by
  obtain ⟨t1, t2, t3⟩ := att_tests X h4 g
  exact TwLaw.link_attention2 s c X (2 * g + 1) a t1 t2 (by rw [t3]; exact ha)

theorem list_head0 :
    linkList s c X ((if X.p4 then 2 else 1) * X.NGr) 0 = forestList s (forestSize X.HLy.fs) ++
      headOwnList s (X.H.own X.hS) :=
  TwLaw.link_head0 s c X _ (beq_self_eq_true _)

theorem list_head2 :
    linkList s c X ((if X.p4 then 2 else 1) * X.NGr) 2 = forestList s (forestSize X.H.tl.f9) ++
      headEndList s (X.H.own X.hS) :=
  TwLaw.link_head2 s c X _ (beq_self_eq_true _)

end
end Fo
