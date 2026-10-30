-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Fit/FitLinks.lean: the planning of the rounds of every sub-proof of the model
(Verify.linkRounds, OnBytes/Model/VerifySubproofs.lean) keeps the property Small of entries
(OnBytes/Params/Fit/FitCalc.lean), wherever the public part was made by the program's own reader.

Main names:
  link_keeps: from Verify.publicOf pol KL lay = .ok X and SetCap s: Keeps s Small (linkRounds X link
    moment), for every number of a link and every moment: the head's arm (HeadCaps.lean), the
    layers' (LayerCaps.lean), attention's (AttKeeps.lean), all in this folder; for a number that
    names no link the routine refuses.
  sub_keeps: so what the frame asks of the sub-proofs (SubKeeps, OnBytes/Params/Fit/FitPlans.lean)
    holds of a record whose plan is linkRounds X and which sends nothing behind the links.
Limits: nothing where publicOf refuses. SetCap s is a premise.
The program does not import this file.

-/
import OnBytes.Model.Fit.HeadCaps
import OnBytes.Model.Fit.LayerCaps
import OnBytes.Model.Fit.AttKeeps
import OnBytes.Params.Fit.FitPlans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Model.Verify

open OnBytes.Params (Keeps Small SetCap SubKeeps)

section
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Public} {s : Params.Setting}

theorem link_keeps (hX : publicOf pol KL lay = .ok X) (S : SetCap s) (link moment : Nat) :
    Keeps s Small (linkRounds X link moment) := by
  unfold linkRounds
  dsimp only
  refine Params.keeps_ite (fun _ => head_keeps hX S moment) fun _ => ?_
  refine Params.keeps_ite (fun _ => ?_) fun _ => Fit.link_att_keeps hX S _ moment
  split
  · rename_i hp hg
    exact Fit.layers_keeps (Params.subBase_small S) hX _ hp hg moment
  · exact (Params.keeps_needs _ _).any

theorem sub_keeps (hX : publicOf pol KL lay = .ok X) (S : SetCap s) {sub : Params.Subproofs}
    (h1 : sub.plan = linkRounds X) (h2 : sub.afterLinks = pure ()) : SubKeeps s sub where
  plan := fun l m => by
    rw [h1]
    exact link_keeps hX S l m
  after := by
    rw [h2]
    exact Params.keeps_pure trivial

end

end OnBytes.Model.Verify

#print axioms OnBytes.Model.Verify.link_keeps
#print axioms OnBytes.Model.Verify.sub_keeps
