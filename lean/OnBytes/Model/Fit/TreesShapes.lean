-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Fit/TreesShapes.lean: what the verifier program hands to the planner has all oracle
messages of its links in the class of leaves 0.

The program makes the links from the declared arrays and the layout file (Plan.reqFrame), gives the
last link one plain scalar (withReply) and lays them into the record that the planner takes
(subproofsWith, OnBytes/Model/VerifySubproofs.lean).

Main names.
  withReply_class: withReply keeps TreeClassCap (OnBytes/Params/Fit/TreesSized.lean).
  subproofsWith_class: the links of subproofsWith X rl have TreeClassCap, if rl is what reqFrame
    returned.

What this file does not claim. That the record which the program hands to the planner is
subproofsWith X rl at such an rl.

The program does not import this file.


-/
import OnBytes.Model.VerifySubproofs
import OnBytes.Params.Fit.TreesFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Model.Verify
open OnBytes.Params

/-- The last link's plain scalar changes no oracle message. -/
theorem withReply_class :
    ∀ {links : List ReqLink}, TreeClassCap links → TreeClassCap (withReply links)
  | [], _ => fun _ h => absurd h List.not_mem_nil
  | [l], h => fun L hL m hm => by
    have e : L = { l with plain := 1 } := List.mem_singleton.1 hL
    rw [e] at hm
    exact h l List.mem_cons_self m hm
  | l :: k :: ls, h => fun L hL m hm => by
    have hL' : L ∈ l :: withReply (k :: ls) := hL
    rcases List.mem_cons.1 hL' with e | q
    · rw [e] at hm
      exact h l List.mem_cons_self m hm
    · exact withReply_class (links := k :: ls)
        (fun L' hL'' => h L' (List.mem_cons_of_mem _ hL'')) L q m hm

/-- **The links of subproofsWith X rl lie in the class 0, where rl is what reqFrame returned.** -/
theorem subproofsWith_class (X : Public) {declared : Array Stages.FrameLink}
    {file : Plan.LayoutLines} {answers : Nat} {rl : List ReqLink} {layout : ReqLayout}
    (h : Plan.reqFrame declared file answers = some (rl, layout)) :
    TreeClassCap (subproofsWith X rl).links :=
  withReply_class (reqFrame_class h)

end OnBytes.Model.Verify
