-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/AtFull.lean: TEN PREMISES OF K10's LAW, ON THE GROUP AND ON THE
NUMBERS, MET TOGETHER AT A REAL GROUP OF THE FULL SIZE. Statements and proofs.

All that needs no text of the description stands in GroupFull.lean
(beside this file): the group, the written place, nine of the ten premises, the proved block's
condition. What stays needs `Pulls` (OrderedOf.lean), beneath which the closing's text stands.
  `full_pulls`: hP: at every list, group, oM, oZ and kp: by `pulls_keep` (PullsOf.lean) and
    `membPort_onto`.
  `full_together`: TEN PREMISES MET TOGETHER AT A VALUE: hFi, hg, hj, hc, he, hv, hP, hx, hxs, hxe:
    at each of the 26 written lists, at the first group in front (8 row variables), nothing kept,
    every member's rows behind those of the messages in front of it.
Limits. Those of GroupFull.lean: IT IS A MEMBER, NOT THE DESCRIPTION's OWN PLACE. The other premises
of K10's law are not treated. It rests on GroupRowsOnto.lean and MemberOnto.lean,
and through FoldPriced.lean on the files under ThirdParty/ (lean/LIMITS.md, L15). Nothing on
soundness of the protocol.

-/
import Johnson.Top.H.MemberOnto
import Johnson.Desc.First.Close.Law.PullsOf
import Johnson.Desc.First.Close.Law.GroupFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G Cb

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) (gs : GroupSize)
  (hgs : gs ∈ frontFull) (oM oZ : Fin lo.length → ℕ)
  (kp : {i // memMain lo i} → Prop) [DecidablePred kp]

/-- hP. -/
theorem full_pulls : Pulls (groupFull lo hlo gs hgs oM oZ kp)
    (pullOf (groupFull lo hlo gs hgs oM oZ kp)) :=
  pulls_keep (rowsAtFull lo hlo gs hgs 219 oM oZ) kp fun a =>
    membPort_onto codesFull2 (lo.get a.1).1 (lo.get a.1).2 (stageOf gs 219) (oM a.1) (oZ a.1)
      (hMFull lo hlo gs hgs 219 a.1 a.2) (hZFull lo hlo gs hgs 219 a.1 a.2)

end

/-- **TEN PREMISES OF K10's LAW, MET TOGETHER AT A VALUE**: at each of the 26 written lists, at the
first group in front (8 row variables), nothing kept, every member's rows behind those of the
messages in front of it. -/
theorem full_together (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) :
    (groupFull lo hlo (grpFull 8 16 false) front8 (pre fun i => (lo.get i).1.mainRows)
        (pre (maskOf lo)) fun _ => False).G.Fits ∧
      (groupFull lo hlo (grpFull 8 16 false) front8 (pre fun i => (lo.get i).1.mainRows)
        (pre (maskOf lo)) fun _ => False).Good ∧
      InJ (groupFull lo hlo (grpFull 8 16 false) front8 (pre fun i => (lo.get i).1.mainRows)
          (pre (maskOf lo)) fun _ => False).s
        (groupFull lo hlo (grpFull 8 16 false) front8 (pre fun i => (lo.get i).1.mainRows)
          (pre (maskOf lo)) fun _ => False).e ∧
      CountsAt (groupFull lo hlo (grpFull 8 16 false) front8 (pre fun i => (lo.get i).1.mainRows)
          (pre (maskOf lo)) fun _ => False).s
        (groupFull lo hlo (grpFull 8 16 false) front8 (pre fun i => (lo.get i).1.mainRows)
          (pre (maskOf lo)) fun _ => False).e (placeFull 8).bC (placeFull 8).bZ ∧
      (groupFull lo hlo (grpFull 8 16 false) front8 (pre fun i => (lo.get i).1.mainRows)
          (pre (maskOf lo)) fun _ => False).G.e <
        (groupFull lo hlo (grpFull 8 16 false) front8 (pre fun i => (lo.get i).1.mainRows)
          (pre (maskOf lo)) fun _ => False).s.d ∧
      (∀ a, ((groupFull lo hlo (grpFull 8 16 false) front8 (pre fun i => (lo.get i).1.mainRows)
          (pre (maskOf lo)) fun _ => False).view a).Fix
        (groupFull lo hlo (grpFull 8 16 false) front8 (pre fun i => (lo.get i).1.mainRows)
          (pre (maskOf lo)) fun _ => False).G.e) ∧
      Pulls (groupFull lo hlo (grpFull 8 16 false) front8 (pre fun i => (lo.get i).1.mainRows)
          (pre (maskOf lo)) fun _ => False)
        (pullOf (groupFull lo hlo (grpFull 8 16 false) front8
          (pre fun i => (lo.get i).1.mainRows) (pre (maskOf lo)) fun _ => False)) ∧
      (placeFull 8).Paid ∧
      (placeFull 8).s = (groupFull lo hlo (grpFull 8 16 false) front8
        (pre fun i => (lo.get i).1.mainRows) (pre (maskOf lo)) fun _ => False).s ∧
      (placeFull 8).e = (groupFull lo hlo (grpFull 8 16 false) front8
        (pre fun i => (lo.get i).1.mainRows) (pre (maskOf lo)) fun _ => False).e :=
  ⟨full_fits lo hlo _ front8 _ _ _,
    full_good_pre lo hlo _ front8
      (by rw [sum_get lo fun x => x.1.mainRows]; exact (linksFull_fit8 lo hlo).1)
      (by
        have h := (linksFull_fit8 lo hlo).2
        rw [← sum_get lo fun x => if x.1.mainRows ≠ 0 then x.1.maskRows else 0] at h
        exact h),
    full_inJ lo hlo _ front8 _ _ _, full_counts lo hlo _ front8 _ _ _,
    full_radius lo hlo _ front8 _ _ _, full_fix lo hlo _ front8 _ _ _,
    full_pulls lo hlo _ front8 _ _ _, placeFull_paid _ front8,
    full_stage lo hlo _ front8 _ _ _, full_radius_eq lo hlo _ front8 _ _ _⟩

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.full_pulls
#print axioms VerifiableInference.Desc.First.Close.full_together
