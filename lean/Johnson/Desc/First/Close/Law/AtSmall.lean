-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/AtSmall.lean: TEN PREMISES OF K10's LAW, ON THE GROUP AND ON THE
NUMBERS, MET TOGETHER AT A REAL GROUP OF THE SMALL SIZE. Statements and proofs.

All that needs no text of the description has moved, to the sign, to GroupSmall.lean
(beside this file): the group, the written place, nine of the ten premises, the proved block's
condition. What stays needs `Pulls` (OrderedOf.lean), beneath which the closing's text stands.
  `small_pulls`: hP: at every list, group, oM, oZ and kp: by `pulls_keep` (PullsOf.lean) and
    `membPort_onto`.
  `small_together`: TEN PREMISES MET TOGETHER AT A VALUE: hFi, hg, hj, hc, he, hv, hP, hx, hxs, hxe:
    at each of the 6 written lists, at the first group in front (9 row variables), nothing kept,
    every member's rows behind those of the messages in front of it.
Limits. Those of GroupSmall.lean: IT IS A MEMBER, NOT THE DESCRIPTION's OWN PLACE. The other
premises of K10's law are not treated. It rests on Johnson/Top/H/GroupRowsOnto.lean and
MemberOnto.lean, and through FoldPriced.lean on the files under ThirdParty/ (lean/LIMITS.md, L15).
Nothing on soundness of the protocol.

-/
import Johnson.Top.H.MemberOnto
import Johnson.Desc.First.Close.Law.PullsOf
import Johnson.Desc.First.Close.Law.GroupSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G Cb

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksSmallLit) (gs : GroupSize)
  (hgs : gs ∈ frontSmall) (oM oZ : Fin lo.length → ℕ)
  (kp : {i // memMain lo i} → Prop) [DecidablePred kp]

/-- hP. -/
theorem small_pulls : Pulls (groupSmall lo hlo gs hgs oM oZ kp)
    (pullOf (groupSmall lo hlo gs hgs oM oZ kp)) :=
  pulls_keep (rowsAtSmall lo hlo gs hgs 218 oM oZ) kp fun a =>
    membPort_onto codesSmall2 (lo.get a.1).1 (lo.get a.1).2 (stageOf gs 218) (oM a.1) (oZ a.1)
      (hMSmall lo hlo gs hgs 218 a.1 a.2) (hZSmall lo hlo gs hgs 218 a.1 a.2)

end

/-- **TEN PREMISES OF K10's LAW, MET TOGETHER AT A VALUE**: at each of the 6 written lists, at the
first group in front (9 row variables), nothing kept, every member's rows behind those of the
messages in front of it. -/
theorem small_together (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksSmallLit) :
    (groupSmall lo hlo (grpSmall 9 8 false) front9 (pre fun i => (lo.get i).1.mainRows)
        (pre (maskOf lo)) fun _ => False).G.Fits ∧
      (groupSmall lo hlo (grpSmall 9 8 false) front9 (pre fun i => (lo.get i).1.mainRows)
        (pre (maskOf lo)) fun _ => False).Good ∧
      InJ (groupSmall lo hlo (grpSmall 9 8 false) front9 (pre fun i => (lo.get i).1.mainRows)
          (pre (maskOf lo)) fun _ => False).s
        (groupSmall lo hlo (grpSmall 9 8 false) front9 (pre fun i => (lo.get i).1.mainRows)
          (pre (maskOf lo)) fun _ => False).e ∧
      CountsAt (groupSmall lo hlo (grpSmall 9 8 false) front9 (pre fun i => (lo.get i).1.mainRows)
          (pre (maskOf lo)) fun _ => False).s
        (groupSmall lo hlo (grpSmall 9 8 false) front9 (pre fun i => (lo.get i).1.mainRows)
          (pre (maskOf lo)) fun _ => False).e (placeSmall 9).bC (placeSmall 9).bZ ∧
      (groupSmall lo hlo (grpSmall 9 8 false) front9 (pre fun i => (lo.get i).1.mainRows)
          (pre (maskOf lo)) fun _ => False).G.e <
        (groupSmall lo hlo (grpSmall 9 8 false) front9 (pre fun i => (lo.get i).1.mainRows)
          (pre (maskOf lo)) fun _ => False).s.d ∧
      (∀ a, ((groupSmall lo hlo (grpSmall 9 8 false) front9 (pre fun i => (lo.get i).1.mainRows)
          (pre (maskOf lo)) fun _ => False).view a).Fix
        (groupSmall lo hlo (grpSmall 9 8 false) front9 (pre fun i => (lo.get i).1.mainRows)
          (pre (maskOf lo)) fun _ => False).G.e) ∧
      Pulls (groupSmall lo hlo (grpSmall 9 8 false) front9 (pre fun i => (lo.get i).1.mainRows)
          (pre (maskOf lo)) fun _ => False)
        (pullOf (groupSmall lo hlo (grpSmall 9 8 false) front9
          (pre fun i => (lo.get i).1.mainRows) (pre (maskOf lo)) fun _ => False)) ∧
      (placeSmall 9).Paid ∧
      (placeSmall 9).s = (groupSmall lo hlo (grpSmall 9 8 false) front9
        (pre fun i => (lo.get i).1.mainRows) (pre (maskOf lo)) fun _ => False).s ∧
      (placeSmall 9).e = (groupSmall lo hlo (grpSmall 9 8 false) front9
        (pre fun i => (lo.get i).1.mainRows) (pre (maskOf lo)) fun _ => False).e :=
  ⟨small_fits lo hlo _ front9 _ _ _,
    small_good_pre lo hlo _ front9
      (by rw [sum_get lo fun x => x.1.mainRows]; exact (linksSmall_fit9 lo hlo).1)
      (by
        have h := (linksSmall_fit9 lo hlo).2
        rw [← sum_get lo fun x => if x.1.mainRows ≠ 0 then x.1.maskRows else 0] at h
        exact h),
    small_inJ lo hlo _ front9 _ _ _, small_counts lo hlo _ front9 _ _ _,
    small_radius lo hlo _ front9 _ _ _, small_fix lo hlo _ front9 _ _ _,
    small_pulls lo hlo _ front9 _ _ _, placeSmall_paid _ front9,
    small_stage lo hlo _ front9 _ _ _, small_radius_eq lo hlo _ front9 _ _ _⟩

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.small_pulls
#print axioms VerifiableInference.Desc.First.Close.small_together
