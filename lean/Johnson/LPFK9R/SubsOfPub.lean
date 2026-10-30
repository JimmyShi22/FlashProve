-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK9R/SubsOfPub.lean: THE SORTS OF THE 25 SEGMENTS, `ProofFile.subsOf Z`
(Johnson/Desc/ProofFile/Frames1.lean), ARE THE WRITTEN ROW: FROM THE GOALS' SCOPE, THE READING OF
THE FILES AND THE RETURN OF THE PUBLIC PART `ProofFile.pubPlain` ALONE: NO OPENING OF THE DESCRIPTION.
Statements and proofs.

Why. `IM.subs_all` (Johnson/IMR/PlacesScope.lean) has the same end from an opening O : IM.Open …, of
which it spends three fields: pub and blank (the members below 25) and chain (that there is no
26th). The road to an example of the head by the kernel may not spend an opening: that is what it is
to give. Hence this form without it.

How: by the make, on the plain road's own laws. The public part's return holds the
plain planner's (`ProofFile.Law.pub_planned`); that holds `builtOf`'s (`IM.planned_built`), which is
`buildLinksH` of `linksPlain` (`IM.plain_built`); building keeps the kinds
  (`TieK.buildLinksH_keeps`); linksPlain is `listLinksH` by its text, whose kinds are `kindsL`, then
  2 (`TieK.listLinksH_kinds`), with as many plans as groups (`listLinksH_with`). In scope attention
  is covered and there are twelve groups (`Meaning.scope_plans`).
  `kindsL_full`: with attention covered and a plan for every group: a 0 and a 1 for each group.
  `linksW_list`: the written row `IM.linksW` member by member: so a tie to any other written row of
    25 sorts is one closed line. (That it is the driver's `Sound.linksFull` is proved:
    `LPFK9.linksW_full`, Johnson/LPFK9R/SubsFull.lean.)
  `subs_of_pub`: **MAIN: ProofFile.subsOf Z = IM.linksW.** lay is a free letter.
Limits. At the second hash function (secondHashFunction) alone. That pubPlain returns is a premise. No
soundness statement.

-/
import Johnson.IMR.PureJoin
import Johnson.IMR.WrittenList
import Johnson.Desc.ProofFile.Law.PlainMade
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws
import Johnson.Goal.Meaning.PlanShapes
import OnBytes.TieK.LinksEnd
import OnBytes.Tie.Pv.Keeps.LinksOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (SubPlanH LinkH listLinksH)
open OnBytes.TieK (kindsL)
open VerifiableInference.Desc.First (ModelPart)

/-- With attention covered and a plan for every group: a 0 and a 1 for each group. -/
theorem kindsL_full (A : Array SubPlanH) : ∀ n, n ≤ A.size →
    kindsL true A n = (List.range n).flatMap fun _ => [0, 1]
  | 0, _ => rfl
  | n + 1, h => by
    have hs : (A[n]?).isSome = true := by
      rw [Array.getElem?_eq_getElem (by omega : n < A.size)]
      rfl
    rw [kindsL, kindsL_full A n (by omega), List.range_succ, List.flatMap_append]
    simp [hs]

/-- The written row of sorts, member by member. -/
theorem linksW_list : IM.linksW =
    [.layers, .attention, .layers, .attention, .layers, .attention, .layers, .attention,
     .layers, .attention, .layers, .attention, .layers, .attention, .layers, .attention,
     .layers, .attention, .layers, .attention, .layers, .attention, .layers, .attention,
     .head] := by decide

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}

/-- **THE 25 SEGMENTS' SORTS ARE THE WRITTEN ONES: FROM THE SCOPE, THE READING AND THE PUBLIC
PART's RETURN ALONE.** -/
theorem subs_of_pub (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z) : ProofFile.subsOf Z = IM.linksW := by
  have hX : Verify.publicOf P.pol P.KL (some lay) = .ok Z.p.X :=
    (VerifiableInference.PlanWritten.publicOfO_older P.pol P.KL (some lay)).symm.trans
      (ProofFile.Law.pub_public hZ)
  obtain ⟨h4, hN, -, -⟩ := Meaning.scope_plans hS hR hX
  obtain ⟨l₀, hl, hb⟩ := IM.plain_built (IM.planned_built (ProofFile.Law.pub_planned hZ))
  unfold ProofFile.Plain.linksPlain at hl
  rw [h4, hN] at hl
  obtain ⟨hG, hA, -⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ hl
  obtain ⟨pre, rfl, hk⟩ := OnBytes.TieK.listLinksH_kinds hl
  rw [hG, kindsL_full _ 12 (by rw [hA])] at hk
  unfold ProofFile.subsOf
  rw [OnBytes.TieK.buildLinksH_keeps (fun X => ProofFile.subOf X.kind) (fun _ _ => rfl) hb,
    Array.toList_push, List.map_append,
    show pre.toList.map (fun X => ProofFile.subOf X.kind) = (pre.toList.map (·.kind)).map ProofFile.subOf by
      rw [List.map_map]; rfl, hk]
  show List.map ProofFile.subOf ((List.range 12).flatMap fun _ => [0, 1]) ++ [ProofFile.subOf 2] = IM.linksW
  decide

end LPFK9

#print axioms LPFK9.kindsL_full
#print axioms LPFK9.linksW_list
#print axioms LPFK9.subs_of_pub
