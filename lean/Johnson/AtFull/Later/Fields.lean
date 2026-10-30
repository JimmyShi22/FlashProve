-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Later/Fields.lean: five small theorems on what the planner answers at a public part
that is as at the full size, which the tests on the proof file's shared chain read and which the
statements on the planner's answer (Johnson/AtFull/Made/MadeAtJoinD.lean) do not name.

  `links_sized`, `links_written`: the request of the written sizes has 25 links, and so has the
    written list of links. By evaluation in Lean's kernel. `links_sized_no`: the first number is
    not 24: it shows only that the first is no constant yes.
  `first_anew`: the planner's routine for the first chain, run anew at the written sizes and at
    the links that stand IN these sizes, returns the written first plan. The statement that is
    called (`first_of_arms`) stands at the written list of links. Of the links that are handed to
    `subproofsWith` the routine reads only how many there are (`firstPlan_congr`,
    Johnson/AtFull/Made/FirstReads.lean); the links in the sizes it reads whole, and they are the
    same on both sides. So the two numbers carry it over; that the two lists are equal is neither
    needed nor said.
  `shared_read`: the shared chain's parameters as they are read back hold the written shape and
    the written codes. By the text of the value that the planner returns.

Limits. The premises on the public part X are premises: nothing here shows them at any files.
The full size alone. Nothing on soundness or on hiding.

-/
import Johnson.AtFull.Made.MadeAtJoinD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Later
open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages OnBytes.Params
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Number.ByRuns (proofThree)
open Johnson.AtFull.LayoutRead (LW)
open Johnson.AtFull.Made
open H2K.Sizes (PubFull)
open VerifiableInference.Desc.LinkJoin (armsB)

/-- The request of the written sizes has 25 links. -/
theorem links_sized : proofSizedFull.request.link.length = 25 := by decide +kernel

/-- The written list of links has 25 members. -/
theorem links_written : reqLinksW.length = 25 := by decide +kernel

/-- The first of these can fail: the request of the written sizes does not have 24 links. -/
theorem links_sized_no : (proofSizedFull.request.link.length == 24) = false := by decide +kernel

/-- **The first chain's plan, made anew at the links that stand in the written sizes.** -/
theorem first_anew {X : Public} {rc : List RangeCheck} (P : PubFull X)
    (hc : rangeChecksOf X = some rc) (ha : armsB X = true) :
    firstPlan proofSizedFull (subproofsWith X proofSizedFull.request.link) =
      .ok proofThree.A.plan := by
  have h2 : (subproofsWith X proofSizedFull.request.link).openRows =
      (subproofsWith X reqLinksW).openRows := by
    show List.replicate proofSizedFull.request.link.length 1 = List.replicate reqLinksW.length 1
    rw [links_sized, links_written]
  exact (firstPlan_congr (sub := subproofsWith X proofSizedFull.request.link)
    (sub' := subproofsWith X reqLinksW) (n := 25) (le_of_eq links_sized) (fun _ _ _ => rfl) h2 rfl
    rfl).trans (first_of_arms P hc ha)

/-- **The shared chain's parameters as read back**: the written shape and the written codes. -/
theorem shared_read {X : Public} {lay cfg : ByteArray} {m : Johnson.G.OfPlan.Made} (P : PubFull X)
    (hG : X.G.size = 12) (hA : X.A.size = 12)
    (hV : (OnBytes.TieK.listedOf X default).map Decl.viewL = Decl.viewsFull)
    (b₁ : Plan.layoutRead lay = some LW) (h32 : cfg.size = 32) (ha : armsB X = true)
    (hc : rangeChecksOf X = some checksFull)
    (hm : VerifiableInference.Desc.Key.madeAt X lay cfg = .ok m) :
    m.p.chains.proof.shared.lin = proofSizedFull.batch.shape ∧
      m.p.chains.proof.shared.codes = proofSizedFull.codes := by
  obtain ⟨_, _, sh, h, -⟩ := madeAt_at_full P hG hA hV b₁ h32 ha hc
  obtain rfl := Except.ok.inj (h.symm.trans hm)
  exact ⟨rfl, rfl⟩

end Johnson.AtFull.Later

#print axioms Johnson.AtFull.Later.links_sized
#print axioms Johnson.AtFull.Later.links_written
#print axioms Johnson.AtFull.Later.links_sized_no
#print axioms Johnson.AtFull.Later.first_anew
#print axioms Johnson.AtFull.Later.shared_read
