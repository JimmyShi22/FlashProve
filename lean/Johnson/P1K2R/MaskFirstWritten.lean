-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/MaskFirstWritten.lean: code switching (K2): TWO OF THE CLOSED PREMISES OF ITS SHARE
OF e₁ AT AN ATTENTION LINK's FIRST PLACE (K5Plan.hμ, Johnson/P1K2R/MadeFirst.lean · hμc,
Johnson/P1K2R/FencesReached.lean), WHICH READ THE REQUEST's SHAPE ALONE: BY LEAN's KERNEL AT THE
WRITTEN SHAPE OF THE FULL SIZE (proofSizedFull.request,
Johnson/Desc/Ok/PlanWritten/SizedLit.lean), with negative tests. NO BLOCK IMPORTS THIS FILE.
  maskFirstB sh l       ONE Bool ON THE SHAPE: link l has a message with a mask row, and the first
                        such stands below the number of the link's messages of moment 0
  mask_first_of         what an accept says: ∃ μ: hμ ∧ hμc, to the letter
  attW                  the written attention links among 1 … 23
  att_count             BY THE KERNEL: they are the twelve odd numbers 1 … 23 (so that what
                        follows is not true of an empty list)
  mask_first_written    BY THE KERNEL: the test accepts at every one of them
  mask_first_late · mask_first_none   TWO NEGATIVE TESTS, BY THE KERNEL: with every message's
                                      moment set to 1 the test rejects at all of them · at a link
                                      that the shape has not (25) it rejects
  mu_at_written         so, where the plan's shape is the written one: at every written attention
                        link: ∃ μ: hμ ∧ hμc
THE TIE TO A VALUE THAT IS LAID: Z.first.shape = proofSizedFull.request: in scope under the first
pin: first_written_in_scope (Johnson/Goal/Numbers/MadeInScope.lean) | AtWritten.shape: NOT
CALLED HERE: a premise.
LIMITS. The full size alone. Two premises of many. No soundness is claimed.
-/
import Johnson.P1K2R.MadeFirst
import Johnson.Desc.Ok.PlanWritten.SizedLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (ModelPart)
open VerifiableInference.PlanWritten (proofSizedFull)
open IM (subW)

/-- Link l has a message with a mask row; the first such stands among those of moment 0. -/
def maskFirstB (sh : Params.ReqShape) (l : Nat) : Bool :=
  match ((sh.link[l]?.map (·.messages)).getD []).findIdx? fun x => x.shape.maskRows != 0 with
  | some μ => decide (μ < (((sh.link[l]?.map (·.messages)).getD []).filter
      fun y => y.moment == 0).length)
  | none => false

theorem mask_first_of {sh : Params.ReqShape} {l : Nat} (h : maskFirstB sh l = true) :
    ∃ μ, (((sh.link[l]?.map (·.messages)).getD []).findIdx? fun x =>
        x.shape.maskRows != 0) = some μ ∧
      μ < (((sh.link[l]?.map (·.messages)).getD []).filter fun y => y.moment == 0).length := by
  unfold maskFirstB at h
  split at h
  · rename_i μ hμ
    exact ⟨μ, hμ, of_decide_eq_true h⟩
  · cases h

/-- The written attention links among 1 … 23. -/
def attW : List Nat := (List.range' 1 23).filter fun l => decide (subW l = .attention)

/-- The shape with every message's moment set to 1. -/
def allLate (sh : Params.ReqShape) : Params.ReqShape :=
  { sh with link := sh.link.map fun L =>
      { L with messages := L.messages.map fun x => { x with moment := 1 } } }

set_option maxRecDepth 1000000 in
theorem att_count : attW = [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23] := by decide +kernel

set_option maxRecDepth 1000000 in
theorem mask_first_written : attW.all (maskFirstB proofSizedFull.request) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem mask_first_late : attW.any (maskFirstB (allLate proofSizedFull.request)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem mask_first_none : maskFirstB proofSizedFull.request 25 = false := by decide +kernel

theorem mu_at_written {sh : Params.ReqShape} (hsh : sh = proofSizedFull.request) {l : Nat}
    (h1 : 1 ≤ l) (h24 : l < 24) (hatt : subW l = .attention) :
    ∃ μ, (((sh.link[l]?.map (·.messages)).getD []).findIdx? fun x =>
        x.shape.maskRows != 0) = some μ ∧
      μ < (((sh.link[l]?.map (·.messages)).getD []).filter fun y => y.moment == 0).length := by
  subst hsh
  refine mask_first_of (List.all_eq_true.1 mask_first_written l ?_)
  unfold attW
  exact List.mem_filter.2 ⟨List.mem_range'_1.2 ⟨h1, by omega⟩, decide_eq_true hatt⟩

end P1K2

#print axioms P1K2.mask_first_of
#print axioms P1K2.att_count
#print axioms P1K2.mask_first_written
#print axioms P1K2.mask_first_late
#print axioms P1K2.mask_first_none
#print axioms P1K2.mu_at_written
