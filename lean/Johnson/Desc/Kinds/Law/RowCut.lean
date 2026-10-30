-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RowCut.lean: THE OUTPUT HEAD's ROW OF THE TABLE OF JOINTS, WITH THE 17 ROW FORMS (idn · the two sums · keys and rider in our own words; planes on neither side; join not among the outs), AT THE BLOCK's ONE HEARING, WITH NO BAD EVENT LEFT AS A PREMISE OF
ITS OWN: the point pV has its place in the rule, coordinate by coordinate: STATED AND PROVED.
WHAT IT DOES NOT SAY. c AND mask ARE LETTERS UNDER "FOR ALL", TIED HERE TO NOTHING THAT IS FIXED IN FRONT OF THE DRAWS: the law is meant to be spent at the
witness's components that are pinned in front of the block's first draw (the table of joints: pin 4 0, pinW): THAT INSTANCE IS THE CALLER's, AND IS NOWHERE YET; whoever
may pick mask behind the draws makes every hidden scalar what they like.
That the 35 forms are 0, that the claim on the weights is true: premises (what the block OPENS). How
probable a bad draw is: lists are counted; no written challenge is counted; no sum of errors is taken. That an honest run
meets the premises. 0 < d is a premise on the plan's public numbers.
WHAT IT IS. A rule here sees a front CUT IN FRONT OF THE ELEMENT IN QUESTION: THE VERY FORM OF A RULE THAT THE BRIDGE FROM A KIND's RULE
TO A BLOCK's ERRORS TYPES (a light file, imported: Johnson/Desc/Sound/RuleForm.lean: cutTo, strikeLast, NoBad, written
Sound.NoBad here; HeadLaw.lean's own NoBad is its NoBadStruck).
  rowRuleC          pointRule at the front, and Law/RowWhole.lean's rowRule at the front with its last round's draw struck.
  blockRule_one     at a front of one round the rule behind the normalization is empty.
  rowRuleC_length   the ceiling: at most the last message's scalars and one; at a WellLaid ledger.
  goodPoint_of_cut  no coordinate in pointRule's list at its front: the point is good.
  RowCutStatement   Law/RowWhole.lean's statement with Sound.NoBad (rowRuleC …) in the place of NoBad (rowRule …) and of GoodPoint.
IMPORTED, NOT PROVED HERE: Law/NormPointRule.lean (pointRule, point_clean, noBad_of_cut, cut_left;
over Alg/Cut.lean).

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RowCeil
import Johnson.Desc.Kinds.Law.NormPointRule

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open Sound (cutTo strikeLast)
open OnBytes.Model (Fork World)
open OnBytes.PscRun (Later)
open Norm (lt ls d lPd S2 T)

/-- **THE BLOCK's ONE RULE, THE POINT WITH IT, BY NAME.** -/
noncomputable def Came.rowRuleC [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] (c : NCells)
    (mask : Nat → E) (F : Fork) : List Fmt.RoundView → List E :=
  fun g => pointRule c g ++ Came.rowRule c mask F (strikeLast g)

/-- **THE ROW, WITH THE 17 ROW FORMS, NO BAD EVENT BESIDE THE RULE.** -/
def RowCutStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] [nI : FinalNorm.In] [hI : In] (sT floor : Nat) (zx : Point)
    (zk : Nat → Point) (c : NCells) (mask : Nat → E) (F : Fork),
    planOk sT = true → 0 < d → Request.ok = true → y < V → WellLaid F → PointsOk floor zx zk →
    nI = (fromLookup floor zx zk).norm → hI = (fromLookup floor zx zk).head →
    ∀ (rs : List Fmt.RoundView) (H : HeardAll) (F1 G : Fork),
      Canonical rs → hear F rs = some (H, F1, []) → Later F1 G →
      Sound.NoBad (Came.rowRuleC c mask F) rs →
      let _ : Norm.Heard := H.1
      let _ : FinalNorm.Heard := H.2.1
      let _ : Heard := H.2.2
      let _ : FinalNorm.Reads := normReadsAtCells c
      let _ : Reads := readsAt c.toCells
      WeightTrue c.toCells G mask noEnt →
      (∀ name fs, claims.lookup name = some fs → ∀ f, f ∈ fs → atWorld G mask noEnt f = 0) →
      (∀ t, t < T → ∀ v, v ∈ rowsAt c (bits lt t) → v = 0) ∧
      (meanAt c.toCells = 0 ∧ countAt c.toCells = 0) ∧
      (∀ call, call < 6 →
        rd (atWorld G mask noEnt
            (keyVector key ((fromLookup floor zx zk).calls.getD call (0, [])).1 (callKeys call)))
          = (Finset.range (2 ^ (zk call).size)).sum fun i =>
              rd (eq (zk call) i) * rd (keyTable c call (i / T) (i % T))) ∧
      (∑ t < T, eq FinalNorm.zt t * clipAt c.toCells (corner 0 t)) = 0 ∧
      (∑ t < T, eq FinalNorm.zt t * tableAt c.toCells (corner 0 t)) = 0

namespace Came

variable [Sizes] [Policy] [Request] [Token]

/-- The normalization's hearing does not return on one round. -/
theorem norm_not_one (F : Fork) (hW : WellLaid F) (r : Fmt.RoundView) : Norm.hear F [r] = none := by
  cases hN : Norm.hear F [r] with
  | none => rfl
  | some v =>
    obtain ⟨H, G, left⟩ := v
    obtain ⟨p0, p1, tS, p2, tP, Fa, Fb, Fc, hrs, h0, h1, _⟩ := norm_parts hW hN
    obtain ⟨r0, rfl⟩ := drawPoint_one h0
    obtain ⟨r1, _, rfl, _, _, _⟩ := batch_one h1
    have := congrArg List.length hrs
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega

/-- **No coordinate in the point's rule's list at its front: the point is good.** -/
theorem goodPoint_of_cut (c : NCells) {F G : Fork} (hW : WellLaid F) {rs left : List Fmt.RoundView}
    {H : Norm.Heard} (hcan : Canonical rs) (hN : Norm.hear F rs = some (H, G, left))
    (hnb : Sound.NoBad (pointRule c) rs) : GoodPoint c H.pV := by
  obtain ⟨p0, p1, tS, p2, tP, Fa, Fb, Fc, hrs, h0, _⟩ := norm_parts hW hN
  obtain ⟨r0, rfl⟩ := drawPoint_one h0
  refine point_clean c h0 (fun x hx => (hcan r0 (by rw [hrs]; simp)).2 x hx) fun j x hj => ?_
  exact hnb 0 r0 (by rw [hrs]; rfl) j x hj

variable [FinalNorm.In] [In]

theorem blockRule_one (c : NCells) (mask : Nat → E) (F : Fork) (hW : WellLaid F) (r : Fmt.RoundView) :
    blockRule c mask F [r] = [] :=
  blockRule_none c mask F (norm_not_one F hW r)

/-- **THE CEILING.** -/
theorem rowRuleC_length (c : NCells) (mask : Nat → E) (F : Fork) (hW : WellLaid F)
    (g : List Fmt.RoundView) : (rowRuleC c mask F g).length
      ≤ ((g.getLast?.map fun r => r.vals.length).getD 0) + 1 := by
  unfold rowRuleC
  rw [List.length_append]
  match g with
  | [] =>
    have h := rowRule_length c mask F hW (strikeLast [])
    rw [strikeLast_vals] at h
    have e : pointRule c [] = [] := rfl
    rw [e]
    simpa using h
  | [r] =>
    have e : strikeLast [r] = [cutTo r 0] := strikeLast_concat [] r
    have e2 : rowRule c mask F [cutTo r 0] = [] := by
      unfold rowRule
      rw [blockRule_one c mask F hW]
      rfl
    rw [e, e2]
    have := pointRule_length c [r]
    simp only [List.length_nil]
    omega
  | r :: a :: fr =>
    have e : pointRule c (r :: a :: fr) = [] := rfl
    have h := rowRule_length c mask F hW (strikeLast (r :: a :: fr))
    rw [strikeLast_vals] at h
    rw [e]
    simpa using h

end Came

namespace Came

theorem rowCut : RowCutStatement := by
  intro _ _ _ _ nI hI sT floor zx zk c mask F hplan hd0 hreq hy hWL hP hn hh rs H F1 G hcan hhear hL hnb
  obtain ⟨Fa, Fb, l1, hNorm, _⟩ := hear_parts hWL hhear
  exact rowWhole sT floor zx zk c mask F hplan hd0 hreq hy hWL hP hn hh rs H F1 G hcan hhear hL
    (noBad_of_cut (p := pointRule c) (b := rowRule c mask F) hnb)
    (goodPoint_of_cut c hWL hcan hNorm
      (cut_left (p := pointRule c) (q := fun g => rowRule c mask F (strikeLast g)) hnb))

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rowRuleC_length
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rowCut
