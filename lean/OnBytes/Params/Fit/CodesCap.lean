-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/CodesCap.lean: the lists of codes that the derivation fills from solved stages
hold only codes with short messages.

"ioppStages" (OnBytes/Params/Derive.lean) enters the two codes of each solved stage into the lists
of a chain's codes ("placeCode"). OnBytes/Params/Fit/SolveCap.lean shows that a solved group's
messages have at most 2 ^ 32 entries at both codes (GroupFit). So the lists hold only such codes.

Main names.
 - CodesCap codes: every code of both lists has logEll ≤ 64 (Code.logEll, OnBytes/Iop/Ground.lean:
   the rounded-up logarithm of the message's length).
 - ceilLog2_le_of: n ≤ 2 ^ k gives ceilLog2 n ≤ k.
 - codesCap_empty, placeCode_cap, **ioppStages_cap**: the empty lists; one code more; the codes of a
   list of stages whose groups are GroupFit.
 - stages_fit: every stage that solveStages returns is GroupFit, if the first group is and the
   stages' lines have their ranges. solveTest_fit: the same of solveTest, from the ranges of the
   group's line and the shape's two lengths.

Limits. In truth the logarithms are at most 32; 64 is what CodesShort asks
(OnBytes/Params/Fit/FitCubes.lean; "codesShort_of_cap", FitCaps.lean). Nothing on a code's length or
random entries. That the lists of a sized record are made in this way is not shown here. The
program does not import this file.

-/
import OnBytes.Params.Fit.SolveCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

/-- Every code of both lists has a message of at most 2 ^ 64 entries, by the logarithm. -/
def CodesCap (codes : Codes) : Prop :=
  (∀ c ∈ codes.base.toList, c.logEll ≤ 64) ∧ ∀ c ∈ codes.mask.toList, c.logEll ≤ 64

/-- The rounded-up logarithm is at most every exponent that is large enough. -/
theorem ceilLog2_le_of {n k : Nat} (h : n ≤ 2 ^ k) : ceilLog2 n ≤ k := by
  unfold ceilLog2
  split
  · exact Nat.zero_le k
  · rename_i h1
    have h2 : Nat.log2 (n - 1) < k := (Nat.log2_lt (by omega)).2 (by omega)
    omega

theorem codesCap_empty : CodesCap {} :=
  ⟨fun _ hc => (List.not_mem_nil hc).elim, fun _ hc => (List.not_mem_nil hc).elim⟩

/-- One code more. -/
theorem placeCode_cap {list : Array Code} {c : CodeSize} (hl : ∀ x ∈ list.toList, x.logEll ≤ 64)
    (hc : CodeFit c) : ∀ x ∈ (placeCode list c).1.toList, x.logEll ≤ 64 := by
  unfold placeCode
  dsimp only
  split
  · exact hl
  · intro x hx
    rw [Array.toList_push] at hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hl x hx
    · obtain rfl := List.mem_singleton.1 hx
      show ceilLog2 c.ell ≤ 64
      have h32 : ceilLog2 c.ell ≤ 32 := ceilLog2_le_of hc.2
      omega

/-- **The codes of a list of stages.** -/
theorem ioppStages_cap : ∀ (st : List StageSize) (codes : Codes), CodesCap codes →
    (∀ y ∈ st, GroupFit y.g) → CodesCap (ioppStages st codes).2 := by
  intro st
  induction st with
  | nil =>
    intro codes H _
    exact H
  | cons y rest ih =>
    intro codes H hf
    unfold ioppStages
    dsimp only
    have hy := hf y List.mem_cons_self
    exact ih _ ⟨placeCode_cap H.1 hy.1, placeCode_cap H.2 hy.2⟩
      fun y' hy' => hf y' (List.mem_cons_of_mem _ hy')

/-- Every stage of a proximity test fits, if the first group does. -/
theorem stages_fit {s : Setting} {scope : Scope} {first : GroupSize}
    {firstT : Nat} {choice : List StageLine} {st : List StageSize}
    (hc : ∀ c ∈ choice, StageCap c) (hf : GroupFit first)
    (h : solveStages s scope first firstT choice = some st) : ∀ y ∈ st, GroupFit y.g := by
  intro y hy
  rcases solveStages_fit hc h y hy with e | e
  · rw [e]
    exact hf
  · exact e.1

/-- The stages of a group that is solved and then tested. -/
theorem solveTest_fit {s : Setting} {scope : Scope} {l : GroupLine} {load : GroupLoad}
    {draws : Nat → Nat} {shape : GroupSize} {t : TestSizes} (H : GroupCap l)
    (hN : shape.main.logN ≤ 32) (hZ : shape.mask.logN ≤ 32)
    (h : solveTest s scope l load draws shape = some t) :
    Solves shape t.group ∧ ∀ y ∈ t.stages, GroupFit y.g := by
  unfold solveTest at h
  obtain ⟨x, hx, h⟩ := opt_bind h
  obtain ⟨st, hs, h⟩ := opt_bind h
  cases h
  have S := solveGroup_solves hx
  exact ⟨S, stages_fit H.stages (fit_of_solves S hN hZ) hs⟩

end OnBytes.Params

#print axioms OnBytes.Params.placeCode_cap
#print axioms OnBytes.Params.ioppStages_cap
#print axioms OnBytes.Params.stages_fit
#print axioms OnBytes.Params.solveTest_fit
