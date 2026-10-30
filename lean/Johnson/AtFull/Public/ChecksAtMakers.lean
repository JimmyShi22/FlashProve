-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/ChecksAtMakers.lean: THE RANGE CHECKS OF A REQUEST AT THE FULL SIZE ARE THE
WRITTEN LIST, at a public part with the makers' plans: the hypotheses by field of
rangeChecks_of_fields (Johnson/AtFull/Made/RangeChecksOfFields.lean), paid by Lean's kernel at what
the makers return, and carried to the witnesses by at_witnesses
(Johnson/AtFull/Public/AtWitnesses.lean).

  `sizesLB G`, `sizesAB A`: at each group below 12 there is a plan whose smallness test has the
    written rows and columns (sizesL, sizesA) and 128 combinations.
  `sizes_W`: [Lean's kernel; no free letter] atMakers accepts both. `sizes_no`: a negative test: the
    makers return, and the layers' tests do not have the attention's sizes.
  `headSizesB H`, `head_sizes`: [Lean's kernel] planH2 at the stand-ins returns, and its smallness
    test has sizesH and 128 combinations. `head_sizes_no`: it has not 127.
  `sizes_of_LB`, `sizes_of_AB`: what an accept says, as propositions.
  **`hc_at`**: rangeChecksOf X = some checksFull at a public part X with twelve groups, attention,
    the witnesses' plans and the head's plan HW, trimmed.

Limits. OpensAt and Makers are premises, as in AtWitnesses.lean. checksFull was copied off a run
(its file's head). The full size alone. Nothing on soundness.

-/
import Johnson.AtFull.Public.AtWitnesses
import Johnson.AtFull.Head.PlanAtFull
import Johnson.AtFull.Made.RangeChecksOfFields

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Public

open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Road.K4.Trial.AttL2 (AOf)
open Johnson.AtFull.Made (sizesOf sizesL sizesA sizesH checksFull rangeChecks_of_fields)
open _root_.AtFull.Head (HW runW runW_ok)

/-- At each group below 12: a layers' plan whose smallness test has the sizes s and 128
combinations. -/
def sizesLB (s : List (Nat × Nat)) (G : Array Layer.HPlan2) : Bool :=
  (List.range 12).all fun g => (G[g]?).any fun hp =>
    decide (sizesOf hp.tl = s) && hp.tl.tau == 128

/-- The like for the attention's plans. -/
def sizesAB (s : List (Nat × Nat)) (A : Array Attention.Plan) : Bool :=
  (List.range 12).all fun g => (A[g]?).any fun a =>
    decide (sizesOf a.seam.tl = s) && a.seam.tl.tau == 128

/-- **By the kernel: the 24 smallness tests have the written sizes and 128 combinations.** -/
theorem sizes_W : atMakers (fun _ G A => sizesLB sizesL G && sizesAB sizesA A) = true := by
  decide +kernel

/-- A negative test: the makers return, and the layers' tests have not the attention's sizes. -/
theorem sizes_no : atMakers (fun _ G _ => !sizesLB sizesA G) = true := by decide +kernel

/-- The head's smallness test has the written sizes and t combinations. -/
def headSizesB (t : Nat) (H : Head.HPlanH2) : Bool :=
  decide (sizesOf H.tl = sizesH) && H.tl.tau == t

theorem head_sizes : (match runW with
    | .ok H => headSizesB 128 H
    | .error _ => false) = true := by decide +kernel

theorem head_sizes_no : (match runW with
    | .ok H => !headSizesB 127 H
    | .error _ => false) = true := by decide +kernel

theorem sizes_of_LB {s : List (Nat × Nat)} {G : Array Layer.HPlan2} (h : sizesLB s G = true) :
    ∀ g, g < 12 → ∃ hp, G[g]? = some hp ∧ sizesOf hp.tl = s ∧ hp.tl.tau = 128 := by
  intro g hg
  have hg' := List.all_eq_true.1 h g (List.mem_range.2 hg)
  cases e : G[g]? with
  | none =>
    rw [e] at hg'
    cases hg'
  | some hp =>
    rw [e] at hg'
    simp only [Option.any, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hg'
    exact ⟨hp, rfl, hg'.1, hg'.2⟩

theorem sizes_of_AB {s : List (Nat × Nat)} {A : Array Attention.Plan} (h : sizesAB s A = true) :
    ∀ g, g < 12 → ∃ a, A[g]? = some a ∧ sizesOf a.seam.tl = s ∧ a.seam.tl.tau = 128 := by
  intro g hg
  have hg' := List.all_eq_true.1 h g (List.mem_range.2 hg)
  cases e : A[g]? with
  | none =>
    rw [e] at hg'
    cases hg'
  | some a =>
    rw [e] at hg'
    simp only [Option.any, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hg'
    exact ⟨a, rfl, hg'.1, hg'.2⟩

variable {y : Layer.Lay} {sc : Layer.Scales} {wsLay : WsLay} {rope : Array Nat}
  {l : List Attention.Line} {ps : List Attention.Plan} {layers : Layer.Pub}
  {G : Array Layer.HPlan2} {seenA : Array SubPlan}

/-- **The range checks are the written list.** -/
theorem hc_at (O : OpensAt y) (M : Makers y sc wsLay rope l ps layers G seenA) {X : Public}
    (hN : X.NGr = 12) (h4 : X.p4 = true) (eG : X.G = G) (eA : X.A = AOf ps.toArray seenA)
    (eH : X.H = { HW with Fp := HW.Fp.trimL }) : rangeChecksOf X = some checksFull := by
  have h := at_witnesses O M sizes_W
  rw [Bool.and_eq_true] at h
  have hh := head_sizes
  rw [runW_ok] at hh
  unfold headSizesB at hh
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hh
  refine rangeChecks_of_fields h4 hN ?_ ?_ ?_
  · rw [eG]
    exact sizes_of_LB h.1
  · rw [eA]
    exact sizes_of_AB h.2
  · rw [eH]
    exact hh

end Johnson.AtFull.Public

#print axioms Johnson.AtFull.Public.sizes_W
#print axioms Johnson.AtFull.Public.sizes_no
#print axioms Johnson.AtFull.Public.head_sizes
#print axioms Johnson.AtFull.Public.head_sizes_no
#print axioms Johnson.AtFull.Public.sizes_of_LB
#print axioms Johnson.AtFull.Public.sizes_of_AB
#print axioms Johnson.AtFull.Public.hc_at
