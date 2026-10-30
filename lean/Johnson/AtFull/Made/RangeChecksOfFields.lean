-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/RangeChecksOfFields.lean: `rangeChecksOf X = some checksFull` UNDER HYPOTHESES
BY FIELD OF THE PUBLIC PART X, WITH A BENT TWIN. Laws by unfolding, and two closed facts on lists. A
law file; no running text imports it. Nothing on codes.

What it is for. The premise hc of `shapes_and_sizes` (Johnson/AtFull/Made/ShapesReturn.lean), and
what the planner's fourth gate reads (`ShapesRead.checks`, Johnson/AtFull/Made/Gates.lean).
Johnson/AtFull/Made/RangeChecksReturn.lean has it from each smallness test's list of checks; here
from two fields of each test.

  `sizesOf tl`, `checkAt tau p`: a test's matrices' (rows, columns); the check of one.
    `checksH_of_fields`: of a smallness test the range checks read these and tau, nothing else.
  `rangeChecks_of_sizes`: **forward, at all sizes and numbers of combinations**: p4 · twelve groups
    · each layers' test has sizes sL and tL combinations · each attention's sA and tA · the head's
    sH and tH ⊢ the value.
  `sizesL`, `sizesA`, `sizesH`: the written sizes, READ OFF `checksPair` AND `checksHead` THEMSELVES
    (Johnson/AtFull/Made/GateChecks.lean): no number is typed here. `sizes_full`: at
    these and 128 the value is `checksFull`.
  `rangeChecks_of_fields`: the law asked for.
  `sizes_bent`, `rangeChecks_bent`: THE BENT TWIN: with 127 combinations at the head's test the
    range checks are not `checksFull`; and, as lists alone (used by nothing), with one column more
    in the layers' first matrix.
  `checksAtHead`, `bits_at_head`: THE TWIN BITES THE VALUE, NOT THE GATE: the fourth gate and
    `ShapesRead.checks` read each check's BITS (`rangeCheckBits`), and at 127 combinations these are
    the written list's: a public part bent so would still meet `ShapesRead.checks`. At 129 the bits
    part.

WHAT IS READ OF X: p4 · NGr · G[g]?.tl and A[g]?.seam.tl at g below 12 · H.tl; of each tl: mats' m
and k, in order, and tau.

Limits. THE HYPOTHESES ARE HYPOTHESES: shown at no files. That all twelve groups have one list of
sizes is part of what is asked. `sizes_full` would hold at every cut of the pair's fourteen: that
the layers' test has the first nine is borne by hL and hA alone. The bent twin's public part is
thought up: no files are shown to reach it. `checksFull` was copied off a run (its file's head). The
full size alone. Nothing on soundness.

-/
import Johnson.AtFull.Made.RangeChecksReturn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Verify

/-! ## 1 A smallness test's checks, from two fields of it -/

/-- The rows and columns of a smallness test's matrices, in order. -/
def sizesOf (tl : HTailF2) : List (Nat × Nat) := tl.mats.toList.map fun M => (M.m, M.k)

/-- The range check of a matrix of these rows and columns, at tau combinations. -/
def checkAt (tau : Nat) (p : Nat × Nat) : RangeCheck :=
  rangeCheckOf tau { m := p.1, k := p.2 }

/-- **Of a smallness test the range checks read the matrices' rows and columns, and tau.** -/
theorem checksH_of_fields {tl : HTailF2} {mk : List (Nat × Nat)} {tau : Nat}
    (h1 : sizesOf tl = mk) (h2 : tl.tau = tau) : rangeChecksH [tl] = mk.map (checkAt tau) := by
  unfold rangeChecksH
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, ← h1, h2]
  unfold sizesOf
  rw [List.map_map]
  rfl

/-! ## 2 The range checks of a request, from these fields: at all values -/

/-- **Forward, by field of X, at all sizes and numbers of combinations.** -/
theorem rangeChecks_of_sizes {X : Public} (h4 : X.p4 = true) (hN : X.NGr = 12)
    {sL sA sH : List (Nat × Nat)} {tL tA tH : Nat}
    (hL : ∀ g, g < 12 → ∃ hp, X.G[g]? = some hp ∧ sizesOf hp.tl = sL ∧ hp.tl.tau = tL)
    (hA : ∀ g, g < 12 → ∃ a, X.A[g]? = some a ∧ sizesOf a.seam.tl = sA ∧ a.seam.tl.tau = tA)
    (hH : sizesOf X.H.tl = sH ∧ X.H.tl.tau = tH) :
    rangeChecksOf X =
      some ((List.range 12).flatMap (fun _ => sL.map (checkAt tL) ++ sA.map (checkAt tA)) ++
        sH.map (checkAt tH)) := by
  rw [rangeChecksOf_of h4 fun g hg => by
    rw [hN] at hg
    obtain ⟨hp, e1, _⟩ := hL g hg
    obtain ⟨a, e2, _⟩ := hA g hg
    rw [e1, e2]
    exact ⟨rfl, rfl⟩, hN, checksH_of_fields hH.1 hH.2]
  congr 2
  refine List.flatMap_congr fun g hg => ?_
  obtain ⟨hp, e1, c1, d1⟩ := hL g (List.mem_range.1 hg)
  obtain ⟨a, e2, c2, d2⟩ := hA g (List.mem_range.1 hg)
  unfold pairAt
  rw [e1, e2]
  show rangeChecksH ([hp.tl] ++ [a.seam.tl]) = _
  rw [checksH_append, checksH_of_fields c1 d1, checksH_of_fields c2 d2]

/-! ## 3 At the written list, and beside it -/

/-- The written rows and columns: read off the written list's own members. -/
def sizesL : List (Nat × Nat) := (checksPair.take 9).map fun c => (c.rows, c.columns)

def sizesA : List (Nat × Nat) := (checksPair.drop 9).map fun c => (c.rows, c.columns)

def sizesH : List (Nat × Nat) := checksHead.map fun c => (c.rows, c.columns)

set_option maxRecDepth 1000000 in
/-- At the written sizes and 128 combinations the list is the written one. -/
theorem sizes_full :
    (List.range 12).flatMap (fun _ => sizesL.map (checkAt 128) ++ sizesA.map (checkAt 128)) ++
      sizesH.map (checkAt 128) = checksFull := by
  decide +kernel

/-- **rangeChecksOf X = some checksFull, UNDER HYPOTHESES BY FIELD OF X.** -/
theorem rangeChecks_of_fields {X : Public} (h4 : X.p4 = true) (hN : X.NGr = 12)
    (hL : ∀ g, g < 12 → ∃ hp, X.G[g]? = some hp ∧ sizesOf hp.tl = sizesL ∧ hp.tl.tau = 128)
    (hA : ∀ g, g < 12 →
      ∃ a, X.A[g]? = some a ∧ sizesOf a.seam.tl = sizesA ∧ a.seam.tl.tau = 128)
    (hH : sizesOf X.H.tl = sizesH ∧ X.H.tl.tau = 128) : rangeChecksOf X = some checksFull := by
  rw [rangeChecks_of_sizes h4 hN hL hA hH, sizes_full]

set_option maxRecDepth 1000000 in
/-- Beside the written values the list is another: one combination fewer at the head's test; one
column more in the layers' first matrix. -/
theorem sizes_bent :
    ((List.range 12).flatMap (fun _ => sizesL.map (checkAt 128) ++ sizesA.map (checkAt 128)) ++
      sizesH.map (checkAt 127) ≠ checksFull) ∧
    ((List.range 12).flatMap (fun _ =>
        ((sizesL.headD (0, 0)).1, (sizesL.headD (0, 0)).2 + 1) :: sizesL.tail |>.map (checkAt 128)
          |>.append (sizesA.map (checkAt 128))) ++
      sizesH.map (checkAt 128) ≠ checksFull) := by
  decide +kernel

/-- **THE BENT TWIN**: the same public part but for one combination fewer at the head's smallness
test: its range checks are NOT the written list. -/
theorem rangeChecks_bent {X : Public} (h4 : X.p4 = true) (hN : X.NGr = 12)
    (hL : ∀ g, g < 12 → ∃ hp, X.G[g]? = some hp ∧ sizesOf hp.tl = sizesL ∧ hp.tl.tau = 128)
    (hA : ∀ g, g < 12 →
      ∃ a, X.A[g]? = some a ∧ sizesOf a.seam.tl = sizesA ∧ a.seam.tl.tau = 128)
    (hH : sizesOf X.H.tl = sizesH ∧ X.H.tl.tau = 127) : rangeChecksOf X ≠ some checksFull := by
  rw [rangeChecks_of_sizes h4 hN hL hA hH]
  exact fun e => sizes_bent.1 (Option.some.inj e)

/-! ## 4 What the bent twin does not bite -/

/-- The list at the written sizes, with tH combinations at the head's test. -/
def checksAtHead (tH : Nat) : List RangeCheck :=
  (List.range 12).flatMap (fun _ => sizesL.map (checkAt 128) ++ sizesA.map (checkAt 128)) ++
    sizesH.map (checkAt tH)

set_option maxRecDepth 1000000 in
/-- **The twin's bend leaves every check's bits as they are**: what the planner's fourth gate reads
is the same at 127 combinations as at 128. At 129 it is not. -/
theorem bits_at_head :
    (checksAtHead 127).map rangeCheckBits = checksFull.map rangeCheckBits ∧
      (checksAtHead 129).map rangeCheckBits ≠ checksFull.map rangeCheckBits := by
  decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.checksH_of_fields
#print axioms Johnson.AtFull.Made.rangeChecks_of_sizes
#print axioms Johnson.AtFull.Made.sizes_full
#print axioms Johnson.AtFull.Made.rangeChecks_of_fields
#print axioms Johnson.AtFull.Made.sizes_bent
#print axioms Johnson.AtFull.Made.rangeChecks_bent
#print axioms Johnson.AtFull.Made.bits_at_head
