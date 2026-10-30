-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/SeatsNamedC.lean: a cheap test with code for `SeatsNamed` (Johnson/Desc/Sound/ReadAt.lean) at
the seats off the layout. One definition and one theorem.

Why. `SeatsNamed arr N s seat` asks, of every number that a segment's seats name within its sizes,
that it has just one tenant in that segment's own group. The plain test (P5J/SeatsNamedB.lean) walks
every row of symbols and every column of every matrix. At the seats off the layout the number hangs
on the matrix alone: under `laidThere` the theorem `Meaning.seat_of_laidThere`
(Johnson/Goal/Meaning/HidSeatsOf.lean) says that the seat's first component is
`num (ownerK (labAt X k μ)) A.message`, A the array that the label names. So it is enough to ask the
atom `namedOnce` once a matrix.
  `seatsNamedC X s layout num arr N`: over the 25 segments and each one's matrices: the array that the
    label names is there in the layout, and its message's number is named once in the segment's
    group.
  **`seatsNamed_of_C`**: `laidThere`, a yes of the test, and "no segment from 25 on has a matrix" (hK)
    give `SeatsNamed` at `Meaning.seatBy (Meaning.fLay layout num) X s`.

Limits. One way alone: a no of the test says nothing. The test has run nowhere. The three premises
are on public letters alone; none is shown here. Nothing on soundness or on hiding.

The theorem's letters X, s, layout, num, arr and N are implicit arguments, and `Meaning.seatBy` is
written in full, since the library has two functions of that name.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.ReadAt
import Johnson.Goal.Meaning.HidSeatsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J

open OnBytes
open OnBytes.Params (ReqLayout)
open Cb.Pv.Tail (Size)
open VerifiableInference.Desc (arrayOf)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (SeatsNamed namedOnce)
open Meaning (laidThere fLay nameOf labAt ownerK ownerA seat_of_laidThere)

/-- The cheap test for `SeatsNamed` at the seats off the layout: once a matrix. -/
def seatsNamedC (X : Model.Verify.Public) (s : ℕ → Size) (layout : ReqLayout) (num arr : ℕ → ℕ → ℕ)
    (N : Numbers) : Bool :=
  (List.range 25).all fun k => (List.range (s k).NM).all fun a =>
    match arrayOf layout (ownerK (labAt X k a)) (nameOf (ownerA (labAt X k a))) with
    | none => false
    | some A => namedOnce arr N k (num (ownerK (labAt X k a)) A.message)

/-- **Under `laidThere`, a yes of the cheap test, and no matrix from segment 25 on, give the
condition at the seats off the layout.** -/
theorem seatsNamed_of_C {X : Model.Verify.Public} {s : ℕ → Size} {layout : ReqLayout}
    {num arr : ℕ → ℕ → ℕ} {N : Numbers} (T : laidThere X s layout = true)
    (hC : seatsNamedC X s layout num arr N = true) (hK : ∀ k, 25 ≤ k → (s k).NM = 0) :
    SeatsNamed arr N s (Meaning.seatBy (fLay layout num) X s) := by
  intro k μ r c hr hc
  by_cases hk : k < 25
  · obtain ⟨A, x, hA, -, -, -, hseat⟩ := seat_of_laidThere T num hk μ hr hc
    rw [hseat]
    unfold seatsNamedC at hC
    have C2 := List.all_eq_true.1 (List.all_eq_true.1 hC k (List.mem_range.2 hk)) μ.val
      (List.mem_range.2 μ.isLt)
    simp only [hA] at C2
    exact C2
  · have h0 := hK k (Nat.le_of_not_lt hk)
    exact absurd (h0 ▸ μ.isLt : μ.val < 0) (Nat.not_lt_zero _)

end P5J

#print axioms P5J.seatsNamed_of_C
