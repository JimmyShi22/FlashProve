-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/OkOfShapes.lean: two further tests on the plain data of a file's three chains
(`shapesFit`, `sealBare`, OnBytes/Maker/ViewTests.lean) say yes wherever the makers' test `okAt`
(OnBytes/Maker/Files.lean) does. Statements and proofs.

Why. The theorems on a file's typing take the three tests as three premises. `sealBare` follows
from `Three.Whole.fits`, a part of `okAt` (`sealBare_of_fits`, OnBytes/Maker/ReadFitsOf.lean).
`shapesFit` compares, tree by tree, the shape in the rounds' data with the shape in the data's
table. Both are made of the same three lists of rounds; what is needed beside is that the two ways
of counting the first two chains' trees agree: the test `countsFit`, also a part of `okAt`.

Main names:
  `shapesFit_of_counts`: from `countsFit`. `shapesFit_of_fits`: from `Three.Whole.fits` (by
    `countsFit_of_fits`, OnBytes/Maker/OkOfFormat.lean).
  `shapesFit_of_okAt`, `sealBare_of_okAt`: from `okAt a (some R) = true`.
Limits: at data of the form `Three.Whole.of R₁ R₂ R₃` alone. Nothing says that `okAt` says yes at
any file.
-/
import OnBytes.Maker.OkOfLeft
import OnBytes.Maker.ViewTests
import OnBytes.Maker.ReadFitsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker
open OnBytes.Three (rootsIn treesOfChain)
open OnBytes.Params (Rounds)

/-- **The test `shapesFit` on the data of three lists of rounds follows from the test `countsFit`**:
the table's rows and the rounds' data are made of the same lists. -/
theorem shapesFit_of_counts (a : ℕ) {R₁ R₂ R₃ : Rounds}
    (hc : countsFit a (Three.Whole.of R₁ R₂ R₃) = true) :
    shapesFit a (Three.Whole.of R₁ R₂ R₃) = true := by
  unfold countsFit at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  have t₁ : (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).t₁ = rootsIn R₁ := hc.1
  have t₂ : (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).t₂ = rootsIn R₂ := hc.2
  have lA : (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 0 0
      (Three.Whole.of R₁ R₂ R₃).ds₁).length = rootsIn R₁ := trees_count _ _ _ _ _ _ _ _ R₁
  have lB : (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 1 (rootsIn R₁)
      (Three.Whole.of R₁ R₂ R₃).ds₂).length = rootsIn R₂ := trees_count _ _ _ _ _ _ _ _ R₂
  have tab : (Three.Whole.of R₁ R₂ R₃).table =
      treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 0 0 (Three.Whole.of R₁ R₂ R₃).ds₁ ++
      (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 1 (rootsIn R₁) (Three.Whole.of R₁ R₂ R₃).ds₂ ++
      treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 2 (rootsIn R₁ + rootsIn R₂)
        (Three.Whole.of R₁ R₂ R₃).ds₃) := rfl
  unfold shapesFit
  refine List.all_eq_true.2 fun j _ => ?_
  rw [beq_iff_eq]
  unfold WholeD.shape
  rw [t₁, t₂]
  by_cases h1 : j < rootsIn R₁
  · rw [if_pos h1, treeShT_flat]
    have fd := flat_dropLast (Three.Whole.of R₁ R₂ R₃).ds₁ j (by
      have : ((((Three.Whole.of R₁ R₂ R₃).ds₁.dropLast.map rdtOf).map (·.trees.length)).sum) =
          rootsIn R₁ := t₁
      rw [this]
      exact h1)
    have fd' : ((WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₁.flatMap (·.trees))[j]? =
        ((Three.Whole.of R₁ R₂ R₃).ds₁.flatMap (·.trees))[j]? := fd
    rw [fd', ← treesOfChain_shapes (Three.Whole.of R₁ R₂ R₃).opens 0 0, List.getElem?_map, tab,
      List.getElem?_append_left (by rw [lA]; exact h1)]
  · rw [if_neg h1]
    by_cases h2 : j - rootsIn R₁ < rootsIn R₂
    · rw [if_pos h2, treeShT_flat]
      have e2 : (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₂.flatMap (·.trees) =
          (Three.Whole.of R₁ R₂ R₃).ds₂.flatMap (·.trees) := by
        show ((Three.Whole.of R₁ R₂ R₃).ds₂.map rdtOf).flatMap (·.trees) = _
        rw [List.flatMap_map]
        rfl
      rw [e2, ← treesOfChain_shapes (Three.Whole.of R₁ R₂ R₃).opens 1 (rootsIn R₁),
        List.getElem?_map, tab, List.getElem?_append_right (by rw [lA]; omega), lA,
        List.getElem?_append_left (by rw [lB]; exact h2)]
    · rw [if_neg h2, treeShT_flat]
      have e3 : (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₃.flatMap (·.trees) =
          (Three.Whole.of R₁ R₂ R₃).ds₃.flatMap (·.trees) := by
        show ((Three.Whole.of R₁ R₂ R₃).ds₃.map rdtOf).flatMap (·.trees) = _
        rw [List.flatMap_map]
        rfl
      rw [e3, ← treesOfChain_shapes (Three.Whole.of R₁ R₂ R₃).opens 2 (rootsIn R₁ + rootsIn R₂),
        List.getElem?_map, tab, List.getElem?_append_right (by rw [lA]; omega), lA,
        List.getElem?_append_right (by rw [lB]; omega), lB]

/-- The same from `Three.Whole.fits`. -/
theorem shapesFit_of_fits (a : ℕ) {R₁ R₂ R₃ : Rounds} {n : ℕ}
    (hf : Three.Whole.fits R₁ R₂ R₃ n = true) : shapesFit a (Three.Whole.of R₁ R₂ R₃) = true :=
  shapesFit_of_counts a (countsFit_of_fits a hf)

/-- **Where the makers' test `okAt` says yes, so do `shapesFit` and `sealBare`.** -/
theorem shapesFit_of_okAt {a : ℕ} {R : Rounds × Rounds × Rounds} (h : okAt a (some R) = true) :
    shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true :=
  shapesFit_of_counts a (okAt_parts h).counts

theorem sealBare_of_okAt {a : ℕ} {R : Rounds × Rounds × Rounds} (h : okAt a (some R) = true) :
    sealBare (Three.Whole.of R.1 R.2.1 R.2.2) = true :=
  sealBare_of_fits (okAt_parts h).fits

end OnBytes.Maker

#print axioms OnBytes.Maker.shapesFit_of_counts
#print axioms OnBytes.Maker.shapesFit_of_fits
#print axioms OnBytes.Maker.shapesFit_of_okAt
#print axioms OnBytes.Maker.sealBare_of_okAt
