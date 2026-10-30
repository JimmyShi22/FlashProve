-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/DryKeyTests.lean: the tests on public data that stand as premises where the key file's
protocol is tied to the verifier on bytes, at the written dry lists of Johnson/G/DryKeyLit.lean, at
the full-size and at the small example: each as a theorem by an evaluation in Lean's kernel.

The tests: `OnBytes.Maker.okAt` and its eight parts (OnBytes/Maker/Files.lean), `shapesFit`,
`sealBare` (OnBytes/Maker/ViewTests.lean), `saltsFit` (OnBytes/Maker/TablesRow.lean). Each is a
function of the three dry lists, the stored table's depth and the number of bytes of a salt. All but
one read `OnBytes.Three.Whole.of` of the lists, at which the kernel runs out of stack; each proof
first rewrites it to a twin (Johnson/G/WholeTwin.lean, `whole_eq`). Proofs.
Main names:
  `fits_keyFull`, `storedFit_keyFull`, `countsFit_keyFull`, `workFit_keyFull`, `depthFit_keyFull`,
    `runFit_keyFull`, `someFit_keyFull`, `rowFit_keyFull`: the eight; `okAt_keyFull`: together.
  `shapesFit_keyFull`, `sealBare_keyFull`, `saltsFit_keyFull`: the others. `controls_keyFull`: at
    the depth 31, and at salts of 41 bytes, two of the tests say no; `controlRoots_keyFull`: with
    one root a message allowed, the first test says no.
  The like with Small (depth 23; the control at 22).
Limits: the theorems speak of the written lists. That these are what `OnBytes.Maker.dryKey` returns
at the planner's answer at the shipped public files and the key of zeros is no theorem. At the full
size no test that a build runs holds it. The tests say that the lists fit the makers' map, not that
they are the file's: with the entries' draws and sizes changed they would still say yes. Most of the
tests have no control here. Nothing on soundness.

-/
import Johnson.G.DryKeyLit
import Johnson.G.WholeTwin
import OnBytes.Maker.Files
import OnBytes.Maker.ViewTests
import OnBytes.Maker.TablesRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

open OnBytes OnBytes.Maker

/-! ## The full-size example: the stored table's depth 32; salts of 40 bytes -/

set_option maxRecDepth 1000000 in
/-- The first of the makers' eight tests. -/
theorem fits_keyFull :
    Three.Whole.fits dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2 2 = true := by
  unfold Three.Whole.fits
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem storedFit_keyFull : storedFit 32 (wholeAt (some dryKeyFull)) = true := by
  show storedFit 32 (Three.Whole.of dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2) = true
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem countsFit_keyFull : countsFit 32 (wholeAt (some dryKeyFull)) = true := by
  show countsFit 32 (Three.Whole.of dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2) = true
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem workFit_keyFull : (WholeD.of 32 (wholeAt (some dryKeyFull))).workFit = true := by
  show (WholeD.of 32 (Three.Whole.of dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2)).workFit = true
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem depthFit_keyFull : (WholeD.of 32 (wholeAt (some dryKeyFull))).depthFit = true := by
  show (WholeD.of 32 (Three.Whole.of dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2)).depthFit = true
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem runFit_keyFull : (WholeD.of 32 (wholeAt (some dryKeyFull))).runFit = true := by
  show (WholeD.of 32 (Three.Whole.of dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2)).runFit = true
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem someFit_keyFull : someFit dryKeyFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem rowFit_keyFull : rowFitAt 32 (wholeAt (some dryKeyFull)) = true := by
  show rowFitAt 32 (Three.Whole.of dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2) = true
  rw [whole_eq]
  decide +kernel

/-- The makers' eight tests together. -/
theorem okAt_keyFull : okAt 32 (some dryKeyFull) = true := by
  simp only [okAt, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨fits_keyFull, storedFit_keyFull⟩, countsFit_keyFull⟩, workFit_keyFull⟩,
    depthFit_keyFull⟩, runFit_keyFull⟩, someFit_keyFull⟩, rowFit_keyFull⟩

set_option maxRecDepth 1000000 in
theorem shapesFit_keyFull : shapesFit 32 (wholeAt (some dryKeyFull)) = true := by
  show shapesFit 32 (Three.Whole.of dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2) = true
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem sealBare_keyFull : sealBare (wholeAt (some dryKeyFull)) = true := by
  show sealBare (Three.Whole.of dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2) = true
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem saltsFit_keyFull : saltsFit 40 (wholeAt (some dryKeyFull)) = true := by
  show saltsFit 40 (Three.Whole.of dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2) = true
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with one root a message allowed, the first test says no. -/
theorem controlRoots_keyFull :
    Three.Whole.fits dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2 1 = false := by
  unfold Three.Whole.fits
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Controls: at another depth, and at salts of another number of bytes, the tests say no. -/
theorem controls_keyFull :
    (storedFit 31 (wholeAt (some dryKeyFull)), saltsFit 41 (wholeAt (some dryKeyFull))) =
      (false, false) := by
  show (storedFit 31 (Three.Whole.of dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2),
    saltsFit 41 (Three.Whole.of dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2)) =
    (false, false)
  rw [whole_eq]
  decide +kernel

/-! ## The small example: the stored table's depth 23; salts of 40 bytes -/

set_option maxRecDepth 1000000 in
/-- The first of the makers' eight tests. -/
theorem fits_keySmall :
    Three.Whole.fits dryKeySmall.1 dryKeySmall.2.1 dryKeySmall.2.2 2 = true := by
  unfold Three.Whole.fits
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem storedFit_keySmall : storedFit 23 (wholeAt (some dryKeySmall)) = true := by
  show storedFit 23 (Three.Whole.of dryKeySmall.1 dryKeySmall.2.1 dryKeySmall.2.2) = true
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem countsFit_keySmall : countsFit 23 (wholeAt (some dryKeySmall)) = true := by
  show countsFit 23 (Three.Whole.of dryKeySmall.1 dryKeySmall.2.1 dryKeySmall.2.2) = true
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem workFit_keySmall : (WholeD.of 23 (wholeAt (some dryKeySmall))).workFit = true := by
  show (WholeD.of 23 (Three.Whole.of dryKeySmall.1 dryKeySmall.2.1 dryKeySmall.2.2)).workFit = true
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem depthFit_keySmall : (WholeD.of 23 (wholeAt (some dryKeySmall))).depthFit = true := by
  show (WholeD.of 23 (Three.Whole.of dryKeySmall.1 dryKeySmall.2.1 dryKeySmall.2.2)).depthFit = true
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem runFit_keySmall : (WholeD.of 23 (wholeAt (some dryKeySmall))).runFit = true := by
  show (WholeD.of 23 (Three.Whole.of dryKeySmall.1 dryKeySmall.2.1 dryKeySmall.2.2)).runFit = true
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem someFit_keySmall : someFit dryKeySmall = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem rowFit_keySmall : rowFitAt 23 (wholeAt (some dryKeySmall)) = true := by
  show rowFitAt 23 (Three.Whole.of dryKeySmall.1 dryKeySmall.2.1 dryKeySmall.2.2) = true
  rw [whole_eq]
  decide +kernel

/-- The makers' eight tests together. -/
theorem okAt_keySmall : okAt 23 (some dryKeySmall) = true := by
  simp only [okAt, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨fits_keySmall, storedFit_keySmall⟩, countsFit_keySmall⟩, workFit_keySmall⟩,
    depthFit_keySmall⟩, runFit_keySmall⟩, someFit_keySmall⟩, rowFit_keySmall⟩

set_option maxRecDepth 1000000 in
theorem shapesFit_keySmall : shapesFit 23 (wholeAt (some dryKeySmall)) = true := by
  show shapesFit 23 (Three.Whole.of dryKeySmall.1 dryKeySmall.2.1 dryKeySmall.2.2) = true
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem sealBare_keySmall : sealBare (wholeAt (some dryKeySmall)) = true := by
  show sealBare (Three.Whole.of dryKeySmall.1 dryKeySmall.2.1 dryKeySmall.2.2) = true
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem saltsFit_keySmall : saltsFit 40 (wholeAt (some dryKeySmall)) = true := by
  show saltsFit 40 (Three.Whole.of dryKeySmall.1 dryKeySmall.2.1 dryKeySmall.2.2) = true
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with one root a message allowed, the first test says no. -/
theorem controlRoots_keySmall :
    Three.Whole.fits dryKeySmall.1 dryKeySmall.2.1 dryKeySmall.2.2 1 = false := by
  unfold Three.Whole.fits
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Controls: at another depth, and at salts of another number of bytes, the tests say no. -/
theorem controls_keySmall :
    (storedFit 22 (wholeAt (some dryKeySmall)), saltsFit 41 (wholeAt (some dryKeySmall))) =
      (false, false) := by
  show (storedFit 22 (Three.Whole.of dryKeySmall.1 dryKeySmall.2.1 dryKeySmall.2.2),
    saltsFit 41 (Three.Whole.of dryKeySmall.1 dryKeySmall.2.1 dryKeySmall.2.2)) =
    (false, false)
  rw [whole_eq]
  decide +kernel

end Johnson.G

#print axioms Johnson.G.fits_keyFull
#print axioms Johnson.G.storedFit_keyFull
#print axioms Johnson.G.countsFit_keyFull
#print axioms Johnson.G.workFit_keyFull
#print axioms Johnson.G.depthFit_keyFull
#print axioms Johnson.G.runFit_keyFull
#print axioms Johnson.G.someFit_keyFull
#print axioms Johnson.G.rowFit_keyFull
#print axioms Johnson.G.okAt_keyFull
#print axioms Johnson.G.shapesFit_keyFull
#print axioms Johnson.G.sealBare_keyFull
#print axioms Johnson.G.saltsFit_keyFull
#print axioms Johnson.G.controlRoots_keyFull
#print axioms Johnson.G.controls_keyFull
#print axioms Johnson.G.fits_keySmall
#print axioms Johnson.G.storedFit_keySmall
#print axioms Johnson.G.countsFit_keySmall
#print axioms Johnson.G.workFit_keySmall
#print axioms Johnson.G.depthFit_keySmall
#print axioms Johnson.G.runFit_keySmall
#print axioms Johnson.G.someFit_keySmall
#print axioms Johnson.G.rowFit_keySmall
#print axioms Johnson.G.okAt_keySmall
#print axioms Johnson.G.shapesFit_keySmall
#print axioms Johnson.G.sealBare_keySmall
#print axioms Johnson.G.saltsFit_keySmall
#print axioms Johnson.G.controlRoots_keySmall
#print axioms Johnson.G.controls_keySmall
