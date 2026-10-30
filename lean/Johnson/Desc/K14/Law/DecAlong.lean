-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/DecAlong.lean: THE LIBRARY's DECODER WITH A RECORD, ITS COLLISION AND ITS BAD
POINTS MOVE ALONG A MAP OF SEEDS. Theorems; general: no kind, no plan, no code is named.

Two encoded indices that differ in the sample map alone: the same names of answers; a map tr from
the one's seeds to the other's; at corresponding seeds the two samples give ONE matrix. Then at
corresponding records they decode to one table (dec_along), collide together (coll_along), have the
record's row together (recRow_along) and the same bad points (bad_along).

WHY. "What the stored table decodes to" is said at typed data whose seed holds, for each answer, a
point and any element of the field, and elsewhere at the library's own sample, whose factor is
another type: the elements other than 0. The two types of records part; the decoders do not.
What is not claimed. That any two samples of the protocol give one matrix at corresponding seeds.
Nothing on soundness.

-/
import Cb.Ld.LdFoldEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.LdIx
open Cb.Ood

variable {E ι κ J : Type} [Field E] [Fintype J] [Fintype ι] [Fintype κ]

/-- The index with another sample map of the same answers' names. -/
@[reducible] def withSeeds (X : LdIx E ι κ J) (D' : Type) [Fintype D'] [Nonempty D']
    (mat' : D' → X.Z.S → J → E) (err' : ℕ) : LdIx E ι κ J :=
  { X with Z := { D := D', S := X.Z.S, mat := mat', err := err' } }

variable (X : LdIx E ι κ J) (D' : Type) [Fintype D'] [Nonempty D']
  (mat' : D' → X.Z.S → J → E) (err' : ℕ) (tr : X.Z.D → D')

/-- At corresponding seeds the rows' samples answer alike. -/
theorem val_along (h : ∀ ρ, mat' (tr ρ) = X.Z.mat ρ) (ρ : X.Z.D) :
    (X.withSeeds D' mat' err').ZR.val (tr ρ) = X.ZR.val ρ := by
  funext u s
  dsimp only [Sample.val, ZR, Sample.rows, withSeeds]
  rw [h ρ]

/-- **They decode to one table.** -/
theorem dec_along (h : ∀ ρ, mat' (tr ρ) = X.Z.mat ρ) (f : X.Row → ι → E) (ρ : X.Z.D)
    (y : X.Row × X.Z.S → E) :
    (X.withSeeds D' mat' err').dec f (tr ρ, y) = X.dec f (ρ, y) := by
  show decMin _ X.rank X.view (fun _ : Unit => (X.withSeeds D' mat' err').ZR.val (tr ρ)) X.eM ()
      y = decMin _ X.rank X.view (fun _ : Unit => X.ZR.val ρ) X.eM () y
  rw [val_along X D' mat' err' tr h ρ]

/-- **They collide together.** -/
theorem coll_along (h : ∀ ρ, mat' (tr ρ) = X.Z.mat ρ) (f : X.Row → ι → E) (ρ : X.Z.D) :
    (X.withSeeds D' mat' err').Coll f (tr ρ) ↔ X.Coll f ρ := by
  show Clash _ (fun _ : Unit => (X.withSeeds D' mat' err').ZR.val (tr ρ)) () ↔
    Clash _ (fun _ : Unit => X.ZR.val ρ) ()
  rw [val_along X D' mat' err' tr h ρ]
  exact Iff.rfl

omit [Fintype ι] [Fintype κ] in
/-- They have the record's row together. -/
theorem recRow_along (h : ∀ ρ, mat' (tr ρ) = X.Z.mat ρ) (ρ : X.Z.D) (y : X.Row × X.Z.S → E)
    (γ : Fin X.v → E) (u : κ → E) :
    (X.withSeeds D' mat' err').RecRow (tr ρ, y) γ u ↔ X.RecRow (ρ, y) γ u := by
  show (fun s => ∑ j, mat' (tr ρ) s j * X.msg u j) = X.tgt (ρ, y) γ ↔
    (fun s => ∑ j, X.Z.mat ρ s j * X.msg u j) = X.tgt (ρ, y) γ
  rw [h ρ]

/-- **They have the same bad points.** -/
theorem bad_along (h : ∀ ρ, mat' (tr ρ) = X.Z.mat ρ) (f : X.Row → ι → E) (ρ : X.Z.D)
    (y : X.Row × X.Z.S → E) (e' : ℕ) (γ : Fin X.v → E) :
    (X.withSeeds D' mat' err').Bad f (tr ρ, y) e' γ ↔ X.Bad f (ρ, y) e' γ := by
  unfold Bad Wrong
  simp only [dec_along X D' mat' err' tr h f ρ y, recRow_along X D' mat' err' tr h ρ y γ]
  exact Iff.rfl

end Cb.LdIx
