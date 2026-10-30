-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/StageOf.lean: the data of the three stages of a file (OnBytes/Maker/Stage.lean) from
the three chains of the file as plain data (OnBytes/Three/Data.lean, `Whole`). Definitions alone.

  `leftAfter W c`: the trees that the chains up to c have sent and a chain behind c opens, each with
    its number over the whole file and its depth, in the order of the table.
  `stage₁`, `stage₂`, `stage₃`: the three stages' data. The first has the first chain without its
    seal. What one stage leaves is what the next has at hand, by the same term; the third leaves
    nothing.

What is not claimed. No law is stated here. a: the stored table's depth, the caller's letter
(OnBytes/Maker/WholeOf.lean, `storedFit`).


-/
import OnBytes.Maker.Stage
import OnBytes.Maker.WholeOf

set_option autoImplicit false

namespace OnBytes.Maker

/-- The trees that the chains up to c have sent and a chain behind c opens. -/
def leftAfter (W : Three.Whole) (c : ℕ) : List LeftT :=
  (W.table.zipIdx.filter fun t =>
    decide (t.1.chain ≤ c) && t.1.openedAt.any fun o => decide (c < o.1)).map fun t =>
      ⟨t.2, t.1.shape.a⟩

def stage₁ (a : ℕ) (W : Three.Whole) : StageD :=
  ⟨a, 0, [], W.stretch₁.map rdtOf, W.key 0, leftAfter W 0⟩

def stage₂ (a : ℕ) (W : Three.Whole) : StageD :=
  ⟨a, W.t₁, leftAfter W 0, W.ds₂.map rdtOf, W.key 1, leftAfter W 1⟩

def stage₃ (a : ℕ) (W : Three.Whole) : StageD :=
  ⟨a, W.t₁ + W.t₂, leftAfter W 1, W.ds₃.map rdtOf, W.key 2, []⟩

/-- What the first stage leaves is what the second has at hand, and so for the second and the
third. -/
example (a : ℕ) (W : Three.Whole) : (stage₁ a W).Eo = (stage₂ a W).Ei := rfl
example (a : ℕ) (W : Three.Whole) : (stage₂ a W).Eo = (stage₃ a W).Ei := rfl

end OnBytes.Maker
