-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/Kept/Def.lean: for CornersKept.lean (one folder up): what is evaluated,
a list at a time. Definitions and a small lemma.

  `each_of_getD`: what holds at each number of a list holds of each of its members. `CornersAll lo`:
    the test `Corners` (Corners.lean) says yes at the list's own layout, whichever members are kept.
    Decidable.
  `flagAt`, `CornersIf lo b0 b1`, `cornersAll_of_if`: the same at the choices with given first two
    flags; the four together give all.
Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.Corners

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G

/-- What holds at each number of a list holds of each of its members. -/
theorem each_of_getD {α : Type} (P : α → Prop) (l : List α) (d : α) (n : ℕ) (hl : l.length = n)
    (h : ∀ i < n, P (l.getD i d)) : ∀ x ∈ l, P x := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have h1 := h i (hl ▸ hi)
  rwa [List.getD_eq_getElem _ _ hi] at h1

/-- The test says yes at a list's own layout, whichever members are kept. -/
def CornersAll (lo : List (OracleShape × ℕ)) : Prop :=
  ∀ kb : Fin lo.length → Bool,
    Corners lo (kLay lo kb) (fun i => layAt (sizesM lo kb) i.val)
      (fun i => layAt (sizesZ lo) i.val) kb

instance (lo : List (OracleShape × ℕ)) : Decidable (CornersAll lo) := by
  unfold CornersAll
  infer_instance

/-- Flag number j of a choice; false beyond its length. -/
def flagAt {n : ℕ} (kb : Fin n → Bool) (j : ℕ) : Bool := if h : j < n then kb ⟨j, h⟩ else false

/-- `CornersAll` at the choices with these first two flags. -/
def CornersIf (lo : List (OracleShape × ℕ)) (b0 b1 : Bool) : Prop :=
  ∀ kb : Fin lo.length → Bool, flagAt kb 0 = b0 → flagAt kb 1 = b1 →
    Corners lo (kLay lo kb) (fun i => layAt (sizesM lo kb) i.val)
      (fun i => layAt (sizesZ lo) i.val) kb

instance (lo : List (OracleShape × ℕ)) (b0 b1 : Bool) : Decidable (CornersIf lo b0 b1) := by
  unfold CornersIf
  infer_instance

theorem cornersAll_of_if {lo : List (OracleShape × ℕ)} (h : ∀ b0 b1, CornersIf lo b0 b1) :
    CornersAll lo := fun kb => h _ _ kb rfl rfl

end VerifiableInference.Desc.First.Close
