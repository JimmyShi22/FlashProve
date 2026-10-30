-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/Drawn/Def.lean: for LayoutDrawn.lean (one folder up): what is
evaluated, a list at a time. Definitions.

  `membersOf`, `stOf`, `posOf`, `AgreesWith`, `LayoutAgrees`, `LayoutAll`: see LayoutDrawn.lean's
    head.
Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.Kept.Def

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G

/-- The numbers of a list's members: the messages with a main row, in the list's order. -/
def membersOf (lo : List (OracleShape × ℕ)) : List (Fin lo.length) :=
  (List.finRange lo.length).filter fun i => (lo.get i).1.mainRows != 0

/-- A statement with the list's messages and one group: the members, with their flags. -/
def stOf (lo : List (OracleShape × ℕ)) (kb : Fin lo.length → Bool) : Statement :=
  { oracles := (lo.map fun x => ({ shape := x.1 } : Oracle)).toArray
    groups := #[{ code := 0, members := ((membersOf lo).map fun i => i.val).toArray
                  kept := ((membersOf lo).map kb).toArray }] }

/-- Where a message stands among the members. -/
def posOf (lo : List (OracleShape × ℕ)) (i : Fin lo.length) : ℕ :=
  ((membersOf lo).filter fun j => decide (j < i)).length

/-- What a layout says against what Corners.lean's definitions say: the number of row variables; no
variable for the mask rows; each member's first main row, if it is not kept; each member's first
mask row, if it has one. -/
def AgreesWith (lo : List (OracleShape × ℕ)) (kb : Fin lo.length → Bool) (L : GroupLayout) : Prop :=
  L.k = kLay lo kb ∧ L.h = 0 ∧
    (∀ i : Fin lo.length, (lo.get i).1.mainRows ≠ 0 → kb i = false →
      L.mainFirst.getD (posOf lo i) none = some (layAt (sizesM lo kb) i.val)) ∧
    (∀ i : Fin lo.length, (lo.get i).1.mainRows ≠ 0 → (lo.get i).1.maskRows ≠ 0 →
      L.maskFirst.getD (posOf lo i) none = some (layAt (sizesZ lo) i.val))

instance (lo : List (OracleShape × ℕ)) (kb : Fin lo.length → Bool) (L : GroupLayout) :
    Decidable (AgreesWith lo kb L) := by
  unfold AgreesWith
  refine @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
    (@instDecidableAnd _ _ ?_ ?_))
  · exact Nat.decidableForallFin _
  · exact Nat.decidableForallFin _

/-- `Statement.layout` itself, at the statement made of the list and the flags. -/
def LayoutAgrees (lo : List (OracleShape × ℕ)) (kb : Fin lo.length → Bool) : Prop :=
  match (stOf lo kb).layout 0 with
  | some L => AgreesWith lo kb L
  | none => False

instance (lo : List (OracleShape × ℕ)) (kb : Fin lo.length → Bool) :
    Decidable (LayoutAgrees lo kb) := by
  unfold LayoutAgrees
  split <;> infer_instance

/-- So it is at a list, whichever members are kept. -/
def LayoutAll (lo : List (OracleShape × ℕ)) : Prop :=
  ∀ kb : Fin lo.length → Bool, LayoutAgrees lo kb

instance (lo : List (OracleShape × ℕ)) : Decidable (LayoutAll lo) := by
  unfold LayoutAll
  infer_instance

/-- `LayoutAll` at the choices with these first two flags. -/
def LayoutIf (lo : List (OracleShape × ℕ)) (b0 b1 : Bool) : Prop :=
  ∀ kb : Fin lo.length → Bool, flagAt kb 0 = b0 → flagAt kb 1 = b1 → LayoutAgrees lo kb

instance (lo : List (OracleShape × ℕ)) (b0 b1 : Bool) : Decidable (LayoutIf lo b0 b1) := by
  unfold LayoutIf
  infer_instance

theorem layoutAll_of_if {lo : List (OracleShape × ℕ)} (h : ∀ b0 b1, LayoutIf lo b0 b1) :
    LayoutAll lo := fun kb => h _ _ kb rfl rfl

end VerifiableInference.Desc.First.Close
