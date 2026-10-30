-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchWireOK.lean: two lemmas on the wire records of an `BatchProtocol`: a bound on `RoundsQueryLayout.maxDepth`
(Iop/BatchWireOf.lean) gives `RoundsQueryLayout.DepthLe` (`depthLe_of_maxDepth_le`), and the enumeration of
`Unit` satisfies `Enum.OK` (`enumUnit_ok`). (Words of this library: lean/GLOSSARY.md.)

Notation: `Enum β : Type` (Iop/Wire.lean): an explicit enumeration of a finite non-empty type; its
fields: `n : ℕ`, `e : Fin (n + 1) → β`; `Enum.OK e : Prop` (there): `Function.Bijective e.e`.
-/
import Iop.BatchWireOf
import Iop.WireOK

namespace Iop
open Prob

namespace BatchWireOK



theorem depthLe_of_maxDepth_le {lam K : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (d : ℕ),
      RoundsQueryLayout.maxDepth s A W ≤ d → RoundsQueryLayout.DepthLe d s A W
  | [], _, _, _, _ => trivial
  | _ :: s, (_, A), (_, W), d, h =>
      ⟨⟨le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h,
          le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h⟩,
        depthLe_of_maxDepth_le s A W d (le_trans (le_max_right _ _) h)⟩

variable {X : Type} {E : ExtSpec}


theorem enumUnit_ok : (⟨0, fun _ => ()⟩ : Enum Unit).OK :=
  ⟨fun a b _ => (Subsingleton.elim (α := Fin 1) a b), fun _ => ⟨(0 : Fin 1), rfl⟩⟩

end BatchWireOK

end Iop
