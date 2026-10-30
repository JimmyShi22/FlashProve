-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Local.lean: a lemma on lists. If `f` gives `none` wherever `p` is false, then the first
result of `f` (`List.findSome?`) is the same in a list and in the list filtered by `p`
(`findSome_filter`).
-/
import Compile.Ser
import Compile.Spec
import Mathlib.Logic.Equiv.Fin.Basic
import Rom.Family

noncomputable section

namespace Compile
open Iop Rom

variable {I X : Type} {lam : ℕ}

theorem findSome_filter {α β : Type} (f : α → Option β)
    (p : α → Bool) (h : ∀ a, p a = false → f a = none) :
    ∀ l : List α, (l.filter p).findSome? f = l.findSome? f
  | [] => rfl
  | a :: l => by
      cases hp : p a
      · simp [hp, h a hp, findSome_filter f p h l]
      · simp [hp, List.findSome?_cons, findSome_filter f p h l]

end Compile
