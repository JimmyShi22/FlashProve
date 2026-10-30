-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/CostV.lean: weighted query bounds in which the weight of a query may depend on its answer:
`OComp.CostBoundV` (Rom/SpecOverOneA.lean) under `pure`, `bind`, `map` and for a weight that is
nowhere larger (`CostBoundV.weight`). `CostBoundV.mono` (a larger bound) and
`CostBoundV.of_costBoundAt` (from a weight that does not depend on the answer) are in
Rom/OverOneA.lean.

Limits: nothing on any program or rule.
-/
import Rom.OverOneA

set_option autoImplicit false

namespace Rom

variable {S : OSpec} {α β : Type} {w w' : (o : S.ι) → S.Dom o → S.Rng o → ℕ}

theorem OComp.CostBoundV.pure (a : α) (t : ℕ) : (OComp.pure a : OComp S α).CostBoundV w t := trivial

/-- Bounds on the costs of two parts add up. -/
theorem OComp.CostBoundV.bind {g : α → OComp S β} {t : ℕ} (hg : ∀ a, (g a).CostBoundV w t) :
    ∀ {c : OComp S α} {s : ℕ}, c.CostBoundV w s → (c.bind g).CostBoundV w (s + t)
  | .pure a, _, _ => OComp.CostBoundV.mono (hg a) (Nat.le_add_left _ _)
  | .sample _ k, _, h => fun r => OComp.CostBoundV.bind hg (c := k r) (h r)
  | .query _ _ k, _, h =>
    fun r => let ⟨t', h1, h2⟩ := h r; ⟨t' + t, by omega, OComp.CostBoundV.bind hg (c := k r) h2⟩

/-- a function of the output costs nothing -/
theorem OComp.CostBoundV.map {c : OComp S α} {s : ℕ} (h : c.CostBoundV w s) (f : α → β) :
    (c.bind fun a => .pure (f a)).CostBoundV w s :=
  OComp.CostBoundV.bind (g := fun a => (.pure (f a) : OComp S β)) (t := 0) (fun _ => trivial) h

/-- a weight that is nowhere larger -/
theorem OComp.CostBoundV.weight (hw : ∀ o q r, w' o q r ≤ w o q r) :
    ∀ {c : OComp S α} {t : ℕ}, c.CostBoundV w t → c.CostBoundV w' t
  | .pure _, _, _ => trivial
  | .sample _ k, _, h => fun r => OComp.CostBoundV.weight hw (c := k r) (h r)
  | .query o q k, _, h => fun r => let ⟨t', h1, h2⟩ := h r; ⟨t', (Nat.add_le_add_right (hw o q r) t').trans h1, OComp.CostBoundV.weight hw (c := k r) h2⟩

end Rom
