-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/Core.lean: WHAT THE FILES ON THE KEY FILE's BACK SHARE. Definitions, and two
tools on `Except`. It proves nothing of the key file.

`Key.sourceOf`, `Key.rangesNumbers` and `Key.laterPlaces` (Johnson/Desc/Key/Desc.lean, Ranges.lean,
Places.lean) each call `treesSent` (Johnson/G/RoundsOfPlan.lean) at the key file's chains. The calls
part in the words for a refusal alone.

  `plan₀`, `plan₁`, `plan₂`, `shapeK`: the three chains' plans and the shape, as fields of m.
  `TreesK m t₀ t₁ t₂`: `treesSent` returns t₀, t₁, t₂ at the three chains, at every such words.
  `cutAt C ch st`: the cut at the first round "BAT" of the chain number ch: `laterPlaces`' own text.
  `ok_of_bind`, `bind_of_ok`: a bind in `Except` returns just where both steps do.
Limits. That `TreesK` holds at any m is not shown here. Nothing on soundness, nothing on hiding.

-/
import Johnson.Desc.Key.Desc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key

/-- The three plans of the key file's chains, and the shape by which they were cut. -/
abbrev plan₀ (m : Made) : Fmt.Plan := m.p.chains.key.oneTime.given.plan
abbrev plan₁ (m : Made) : Fmt.Plan := m.p.chains.key.shared.given.plan
abbrev plan₂ (m : Made) : Fmt.Plan := m.p.chains.key.second.given.plan
abbrev shapeK (m : Made) : LinShape := m.p.chains.made.sized.key.once.shape

/-- THE CORE: `treesSent` returns at the key file's three chains, whatever a refusal's words. -/
structure TreesK (m : Made) (t₀ t₁ t₂ : List (Sent × Nat)) : Prop where
  first : ∀ a, treesSent a m.key.1 (plan₀ m) [] = .ok t₀
  shared : ∀ a, treesSent a m.key.2.1 (plan₁ m)
    (ownMasks m.key.2.1.codes (shapeK m) (plan₁ m).rounds) = .ok t₁
  second : ∀ a, treesSent a m.key.2.2 (plan₂ m) [] = .ok t₂

/-- The cut at the first "BAT" of the chain number ch (from 0): `laterPlaces`' own text. -/
abbrev cutAt (C : Configured) (ch : Nat) (st : List IoppStage) : Option H2U.TestCut := do
  keyTestCut C ch (← (← keyBatchRounds C ch)[0]?) st

/-- Where a bind returns, both steps return. -/
theorem ok_of_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, h⟩

/-- Where both steps return, the bind returns. -/
theorem bind_of_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {a : α} {b : β}
    (hx : x = .ok a) (hf : f a = .ok b) : x >>= f = .ok b := by
  rw [hx]
  exact hf

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.ok_of_bind
#print axioms Johnson.AtFull.KeyBack.bind_of_ok
