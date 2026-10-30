-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/SourceIs.lean: where `Key.sourceOf` returns, and what.

`Key.sourceOf m` (Johnson/Desc/Key/Desc.lean) has two steps that can refuse: `declKOf m`, the key
file's declared rounds (Johnson/G/RoundsOfPlan.lean), and `toldOfMade m`, what is told of the three
chains' trees (Johnson/Desc/Key/Source.lean). All else that it lays into its answer is a field of m.

  `sourceAt m D T`: the answer at given declared rounds D and given tenants T.
  `sourceOf_iff`: `sourceOf m` returns X just where both steps return, and then X is
    `sourceAt m D T`.

Limits. It takes two returns to give one: that either step returns at any m is not shown here.
Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.Core

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key

/-- `sourceOf`'s answer at given declared rounds and tenants: its own text, with the two steps'
values as arguments. -/
def sourceAt (m : Made) (D : Decl3) (T : List ProofFile.Root × List ProofFile.Root × List ProofFile.Root) : Source :=
  ⟨⟨m.p.chains.key, m.p.chains.made.sized.key.once.shape,
      (m.key.1.codes, m.key.2.1.codes, m.key.2.2.codes), m.p.chains.made.sized.key.once.input,
      m.p.chains.made.sized.key.ranges.x, m.p.chains.made.sized.set.samples, D, T,
      OnBytes.Plan.unitsOfLayout m.p.X.layers.wsLay⟩, m.p.chains, m.p.chains.made.sized.key.set⟩

/-- `sourceOf` returns just where its two steps return. -/
theorem sourceOf_iff (m : Made) (X : Source) :
    sourceOf m = .ok X ↔ ∃ D T, declKOf m = .ok D ∧ toldOfMade m = .ok T ∧ X = sourceAt m D T := by
  constructor
  · intro h
    unfold sourceOf at h
    obtain ⟨D, hD, h⟩ := ok_of_bind h
    obtain ⟨T, hT, h⟩ := ok_of_bind h
    exact ⟨D, T, hD, hT, (Except.ok.inj h).symm⟩
  · rintro ⟨D, T, hD, hT, rfl⟩
    unfold sourceOf
    refine bind_of_ok hD ?_
    exact bind_of_ok hT rfl

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.sourceOf_iff
