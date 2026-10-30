-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/EntryRoundsToy.lean: small laws on a link's parameters and rounds: `Link.read_of`,
`roundParts`, `rounds_of_parts`. Nothing on soundness, completeness or hiding.
-/
import Fmt.M3ParOfLaws
import Fmt.M3Items
import Fmt.M3Dec
import Fmt.ParamsRead
import Fmt.Rules5Fast
import Fmt.M1SpecKnown
import Fmt.M3ParOfLawsProofs
import Fmt.M1SpecKnownProofs
import OnBytes.Params.EntryRounds

namespace OnBytes.Params

/-- Parameter bytes that hold the two items of a link's chain are read as such. -/
theorem Link.read_of {b c l : ByteArray} {g : Given} {x : Codes} {y : LinkShape}
    (hg : Given.read b = some g) (hi : g.items = [("codes", c), ("the link", l)])
    (hc : readCodes c = some x) (hl : readLink l = some y) : Link.read b = some ⟨g, x, y⟩ := by
  unfold Link.read
  simp only [hg, hi, hc, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-- What a round consists of, as a tuple whose equality can be decided. -/
def roundParts (r : Fmt.Round) :
    Fmt.Entry × Fmt.Kind × List Fmt.Item × List (Fmt.Shape × Fmt.Src) :=
  (r.entry, r.kind, r.items, r.opens)

/-- Rounds with the same parts are the same. -/
theorem rounds_of_parts : ∀ {a b : List Fmt.Round}, a.map roundParts = b.map roundParts → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | ⟨e, k, i, o⟩ :: a, ⟨e', k', i', o'⟩ :: b, h => by
    simp only [List.map_cons, List.cons.injEq, roundParts, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl, rfl⟩, t⟩ := h
    rw [rounds_of_parts t]

end OnBytes.Params
