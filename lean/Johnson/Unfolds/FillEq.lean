-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/FillEq.lean: when `fillL es plan` (Johnson/Unfolds/FillLaw.lean) is a given list L
of declared rounds.

Definition.
  `posB e`: the round of this entry draws positions.
Statement. General.
  **`fillL_eq_of`**: where a round of L that draws no positions stores and opens nothing, and what
    L's rounds that draw positions open and store, in order, is the plan:
    `fillL (L.map (·.entry)) plan = L`.

Limits. The two conditions are premises. No closed fact. Nothing on soundness.

-/
import Johnson.Unfolds.FillLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds
open Johnson.G Johnson.G.OfPlan

/-- The round of this entry draws positions. -/
def posB (e : Fmt.Entry) : Bool := Fmt.kindOf e.name == some .positions

/-- **Where a round of L that draws no positions stores and opens nothing: `fillL` at L's entries
and at what L's rounds of positions open and store is L.** -/
theorem fillL_eq_of : ∀ (L : List Fmt.DeclaredRound) (plan : List (List Told × List Fmt.Stored)),
    (∀ d ∈ L, posB d.entry = false → d.stored = [] ∧ d.opens = []) →
    (L.filter fun d => posB d.entry).map (fun d => (d.opens, d.stored)) = plan →
      fillL (L.map (·.entry)) plan = L
  | [], _, _, _ => rfl
  | d :: L, plan, hq, hp => by
    have hq' : ∀ x ∈ L, posB x.entry = false → x.stored = [] ∧ x.opens = [] :=
      fun x hx => hq x (List.mem_cons_of_mem _ hx)
    rw [List.map_cons]
    cases hb : posB d.entry with
    | false =>
      have hb' : (Fmt.kindOf d.entry.name == some .positions) = false := hb
      have hp' : (L.filter fun d => posB d.entry).map (fun d => (d.opens, d.stored)) = plan := by
        simpa [List.filter_cons, hb] using hp
      obtain ⟨h1, h2⟩ := hq d List.mem_cons_self hb
      simp only [fillL, hb']
      rw [fillL_eq_of L plan hq' hp']
      congr 1
      cases d
      simp_all
    | true =>
      have hb' : (Fmt.kindOf d.entry.name == some .positions) = true := hb
      have hp' : (d.opens, d.stored) ::
          (L.filter fun d => posB d.entry).map (fun d => (d.opens, d.stored)) = plan := by
        simpa [List.filter_cons, hb] using hp
      subst hp'
      simp only [fillL, hb']
      rw [fillL_eq_of L _ hq' rfl]

end Johnson.Unfolds

#print axioms Johnson.Unfolds.fillL_eq_of
