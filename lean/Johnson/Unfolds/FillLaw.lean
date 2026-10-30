-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/FillLaw.lean: the value of `Johnson.G.OfPlan.fill` (Johnson/G/RoundsOfPlan.lean)
from its two tests; its last line, a fold that pushes one declared round an entry onto an array, is
a routine on lists.

Why. To Lean's kernel a push onto an array of n members walks all n: at the 48,293 entries of the
proof file's first chain (`dryProofFull_length`, Johnson/G/DryProofLit.lean), by our reading, of the
order of the square of that.

Definition.
  `fillL es plan`: the declared rounds, entry by entry: a round that draws positions takes the next
    list of the plan. It recurses on the entries.
Statements. General.
  `fold_fill`: the fold of pushes is `fillL` behind what the array held.
  **`fill_of`**: from (hn) as many rounds draw positions as there are lists, (hf) no list is empty
    of trees and of stored tables: `fill at_ es plan = .ok (fillL es plan)`.
Whose text. `fillL` follows the fold's step in `fill` (Johnson/G/RoundsOfPlan.lean): this tree's own
file.

Limits. THE TWO TESTS ARE PREMISES. The cost named above is by reading, not measured. No closed
fact. Nothing on soundness.

-/
import Johnson.G.RoundsOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds
open Johnson.G Johnson.G.OfPlan

/-- The declared rounds, entry by entry: a round that draws positions takes the next list. -/
def fillL : List Fmt.Entry → List (List Told × List Fmt.Stored) → List Fmt.DeclaredRound
  | [], _ => []
  | e :: es, plan =>
    match Fmt.kindOf e.name == some .positions, plan with
    | true, x :: rest => ⟨e, x.2, x.1⟩ :: fillL es rest
    | _, _ => ⟨e, [], []⟩ :: fillL es plan

/-- **The fold of pushes is `fillL` behind what the array held.** -/
theorem fold_fill : ∀ (es : List Fmt.Entry) (acc : Array Fmt.DeclaredRound)
    (plan : List (List Told × List Fmt.Stored)),
    (es.foldl (fun (s : Array Fmt.DeclaredRound × List (List Told × List Fmt.Stored)) e =>
      match Fmt.kindOf e.name == some .positions, s.2 with
      | true, x :: rest => (s.1.push ⟨e, x.2, x.1⟩, rest)
      | _, _ => (s.1.push ⟨e, [], []⟩, s.2)) (acc, plan)).1.toList = acc.toList ++ fillL es plan
  | [], acc, plan => by simp [fillL]
  | e :: es, acc, plan => by
    rw [List.foldl_cons]
    cases hb : (Fmt.kindOf e.name == some .positions) with
    | false =>
      simp only [fillL, hb]
      rw [fold_fill es]
      simp
    | true =>
      cases plan with
      | nil =>
        simp only [fillL, hb]
        rw [fold_fill es]
        simp
      | cons x rest =>
        simp only [fillL, hb]
        rw [fold_fill es]
        simp

/-- **`fill`'s value**, from its two tests: as many rounds draw positions as there are lists; no
list is empty of trees and of stored tables. -/
theorem fill_of {at_ : String} {es : List Fmt.Entry} {plan : List (List Told × List Fmt.Stored)}
    (hn : ((es.filter fun e => Fmt.kindOf e.name == some .positions).length == plan.length) = true)
    (hf : (plan.zipIdx.find? fun x => x.1.1.isEmpty && x.1.2.isEmpty) = none) :
    fill at_ es plan = .ok (fillL es plan) := by
  unfold fill
  simp only [hn, hf, ↓reduceIte, bind, Except.bind, pure, Except.pure]
  exact congrArg Except.ok ((fold_fill es #[] plan).trans (by simp))

end Johnson.Unfolds

#print axioms Johnson.Unfolds.fold_fill
#print axioms Johnson.Unfolds.fill_of
