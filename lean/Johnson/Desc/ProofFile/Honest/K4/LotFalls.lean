-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/LotFalls.lean.

What is here. THE FALLS AT THE OWN MEMBERS OF THE LAYERS' OWN ROUNDS (kind K4), AS ONE LIST, MADE
OFF THE LOT's OWN LIST OF PLACES. `k4HLot` (Honest/K4/Part.lean) lays a half at each place at which
the lot lays a sub-protocol, for which `k4PubOf` yields the public data and `k4TableFits` is true.
`k4LotFalls` lays `k4Fall Q` (the same file: the verifier's test on one sampled element, at K4's own
member) at these very places, by the same text: one fall for each half. What it is for: statements
on the member's step ask that `k4Fall Q` be among the falls that are excused; a fall holds
functions, so membership can be had by construction alone. One definition with code, and laws on
lists with their proofs.

  `k4LotFalls`   the list.
  `k4Fall_mem`   **where the lot lays a half, its fall is in the list.**
  `k4LotFalls_kind`   every fall of the list stands at a place of the kind K4.
  `k4LotFalls_length`   as many falls as halves.

Limits. GENERAL IN THE PUBLIC PART Z AND THE SEGMENTS' DATA G. `k4Fall_mem` is CONDITIONAL on hx (x
is among the places at which the lot lays a sub-protocol), hQ (`k4PubOf` returns Q at x's
parameters) and hF (`k4TableFits` accepts Q); that the three hold at any files is not shown here.
Where the lot's list is empty this list is empty. THE SECOND FALL, on the free slots behind the
batching (`k4FreeSlotFall`, Honest/K4/Part.lean; `k4FreeSlotFallCut`, Honest/K4/FallCut.lean), IS
NOT IN THE LIST: it stands at another member, and its place, seat and share are laid by whoever
seats it. EACH FALL's SHARE IS A STATED NUMBER (`k4CoinZeroShare`): no bound is shown, and nothing
is added up here. Statements over the list: Law/LotPlace.lean, Law/LotFallsLaws.lean,
Law/FillFalls.lean. No filling or side holds it.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Part

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4.Honest

/-- **K4's falls at its own members**: `k4Fall Q` at each place at which `k4HLot` lays a half. -/
def k4LotFalls {S : Type} (Z : Pub) (G : Ground) : List (Fall S) :=
  (k4From Z G G.built.toList 0 none).filterMap fun x =>
    ((k4PubOf Z x.2).filter k4TableFits).map k4Fall

/-- CONDITIONAL: on the three hypotheses. **WHERE THE LOT LAYS A HALF, ITS FALL IS IN THE LIST.** -/
theorem k4Fall_mem {S : Type} {Z : Pub} {G : Ground} {x : Bool × OnBytes.Desc.First.K4.Par}
    {Q : K4Pub} (hx : x ∈ k4From Z G G.built.toList 0 none) (hQ : k4PubOf Z x.2 = some Q)
    (hF : k4TableFits Q = true) : (k4Fall Q : Fall S) ∈ k4LotFalls Z G := by
  refine List.mem_filterMap.2 ⟨x, hx, ?_⟩
  rw [hQ]
  simp [Option.filter, hF]

/-- Every fall of the list stands at a place of the kind K4. -/
theorem k4LotFalls_kind {S : Type} (Z : Pub) (G : Ground) (f : Fall S)
    (hf : f ∈ k4LotFalls Z G) : f.place.kind = .K4 := by
  obtain ⟨y, -, e⟩ := List.mem_filterMap.1 hf
  obtain ⟨Q, -, rfl⟩ := Option.map_eq_some_iff.1 e
  rfl

/-- A law on lists: the function behind the filter does not bear on the length. -/
theorem filterMap_map_length.{u, v, w} {α : Type u} {β : Type v} {γ : Type w} (o : α → Option β)
    (f : β → γ) (l : List α) :
    (l.filterMap fun x => (o x).map f).length = (l.filterMap o).length := by
  rw [← List.map_filterMap, List.length_map]

/-- As many falls as the lot has halves. -/
theorem k4LotFalls_length {S W₀ Rc Tr X : Type} (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : Pub → Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Z : Pub)
    (G : Ground) :
    (k4LotFalls (S := S) Z G).length =
      ((k4HLot (Rc := Rc) (X := X) cells weights look).halves Z G).length :=
  (filterMap_map_length (fun x : Bool × OnBytes.Desc.First.K4.Par =>
      (k4PubOf Z x.2).filter k4TableFits) k4Fall (k4From Z G G.built.toList 0 none)).trans
    (filterMap_map_length (fun x : Bool × OnBytes.Desc.First.K4.Par =>
      (k4PubOf Z x.2).filter k4TableFits) (k4Half cells weights k4Tokens (look Z G))
      (k4From Z G G.built.toList 0 none)).symm

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4Fall_mem
#print axioms ProofFile.Honest.K4.k4LotFalls_kind
#print axioms ProofFile.Honest.K4.filterMap_map_length
#print axioms ProofFile.Honest.K4.k4LotFalls_length
