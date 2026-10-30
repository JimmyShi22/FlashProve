-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameLabelsO.lean: GameLabels.lean's test on the plan, `labelsPubB`, AT TWO
REAL PLACES, by Lean's kernel: the shared chain's first proximity test (first arm) at the smaller
stored proof's plan and at the full size's (`piU`, `piUFull`: Johnson/Desc/K12/Law/PlacesSmall.lean,
PlacesFull.lean). Statements and proofs.
The letters: the chain's trees are numbered from lo on through the file: num := `numAt lo t₂ 1`;
nl ℓ := lo + (ℓ - the place's firstTree); base := lo + the place's count of trees in front. Tried at
lo := 0 and at lo := 40 (a made-up count for the first chain's trees).
  `labels_U` | `labels_U40` | `labels_UFull`: the test says yes.
  `labels_U_base`: no, with base lower by one. `labels_U_nl`: no, with nl raised by one.
Limits. Nothing on soundness. The first chain's own place of the test has no literal here.

-/
import Johnson.Desc.K12.Coin.GameLabels
import Johnson.Desc.K12.Law.PlacesSmall
import Johnson.Desc.K12.Law.PlacesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Member (piU piUFull)

/-- From a label to the tree's number through the file, at a chain whose trees begin at lo. -/
def nlAt (π : P12) (lo ℓ : ℕ) : ℕ := lo + (ℓ - π.nums.firstTree)

theorem labels_U : labelsPubB piU (numAt 0 0 1) (nlAt piU 0) piU.nums.free = true := by
  decide +kernel

theorem labels_U40 : labelsPubB piU (numAt 40 0 1) (nlAt piU 40) (40 + piU.nums.free) = true := by
  decide +kernel

theorem labels_UFull :
    labelsPubB piUFull (numAt 0 0 1) (nlAt piUFull 0) piUFull.nums.free = true := by
  decide +kernel

theorem labels_U_base : labelsPubB piU (numAt 0 0 1) (nlAt piU 0) (piU.nums.free - 1) = false := by
  decide +kernel

theorem labels_U_nl :
    labelsPubB piU (numAt 0 0 1) (fun ℓ => nlAt piU 0 ℓ + 1) piU.nums.free = false := by
  decide +kernel

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.labels_U
#print axioms VerifiableInference.Desc.K12.Coin.labels_U40
#print axioms VerifiableInference.Desc.K12.Coin.labels_UFull
#print axioms VerifiableInference.Desc.K12.Coin.labels_U_base
#print axioms VerifiableInference.Desc.K12.Coin.labels_U_nl
