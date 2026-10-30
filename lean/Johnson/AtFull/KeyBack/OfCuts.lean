-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/OfCuts.lean: WHAT IS LEFT OF `Key.rangesNumbers m` AND `Key.laterPlaces m`
RETURNING, AS TWO THEOREMS' PREMISES. General in m: no written value stands here. Calls alone:
RangesReturns.lean, LaterReturns.lean, BatLaw.lean.

IT TAKES A RETURN TO GIVE A RETURN. None of the premises below is shown at any m here.
  `rangesNumbers_of_split`: `Key.rangesNumbers m` returns `rangesAt m t₀ pre.length`, from:
    `treesSent`'s return at the first chain; the first chain's rounds are pre ++ b :: post; no round
    of pre is named "BAT"; b is; `rangesGuard m pre.length`.
  `laterPlaces_of_cuts`: `Key.laterPlaces m` returns `laterAt m (firstsAt m t₀ t₁) tU tW`, from:
    `treesSent`'s returns at the three chains; and for each of the made plans number 1 and 2: it is
    there; the first place of "BAT" on its entries; `H2U.cutOn` returns there.
Limits. The first theorem reads the rounds of the given plan (`plan₀ m`), the second the entries of
the made plans (`m.p.chains.made.key`): that these are one list is not said. Nothing on soundness,
nothing on hiding.

-/
import Johnson.AtFull.KeyBack.BatLaw
import Johnson.AtFull.KeyBack.RangesReturns
import Johnson.AtFull.KeyBack.LaterReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key

/-- **r2, from the split of the first chain's rounds at their first "BAT".** -/
theorem rangesNumbers_of_split (m : Made) (t₀ : List (Sent × Nat)) (pre post : List Fmt.Entry)
    (b : Fmt.Entry)
    (h₀ : treesSent "key file, first chain" m.key.1 (plan₀ m) [] = .ok t₀)
    (hs : (plan₀ m).rounds = pre ++ b :: post)
    (hp : noBat pre = true) (hb : b.name = "BAT")
    (hg : rangesGuard m pre.length = true) :
    rangesNumbers m = .ok (rangesAt m t₀ pre.length) :=
  rangesNumbers_eq m t₀ pre.length h₀
    (by rw [hs]; exact batPlaces_head_of_split pre post b hp hb) hg

/-- **r3, from the two later chains' made plans.** -/
theorem laterPlaces_of_cuts (m : Made) (t₀ t₁ t₂ : List (Sent × Nat)) (P₁ P₂ : Planned)
    (i₁ i₂ : Nat) (tU tW : H2U.TestCut)
    (h₀ : treesSent "key file, first chain" m.key.1 (plan₀ m) [] = .ok t₀)
    (h₁ : treesSent "key file, shared chain" m.key.2.1 (plan₁ m)
      (ownMasks m.key.2.1.codes (shapeK m) (plan₁ m).rounds) = .ok t₁)
    (h₂ : treesSent "key file, second chain" m.key.2.2 (plan₂ m) [] = .ok t₂)
    (hP₁ : m.p.chains.made.key[1]? = some P₁)
    (hb₁ : (H2U.batPlaces (P₁.rounds.map (·.entry))).head? = some i₁)
    (hU : H2U.cutOn (P₁.rounds.map (·.entry)) 1 i₁ (shapeK m).testU = some tU)
    (hP₂ : m.p.chains.made.key[2]? = some P₂)
    (hb₂ : (H2U.batPlaces (P₂.rounds.map (·.entry))).head? = some i₂)
    (hW : H2U.cutOn (P₂.rounds.map (·.entry)) 2 i₂ (shapeK m).testOwn = some tW) :
    laterPlaces m = .ok (laterAt m (firstsAt m t₀ t₁) tU tW) :=
  laterPlaces_eq m _ tU tW (testFirsts_eq m t₀ t₁ t₂ h₀ h₁ h₂)
    ((cutAt_eq _ 1 i₁ _ P₁ hP₁ hb₁).trans hU) ((cutAt_eq _ 2 i₂ _ P₂ hP₂ hb₂).trans hW)

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.rangesNumbers_of_split
#print axioms Johnson.AtFull.KeyBack.laterPlaces_of_cuts
