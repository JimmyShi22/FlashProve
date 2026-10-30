-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/InScope.lean: r1, r2, r3 of the key file's back, in the goals' scope, from
the two makers' returns. Calls alone. Nothing is evaluated here.

`Key.sourceOf`, `Key.rangesNumbers` and `Key.laterPlaces` (Johnson/Desc/Key/Desc.lean,
Ranges.lean, Places.lean) return at m, at named values, where the three public files are in the
goals' scope (hZ), `publicOfO` returns X₀ (hX) and `Key.madeAt` returns m at the constant digest
`Key.fixedDigest` (hm). Each theorem is one of this folder's theorems from `KeyPins m`
(Pins.lean) applied to `keyPins_at_fixed`
(Johnson/HB/LLHARD/KB8/KeyPinsOfReturns.lean), which gives `KeyPins m` from hZ, hX and hm.

  `treesK_in_scope`: `treesSent` returns at the key file's three chains (`TreesK`, Core.lean).
  `sourceOf_in_scope`: r1, at `sourceAt m declKeyFull T`, T being what `toldOfMade` returns.
    `sourceOf_returns_in_scope`: that it returns.
  `rangesNumbers_in_scope`: r2, at the written `rangesNumsFull`
    (Johnson/HB/LLHARD/KB8/Written.lean).
  `laterPlaces_in_scope`: r3, at that file's `laterPlacesFull`.
It takes two returns: hX and hm are the returns of `publicOfO` and of `Key.madeAt`. That either
returns at any files is not shown here. That hZ, hX and hm can be met together is not shown in this
file: if they could not, these theorems would be idle and nothing here would show it. In other files
the three are met at Lean's written copy of the full-size public files (`VerifierAndGoals.storedPublicFiles`: three terms
written in Lean, tied to the shipped files by no theorem; the example's weights are synthetic): hZ
by `VerifierAndGoals.inScope_full` (Johnson/Goal/Files/ScopeExample.lean); hX and hm, for some X₀ and m, by
`AtFullSide.Planner.theKeyLaid_zFull_returns` (AtFullSide/Planner/KeyLaidReturns.lean), in a side
library outside the main library (one theorem beneath `theKeyLaid_zFull_returns`,
`Johnson.Unfolds.Layout.lay_chars` in AtFullSide/Layout/TieRfl.lean, passes Lean's kernel only at a
thread stack larger than the default; Lean's re-checker leanchecker, run on it, fails at each
shell stack limit that was tried, up to 1 GiB; no independent checker has given a verdict on it), at
the format's second hash function (`OnBytes.secondHashFunction`) and the constant digest `Key.fixedDigest` (32
bytes of 1), at which the key file's piece is laid for the verifier's text, where no digest is
handed in; not the files' own. These two theorems speak of `VerifierAndGoals.storedPublicFiles` alone, not of other files
in scope.
Limits. T, what `toldOfMade` returns, is not named: `sourceOf_in_scope` is a «there is» in T. The
later premises of the theorem that lists what the key file's maker needs (`keyBack_of_rows`,
Johnson/IMR/KeyBackOfRows.lean: r4 to r8) are untouched. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.TreesKAtPins
import Johnson.AtFull.KeyBack.OfKeyPins
import Johnson.AtFull.KeyBack.SourceFromPins
import Johnson.HB.LLHARD.KB8.KeyPinsOfReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open VerifiableInference VerifiableInference.Desc
open Johnson.G.OfPlan (Made)
open Johnson.G (keySends0 keySends1 keySends2)
open OnBytes.Model.Verify (Public)

section
variable {Z : VerifierAndGoals.PublicFiles} {o : ℕ → ByteArray → ByteArray} {X₀ : Public} {m : Made}

/-- The core, in scope. -/
theorem treesK_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m) :
    TreesK m (treesOf keySends0 1 []) (treesOf keySends1 0 masksB) (treesOf keySends2 0 []) :=
  treesK_at_pins m (Johnson.KB8.keyPins_at_fixed hZ hX hm)

/-- **r1, in scope.** -/
theorem sourceOf_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m) :
    ∃ T, Key.toldOfMade m = .ok T ∧
      Key.sourceOf m = .ok (sourceAt m Johnson.KB8.declKeyFull T) :=
  sourceOf_from_pins m (Johnson.KB8.keyPins_at_fixed hZ hX hm)

/-- r1, in scope: that it returns. -/
theorem sourceOf_returns_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m) :
    ∃ X, Key.sourceOf m = .ok X :=
  sourceOf_returns_from_pins m (Johnson.KB8.keyPins_at_fixed hZ hX hm)

/-- **r2, in scope.** -/
theorem rangesNumbers_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m) :
    Key.rangesNumbers m = .ok Johnson.KB8.rangesNumsFull :=
  rangesNumbers_of_keyPins m (Johnson.KB8.keyPins_at_fixed hZ hX hm)

/-- **r3, in scope.** -/
theorem laterPlaces_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m) :
    Key.laterPlaces m = .ok Johnson.KB8.laterPlacesFull :=
  laterPlaces_of_keyPins m (Johnson.KB8.keyPins_at_fixed hZ hX hm)

end

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.treesK_in_scope
#print axioms Johnson.AtFull.KeyBack.sourceOf_in_scope
#print axioms Johnson.AtFull.KeyBack.sourceOf_returns_in_scope
#print axioms Johnson.AtFull.KeyBack.rangesNumbers_in_scope
#print axioms Johnson.AtFull.KeyBack.laterPlaces_in_scope
