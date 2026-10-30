-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/InScopeNamed.lean: r1 of the key file's back with its table of trees named:
from `KeyPins m` alone, and in the goals' scope from the two makers' returns. Calls and one
rewriting. Nothing is evaluated here.

InScope.lean gives `Key.sourceOf m = .ok (sourceAt m declKeyFull T)` for the T that
`Key.toldOfMade` returns, and leaves T unnamed. ToldOfKeyPins.lean names it: under `KeyPins m`
(Pins.lean) it is the written `toldKeyFull` (Johnson/HB/LLHARD/KB4/Told.lean). Here
the two are joined.

  `sourceOf_named_from_pins`: from `KeyPins m` alone. No return of a routine stands among its
    premises.
  `toldOfMade_in_scope`, `sourceOf_named_in_scope`: from hZ, hX and hm, as in InScope.lean.
  `told_at_return`, `decl_at_return`: so, in scope, whatever X `Key.sourceOf` returns has
    `X.Y.told = toldKeyFull` and `X.Y.D = declKeyFull`.
  `sourceAt_told`, `sourceAt_D`: which fields of its answer `sourceAt` lays T and D into.
It takes two returns, as InScope.lean does: hX and hm are the returns of `publicOfO` and of
`Key.madeAt`. That either returns at any files is not shown here. That hZ, hX and hm can be met
together is not shown in this file: if they could not, the four statements in scope would be idle
and nothing here would show it. In other files the three are met at Lean's written copy of the
full-size public files (`VerifierAndGoals.storedPublicFiles`: three terms written in Lean, tied to the shipped files by
no theorem; the example's weights are synthetic): hZ by `VerifierAndGoals.inScope_full`
(Johnson/Goal/Files/ScopeExample.lean); hX and hm, for some X₀ and m, by
`AtFullSide.Planner.theKeyLaid_zFull_returns` (AtFullSide/Planner/KeyLaidReturns.lean), in a side
library outside the main library (one theorem beneath `theKeyLaid_zFull_returns`,
`Johnson.Unfolds.Layout.lay_chars` in AtFullSide/Layout/TieRfl.lean, passes Lean's kernel only at a
thread stack larger than the default; Lean's re-checker leanchecker, run on it, fails at each
shell stack limit that was tried, up to 1 GiB; no independent checker has given a verdict on it), at
the format's second hash function (`OnBytes.secondHashFunction`) and the constant digest `Key.fixedDigest` (32
bytes of 1), at which the key file's piece is laid for the verifier's text, where no digest is
handed in; not the files' own. These two theorems speak of `VerifierAndGoals.storedPublicFiles` alone, not of other files
in scope.
Limits. `toldKeyFull` is a literal that was typed by hand: that it is what
`Key.toldOfMade` returns is said here under hZ, hX and hm, not at any public files. The answer is
still no written value whole: `sourceAt m …` keeps m's own fields (the chains as read, the
planner's chains, the layout's units). The later premises of `keyBack_of_rows`
(Johnson/IMR/KeyBackOfRows.lean: r4 to r8) are untouched. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.InScope
import Johnson.AtFull.KeyBack.ToldOfKeyPins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open VerifiableInference VerifiableInference.Desc
open Johnson.G.OfPlan (Made)
open OnBytes.Model.Verify (Public)

/-- **r1 with its table named, from the pins alone.** -/
theorem sourceOf_named_from_pins (m : Made) (h : KeyPins m) :
    Key.sourceOf m = .ok (sourceAt m Johnson.KB8.declKeyFull Johnson.KB4.toldKeyFull) := by
  obtain ⟨T, hT, hS⟩ := sourceOf_from_pins m h
  obtain rfl : T = Johnson.KB4.toldKeyFull :=
    Except.ok.inj (hT.symm.trans (toldOfMade_of_keyPins m h))
  exact hS

section
variable {Z : VerifierAndGoals.PublicFiles} {o : ℕ → ByteArray → ByteArray} {X₀ : Public} {m : Made}

/-- The table of trees, in scope. -/
theorem toldOfMade_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m) :
    Key.toldOfMade m = .ok Johnson.KB4.toldKeyFull :=
  toldOfMade_of_keyPins m (Johnson.KB8.keyPins_at_fixed hZ hX hm)

/-- **r1 with its table named, in scope.** -/
theorem sourceOf_named_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m) :
    Key.sourceOf m = .ok (sourceAt m Johnson.KB8.declKeyFull Johnson.KB4.toldKeyFull) :=
  sourceOf_named_from_pins m (Johnson.KB8.keyPins_at_fixed hZ hX hm)

/-- Whatever `Key.sourceOf` returns, in scope: its table of trees is the written one. -/
theorem told_at_return (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m)
    {X : Key.Source} (r1 : Key.sourceOf m = .ok X) : X.Y.told = Johnson.KB4.toldKeyFull := by
  obtain rfl := Except.ok.inj (r1.symm.trans (sourceOf_named_in_scope hZ hX hm))
  rfl

/-- Whatever `Key.sourceOf` returns, in scope: its declared rounds are the written ones. -/
theorem decl_at_return (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m)
    {X : Key.Source} (r1 : Key.sourceOf m = .ok X) : X.Y.D = Johnson.KB8.declKeyFull := by
  obtain rfl := Except.ok.inj (r1.symm.trans (sourceOf_named_in_scope hZ hX hm))
  rfl

end

/-- `sourceAt` lays T into the field `told` of its answer's key source. -/
theorem sourceAt_told (m : Made) (D T) : (sourceAt m D T).Y.told = T := rfl

/-- `sourceAt` lays D into the field `D`. -/
theorem sourceAt_D (m : Made) (D T) : (sourceAt m D T).Y.D = D := rfl

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.sourceOf_named_from_pins
#print axioms Johnson.AtFull.KeyBack.toldOfMade_in_scope
#print axioms Johnson.AtFull.KeyBack.sourceOf_named_in_scope
#print axioms Johnson.AtFull.KeyBack.told_at_return
#print axioms Johnson.AtFull.KeyBack.decl_at_return
#print axioms Johnson.AtFull.KeyBack.sourceAt_told
#print axioms Johnson.AtFull.KeyBack.sourceAt_D
