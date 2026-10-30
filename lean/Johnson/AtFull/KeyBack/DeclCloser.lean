-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/DeclCloser.lean: at an m whose plans and shape are the full size's written
ones, the declared rounds that `declKOf` returns are the written declared rounds, from one closed
Bool.

`declK m t₀ t₁ t₂` (FillOpens.lean) is `fillL` at the three plans' rounds and at the lists that the
rule makes of the three chains' trees. `declKeyFull` (Johnson/HB/LLHARD/KB8/Written.lean) is a
written value. By `fillL_eq_of` (FillsBool.lean) the two are one where the written rounds bear the
plans' rounds as entries (DeclEntries.lean), only their rounds of positions open anything
(DeclRest.lean), and these carry just the rule's lists. The last is `closesB`: it is read along the
written runs, so its cost goes by the number of runs.

  `drawnRuns recs runs`: what the rounds that draw positions carry, in order, along the runs.
  `drawn_of_runs`: that is what a filter on the whole list gives.
  `closesB S t₀ t₁ t₂`: at the three written lists it is what the rule makes of t₀, t₁, t₂.
  `declK_at`: the equation.

Limits. That `KeyPins` holds at any m is not shown. That `closesB` says yes at any lists of trees is
not shown: it can be evaluated only where the three lists are written values. That `declKeyFull` is
what the program's dry runs state is not said. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.FillsBool
import Johnson.AtFull.KeyBack.Pins
import Johnson.AtFull.KeyBack.DeclEntries
import Johnson.AtFull.KeyBack.DeclRest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G.OfPlan
open Johnson.KB8 (declKeyFull declRecsFull unrunD)
open Johnson.G (dryKeyRunsFull0 dryKeyRunsFull1 dryKeyRunsFull2)
open Johnson.G.Runs (valRuns expand filter_unrunG)
open Johnson.Unfolds (fillL)
open Lk6.AtPlan (keyFull)

/-- What the rounds that draw positions carry, in order, read along the runs. -/
def drawnRuns (recs : List Fmt.DeclaredRound) (runs : List (Nat × Nat)) :
    List (List Told × List Fmt.Stored) :=
  (expand ((valRuns recs runs).filter fun x => Fmt.kindOf x.2.entry.name == some .positions)).map
    fun r => (r.opens, r.stored)

/-- That is what a filter on the whole list gives. -/
theorem drawn_of_runs (recs : List Fmt.DeclaredRound) (runs : List (Nat × Nat)) :
    ((unrunD recs runs).filter fun r => Fmt.kindOf r.entry.name == some .positions).map
      (fun r => (r.opens, r.stored)) = drawnRuns recs runs :=
  congrArg (List.map fun r : Fmt.DeclaredRound => (r.opens, r.stored))
    (filter_unrunG (fun r : Fmt.DeclaredRound => Fmt.kindOf r.entry.name == some .positions) recs runs)

/-- The written declared rounds' rounds of positions carry just the lists that the rule makes of
three lists of trees. -/
def closesB (S : LinShape) (t₀ t₁ t₂ : List (Sent × Nat)) : Bool :=
  decide (drawnRuns declRecsFull dryKeyRunsFull0 = noStored (onceOpens t₀)) &&
  decide (drawnRuns declRecsFull dryKeyRunsFull1 = sharedOpens S t₁) &&
  decide (drawnRuns declRecsFull dryKeyRunsFull2 =
    noStored (secondOpens S (fun t => t.tag == .indexMask) t₀ t₁ t₂))

/-- **At a pinned m, what `declKOf` returns is the written value, from one closed Bool.** -/
theorem declK_at (m : Made) (h : KeyPins m) (t₀ t₁ t₂ : List (Sent × Nat))
    (hC : closesB keyFull.once.shape t₀ t₁ t₂ = true) : declK m t₀ t₁ t₂ = declKeyFull := by
  rw [← h.shape] at hC
  have h₁ := Bool.and_eq_true_iff.1 hC
  have h₂ := Bool.and_eq_true_iff.1 h₁.1
  have e₀ : fillL (plan₀ m).rounds (lists₀ t₀) = declKeyFull.1 :=
    fillL_eq_of _ _ _ (decl_entries0.trans h.rounds₀.symm)
      ((drawn_of_runs declRecsFull dryKeyRunsFull0).trans (of_decide_eq_true h₂.1)) decl_rest0
  have e₁ : fillL (plan₁ m).rounds (lists₁ m t₁) = declKeyFull.2.1 :=
    fillL_eq_of _ _ _ (decl_entries1.trans h.rounds₁.symm)
      ((drawn_of_runs declRecsFull dryKeyRunsFull1).trans (of_decide_eq_true h₂.2)) decl_rest1
  have e₂ : fillL (plan₂ m).rounds (lists₂ m t₀ t₁ t₂) = declKeyFull.2.2 :=
    fillL_eq_of _ _ _ (decl_entries2.trans h.rounds₂.symm)
      ((drawn_of_runs declRecsFull dryKeyRunsFull2).trans (of_decide_eq_true h₁.2)) decl_rest2
  exact Prod.ext e₀ (Prod.ext e₁ e₂)

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.drawn_of_runs
#print axioms Johnson.AtFull.KeyBack.declK_at
