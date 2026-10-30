-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/MergeApart.lean: The kind "lookup" (K3): BEHIND AN ACCEPT OF A LOOKUP's DECISION
NO KEPT ROW NAMES THE SLOT OF THE MERGE's END VALUE: the premise hmerge of objects_formsIn and
objects_formsInT (Johnson/Top/H/Keep/FormsInObjects.lean, FormsInTObjects.lean) IN ITS OWN TEXT, at
both seats: FROM ONE TEST WITH CODE ON THE STATE IN FRONT: sFvFitsB
(Johnson/Desc/First/Look/MergeSlotFits.lean): the merge's slot lies below the ledger's next slot.
Statements and proofs: joinings.

OBJECT: K3.block's decide at K3.seatDigits and at K3.seatCalls; K9.mergeOf.
Used by Johnson/Desc/Sound/MgAt/K3DigitsObjInFits.lean, Johnson/P5J/K03MergeAt.lean,
  Johnson/P5J/K03MergeAttAt.lean and 1 more.
LETTERS: claim, piece, laid, before, p, guests, s, s', rs, cols, F free.
Compiled with the whole library.

Main names: k3_digits_hmerge, k3_calls_hmerge.

By: decide_fresh (Johnson/Top/H/Keep/PadFresh.lean: the kept rows name no slot below F.next) ·
hmerge_of_fits (Johnson/Top/H/Keep/MergeSlotFitsLaw.lean) · k3_digits_pass, k3_calls_pass
(Johnson/Top/H/Keep/K3PassOf.lean).

Limits. THE ONE PREMISE ON THE STATE IN FRONT THAT THE PROMISE DOES NOT GIVE: sFvFitsB s = true: no
public item and no fact along the fold says it today. s.fork? = some F and Sized F: the item lookIn
says both.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.PadFresh
import Johnson.Top.H.Keep.MergeSlotFitsLaw
import Johnson.Top.H.Keep.K3PassOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (seatDigits seatCalls seatDigits_reads seatCalls_reads sFvFitsB)
open VerifiableInference.Desc.K9 (mergeOf)

section
variable {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
  (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl)) (s s' : S)
  (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))

/-- **hmerge behind the lookup on the digits.** -/
theorem k3_digits_hmerge
    (hd : (Desc.K3.block (seatDigits claim) piece laid before p guests).decide s rs cols =
      .ok s')
    {F : Fork} (hF : s.fork? = some F) (hS : Sized F) (h : sFvFitsB s = true) :
    ∀ g, (seatDigits claim).heard s' = some g →
      ∀ f ∈ g.rows.toList, ∀ x ∈ f.slots.toList, mergeOf s' ≠ some x.1 := by
  obtain ⟨G, P⟩ := k3_digits_pass claim piece laid before p guests s s' rs cols hd hF hS
  obtain ⟨F1, y, hF1, hn, e, hfr⟩ :=
    decide_fresh (seatDigits claim) piece laid before p guests s s' rs cols hd
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans hF1)
  have hsome : ((seatDigits claim).fork s).isSome = true := by
    rw [hF1]
    rfl
  have hg1 : (seatDigits claim).heard s' = some y.1 := by
    rw [e]
    exact seatDigits_reads claim s y.1 y.2 hsome hn
  intro g hg
  obtain rfl : y.1 = g := Option.some.inj (hg1.symm.trans hg)
  exact hmerge_of_fits P h (hfr hS).1

/-- **hmerge behind the lookup on the calls.** -/
theorem k3_calls_hmerge
    (hd : (Desc.K3.block (seatCalls claim) piece laid before p guests).decide s rs cols = .ok s')
    {F : Fork} (hF : s.fork? = some F) (hS : Sized F) (h : sFvFitsB s = true) :
    ∀ g, (seatCalls claim).heard s' = some g →
      ∀ f ∈ g.rows.toList, ∀ x ∈ f.slots.toList, mergeOf s' ≠ some x.1 := by
  obtain ⟨G, P⟩ := k3_calls_pass claim piece laid before p guests s s' rs cols hd hF hS
  obtain ⟨F1, y, hF1, hn, e, hfr⟩ :=
    decide_fresh (seatCalls claim) piece laid before p guests s s' rs cols hd
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans hF1)
  have hsome : ((seatCalls claim).fork s).isSome = true := by
    rw [hF1]
    rfl
  have hg1 : (seatCalls claim).heard s' = some y.1 := by
    rw [e]
    exact seatCalls_reads claim s y.1 y.2 hsome hn
  intro g hg
  obtain rfl : y.1 = g := Option.some.inj (hg1.symm.trans hg)
  exact hmerge_of_fits P h (hfr hS).1

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_digits_hmerge
#print axioms VerifiableInference.OnPublicFiles.k3_calls_hmerge
