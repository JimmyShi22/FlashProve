-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Part/MaskedSumKeeps.lean: the masked sumcheck's share of «what lies under a filled slot
stays there»: all three of its functions that take a ledger lead to a later one.

The masked sumcheck (Johnson/Desc/Part/MaskedSum4.lean) is a part, not a block: it has no place and
no record of its own. What it owes to the law LedgerKeeps of the blocks that call it
(Johnson/Desc/Part/LedgerKeeps.lean) is that «hear», «row» and «whole», wherever they return, hand
back a ledger that is later (OnBytes.PscRun.Later) than the one that they were handed.
  hear_keeps, row_keeps : Johnson/Desc/Part/MaskedSumLedger.lean.
  whole_keeps           : here: «whole» is «hear», a reading of what the ledger shows, and «row».
  whole_parts           : what «whole» returns, in its parts.
Nothing is asked of the ledger's sizes. Nothing on soundness, on an honest prover or on hiding.
-/
import Johnson.Desc.Part.MaskedSumLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.Model

/-- What «whole» returns, in its parts. -/
theorem whole_parts {C : Aff} {k : Call} {endTerm : List E → List E → E} {F G' : Fork}
    {rs : List Fmt.RoundView} {h : Heard} {f : Aff} (hw : whole C k endTerm F rs = some (h, f, G')) :
    ∃ (e : Ends) (G : Fork) (sh : List E), k.ends = some e ∧ hear C k F rs = some (h, G) ∧
      shownEnds h e.n G = some sh ∧ row h (endTerm h.r sh) {} G = some (f, G') := by
  unfold whole at hw
  cases he : k.ends with
  | none => simp [he] at hw
  | some e =>
    cases hh : hear C k F rs with
    | none => simp [he, hh] at hw
    | some x =>
      obtain ⟨h0, G0⟩ := x
      cases hs : shownEnds h0 e.n G0 with
      | none => simp [he, hh, hs] at hw
      | some sh =>
        cases hr : row h0 (endTerm h0.r sh) {} G0 with
        | none => simp [he, hh, hs, hr] at hw
        | some y =>
          obtain ⟨f0, G1⟩ := y
          simp [he, hh, hs, hr] at hw
          obtain ⟨e1, e2, e3⟩ := hw
          subst e1 e2 e3
          exact ⟨e, G0, sh, rfl, rfl, hs, hr⟩

/-- **«whole» leads to a later ledger.** -/
theorem whole_keeps {C : Aff} {k : Call} {endTerm : List E → List E → E} {F G' : Fork}
    {rs : List Fmt.RoundView} {h : Heard} {f : Aff} (hw : whole C k endTerm F rs = some (h, f, G')) :
    OnBytes.PscRun.Later F G' := by
  obtain ⟨_, _, _, _, hh, _, hr⟩ := whole_parts hw
  exact (hear_keeps hh).trans (row_keeps hr)

end VerifiableInference.Desc.Part.MaskedSum

#print axioms VerifiableInference.Desc.Part.MaskedSum.whole_parts
#print axioms VerifiableInference.Desc.Part.MaskedSum.whole_keeps
