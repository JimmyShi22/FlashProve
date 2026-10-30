-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/Back/CallsOfKeys.lean: FROM THE NINE KEYS OF THE OUTPUT HEAD BACK TO THE
SIX CALLS' TABLES, AT EVERY COLUMN: the converse of `backCall`
(Johnson/Desc/Kinds/Law/OutCall.lean). THE LIBRARY HAS IT: `forthCall`, with the definition
`NineKeys` and `nineKeys_of_calls` (Johnson/Desc/Kinds/Law/OutCallBack.lean). This file imports that
file and declares neither of these two names; it keeps `calls_of_keys`, the name by which the files
of this folder call the converse, as one call of `forthCall`. Two statements with their proofs. Over
the library alone; general in the sizes.

What it is not. Nothing of its own but `slot_at`. Nothing says that the nine keys are rows at any
cells: `calls_of_keys` is CONDITIONAL on that. No chance in it. Nothing on soundness, completeness
or hiding.

  `slot_at`             key number s of a call stands in that call, and the call's list of lengths
                        holds that key's length at s. No file of this folder calls it. (The
                        library's `slot_place`, in the file named above, says of the first half
                        more: the key's place.)
  `calls_of_keys`       `forthCall` under another name: CONDITIONAL on the tests on the plan, "row 0
                        of the table is 2^F" (F: a field of the sizes, `Sizes`,
                        Johnson/Desc/Kinds/HeadPublic.lean) and the nine keys: every place of every
                        call's table, at EVERY column, is a row of the call's lookup table

How. See the head of Johnson/Desc/Kinds/Law/OutCallBack.lean.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.OutCall
import Johnson.Desc.Kinds.Law.TableTie
import Johnson.Desc.Kinds.Law.OutCallBack

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open Norm (lt ls d S2 T)

/-- Key number s of a call stands in that call, and the call's list of lengths holds its length. -/
theorem slot_at [Sizes] {call s : Nat} (hcall : call < 6) (hs : s < (callKeys call).length) :
    (placeOf (slot (callKeys call) s)).1 = call ∧
      ((callKeys call).map lenOf).getD s 0 = lenOf (slot (callKeys call) s) := by
  have hc : call = 0 ∨ call = 1 ∨ call = 2 ∨ call = 3 ∨ call = 4 ∨ call = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · have h3 : s < 3 := hs
    have h : s = 0 ∨ s = 1 ∨ s = 2 := by omega
    rcases h with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  · have h1 : s < 1 := hs
    have h : s = 0 := by omega
    subst h
    exact ⟨rfl, rfl⟩
  · have h2 : s < 2 := hs
    have h : s = 0 ∨ s = 1 := by omega
    rcases h with rfl | rfl <;> exact ⟨rfl, rfl⟩
  · have h1 : s < 1 := hs
    have h : s = 0 := by omega
    subst h
    exact ⟨rfl, rfl⟩
  · have h1 : s < 1 := hs
    have h : s = 0 := by omega
    subst h
    exact ⟨rfl, rfl⟩
  · have h1 : s < 1 := hs
    have h : s = 0 := by omega
    subst h
    exact ⟨rfl, rfl⟩

/-- **FROM THE NINE KEYS BACK TO THE SIX CALLS' TABLES, AT EVERY COLUMN.** CONDITIONAL: the tests on
the plan; row 0 of the table is 2^F (so that the padding keys are rows); the nine keys. The
library's `forthCall` (Johnson/Desc/Kinds/Law/OutCallBack.lean), under another name. -/
theorem calls_of_keys [Sizes] [Policy] [Request] [Token] (sT : Nat) (tab : Nat → Nat) (c : NCells)
    (hplan : planOk sT = true) (h0 : tab 0 = 2 ^ F) (h : NineKeys tab c) :
    ∀ call, call < 6 → ∀ col t, t < T → InTable tab call (keyTable c call col t) :=
  forthCall sT tab c hplan h0 h

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.slot_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.calls_of_keys
