-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/AsRowGroups.lean: THE MAKING OF THE ONE EQUATION's ROW (`asRow`, Johnson/Desc/First/Batch/Text.lean) LEAVES THE STATEMENT's GROUPS: it takes mask
entries, which turns one message's ledger, and nothing else of the statement. One lemma, general: no description, no state of a chain.

  **`asRow_groups`**   `asRow R f q d = .ok y` gives: the groups of y's statement are the groups of d's

Limits. Nothing on whether `asRow` returns. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.PadForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (asRow St Equation)
open VerifiableInference.Desc.K9.Shape (ans_bind need_ok there_ok)

theorem asRow_groups {X : Type} (R : ReqRows) (f : ReqFrame) (q : Equation) (d : St X) (y : OnBytes.Row × St X)
    (hy : asRow R f q d = .ok y) : y.2.st.groups = d.st.groups := by
  unfold asRow at hy
  simp only [ans_bind] at hy
  obtain ⟨row, -, hy⟩ := hy
  split at hy
  · obtain rfl := Except.ok.inj hy
    rfl
  · simp only [ans_bind, need_ok, there_ok, exists_const] at hy
    obtain ⟨m, _hm, -, o₁, _ho, x, hx, -, hy⟩ := hy
    obtain rfl := Except.ok.inj hy
    exact (takeN_pads o₁ _ d [] x hx).1

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.asRow_groups
