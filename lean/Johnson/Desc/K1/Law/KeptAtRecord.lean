-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/KeptAtRecord.lean: a yes of W's sending at the first chain's carried record
leaves what stood in the statement: the codes, the groups with their rows, and every older message
whole. 
Main names: decideSend_kept; sendAtS_kept.

What is not claimed. A segment's later moment and the first segment's opening join groups behind the
decision: of these GoodSend5.lean says what stays of the older messages. Nothing on soundness, on an
honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.AtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

/-- A yes of the kind's decision leaves what stood in the statement, on whatever rounds. -/
theorem decideSend_kept {L : Type} (P : Par) (owed : Option Nat) (d d' : DState L)
    (rs : List Fmt.RoundView) (ids : Array Nat) (h : decideSend P owed d rs = .ok (ids, d')) :
    Kept d d' := by
  match rs, h with
  | [r₁, r₂], h =>
    obtain ⟨_, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
    exact kept_behind P d _ _

/-- **W's sending leaves what stood in the statement.** -/
theorem sendAtS_kept (P : Par) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (sendAtS P : Block S Cl).decide s rs gs = .ok s') :
    s'.st.codes = s.st.codes ∧ s'.st.groups = s.st.groups ∧
      ∀ j, j < s.st.oracles.size → s'.st.oracles[j]? = s.st.oracles[j]? := by
  obtain ⟨ids, d', h1, e1, _⟩ := sendAtS_ok P s s' _ gs h
  rw [e1]
  exact decideSend_kept P _ (stateOf s (#[] : Array Nat)) d' rs ids h1

end VerifiableInference.Desc.K1
