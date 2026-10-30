-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/KindDecide.lean: WHAT THE DECISION OF K10's BLOCK IS, IN TERMS OF THE
FRAME's CLOSING. Two statements and their proofs.

  `kind_decide`: the block's decision at a place P (Johnson/Desc/First/Close/Kind.lean) is
    `closeFrame` at what is owed, the frame and the statement of the record, at the place's entries,
    on the rounds; the record behind holds "nothing owed", the frame behind and the statement
    behind. It takes no column. By definition.
  `kind_decide_iff`: so it says yes with a record s' exactly if `closeFrame` says yes with some x
    and s' is made of x.
Limits. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.First.Close.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes

theorem kind_decide {Cl : Type} (P : Par) (s : Rec) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    ((kind (Cl := Cl)) P).decide s rs gs =
      (closeFrame s.owed s.frame s.st (entries P) rs).map fun x => ⟨none, x.1, x.2⟩ := rfl

theorem kind_decide_iff {Cl : Type} (P : Par) (s s' : Rec) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    ((kind (Cl := Cl)) P).decide s rs gs = .ok s' ↔
      ∃ x, closeFrame s.owed s.frame s.st (entries P) rs = .ok x ∧ s' = ⟨none, x.1, x.2⟩ := by
  rw [kind_decide]
  cases closeFrame s.owed s.frame s.st (entries P) rs with
  | error e => simp [Except.map]
  | ok x =>
    simp only [Except.map, Except.ok.injEq]
    exact ⟨fun h => ⟨x, rfl, h.symm⟩, fun ⟨_, h1, h2⟩ => by rw [h2, ← h1]⟩

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.kind_decide
#print axioms VerifiableInference.Desc.First.Close.kind_decide_iff
