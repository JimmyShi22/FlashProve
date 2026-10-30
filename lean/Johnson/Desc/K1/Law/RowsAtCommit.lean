-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/RowsAtCommit.lean: a later moment's sending leaves the rows on the table.

  commitAtS_rows   behind a yes of K1.commitAtS, on any rounds, S.rows is what it was.

S.rows (Johnson/Desc/First/State.lean) reads where the chain's state stands and what the links have
left. The block stands in a layers', an attention's or the head's segment in front and behind
(commitAtS_here, Johnson/Desc/K1/Law/LaterAtRecord.lean), never in the members' part, and leaves
what the links have left (commitAtS_left, Johnson/Desc/K1/Law/BookAtRecord.lean).

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.LaterAtRecord
import Johnson.Desc.K1.Law.BookAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

/-- **A later moment's sending leaves the rows on the table**: it stands in a segment in front and
behind, where these are the rows that the links have left, and it leaves those. -/
theorem commitAtS_rows (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    s'.rows = s.rows := by
  obtain ⟨-, -, hh⟩ := commitAtS_here P link moment arrays s s' rs gs h
  have ho := (commitAtS_left P link moment arrays s s' rs gs h).2
  rcases hh with ⟨a, a', e1, e2⟩ | ⟨a, a', e1, e2⟩ | ⟨a, a', e1, e2, -, -⟩ <;>
    simp [S.rows, e1, e2, ho]

end VerifiableInference.Desc.K1
