-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/HereAtRecord.lean: what W's sending leaves of the first chain's carried record:
the chain stands at the members' places as it stood, with the new messages' numbers noted; the
statement's codes, the rows on the table, and the fields check, out, req and failed are as they
were; behind it no row is owed. The statement, the book and the roots' count are the sending's.

Main names: sendAtS_here, sendAtS_rows.

What is not claimed. Nothing on a segment's later moment or on the first segment's opening. Nothing
on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.AtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

/-- **What W's sending leaves.** -/
theorem sendAtS_here (P : Par) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (sendAtS P : Block S Cl).decide s rs gs = .ok s') :
    ∃ a ids, s.here = .mem a ∧ a.msg = P.sent ∧ s'.here = .mem { a with ids := ids } ∧
      s'.check = s.check ∧ s'.out = s.out ∧ s'.req = s.req ∧ s'.failed = s.failed ∧
      s'.rowsOwed = none := by
  unfold sendAtS at h
  dsimp only at h
  split at h
  · rename_i a ha
    split at h
    · rename_i hm
      obtain ⟨y, _, rfl⟩ := (map_ok _ _ _).1 h
      exact ⟨a, _, ha, by simpa using hm, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases h
  · cases h

/-- The statement's codes and the rows on the table are as they were. -/
theorem sendAtS_rows (P : Par) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (sendAtS P : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    s'.st.codes = s.st.codes ∧ s'.rows = s.rows := by
  obtain ⟨a, ids, h1, _, h2, _, h4, _⟩ := sendAtS_here P s s' _ gs h
  obtain ⟨ids', d', hd, e1, _⟩ := sendAtS_ok P s s' _ gs h
  obtain ⟨_, _, rfl⟩ := (decideSend_iff P _ _ d' r₁ r₂ ids').1 hd
  refine ⟨by rw [e1]; rfl, ?_⟩
  simp only [S.rows, h1, h2, h4]

end VerifiableInference.Desc.K1
