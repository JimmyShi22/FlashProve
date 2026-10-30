-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/LedgersAtRow.lean: THE PENDING ROW's TAKE.

  pendingRowO_ledgers   behind a yes of pendingRowO (Johnson/Desc/First/Pend/Row.lean), where every
                   ledger in the statement was in order (LedgersFit): every ledger is in order; the
                   row's one mask entry is an entry of the index masks' message and lies within its
                   mask table; the table's size stays.

By the read-out pendingRowO_iff (Johnson/Desc/First/Pend/RowMeans.lean) and takeEntry_within
(Johnson/Desc/K13/Law/LedgerWithin.lean).

What is not claimed. Of the block that calls pendingRowO. Nothing on soundness, on an honest prover
or on hiding.

-/
import Johnson.Desc.K13.Law.LedgersKept
import Johnson.Desc.First.Pend.RowMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice Desc.Plain
open OnBytes.Means (tableSize)
open VerifiableInference.Desc.First.Pend (takeEntry pendingRowO pendingRowO_iff)

/-- **The pending row's take**: every ledger stays in order; the row's one mask entry is an entry of
the index masks' message and lies within its table, whose size stays; and what is left there is one
less. -/
theorem pendingRowO_ledgers {lay : WsLay} {indexMasks : ℕ} {o : WsForkOut} {claims : ℕ}
    {Sh : LinShape} {st : Statement} {row : TensorRow} {oracles' : Array OnBytes.Oracle}
    (h : pendingRowO lay indexMasks o claims Sh st.oracles = .ok (row, oracles'))
    (hf : LedgersFit st) :
    LedgersFit { st with oracles := oracles' } ∧
      (∀ t ∈ row.masks, t.1.oracle = indexMasks ∧ t.1.index < tableSize st indexMasks .mask) ∧
      tableSize { st with oracles := oracles' } indexMasks .mask =
        tableSize st indexMasks .mask := by
  obtain ⟨-, -, -, -, _, _, -, -, -, -, -, _, -, _, -, l, hl, c, l', ht, rfl, rfl⟩ :=
    (pendingRowO_iff lay indexMasks o claims Sh st.oracles oracles' row).1 h
  obtain ⟨x, hx, hxl⟩ := Option.bind_eq_some_iff.1 hl
  obtain ⟨k, hk⟩ := hf indexMasks x hx (by rw [hxl]; rfl)
  obtain ⟨a, b, -⟩ := takeEntry_within hk hl ht
  refine ⟨fit_of (T := st) ?_ ?_ hf, ?_, b⟩
  · rintro j ⟨k', hk'⟩
    by_cases e : indexMasks = j
    · subst e
      exact ⟨k' + 1, (takeEntry_within hk' hl ht).2.2⟩
    · exact ⟨k', ledgerAt_other₀ st indexMasks _ e hk'⟩
  · refine noNew_modify₀ st indexMasks _ ?_
    intro y hy _
    obtain rfl : x = y := Option.some.inj (hx.symm.trans hy)
    rw [hxl]
    rfl
  · intro t ht'
    rw [List.mem_singleton] at ht'
    subst ht'
    exact ⟨rfl, a⟩

end VerifiableInference.Desc.K13.Law
