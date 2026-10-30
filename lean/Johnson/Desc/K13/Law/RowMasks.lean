-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/RowMasks.lean: the proof of the statement `OwedRowMasks`
(Johnson/Desc/K13/Law/OwedRowMasks.lean): where kind K13's block (`atM3 P`) says yes, one row lies
on the table behind it, every mask entry that the row names is an entry of the record's index masks'
message, and the row names at least one. Three theorems.
Main names:
  `walk_ne`: at one variable or more, with one challenge for each, the hiding walk's list of
    coefficients is not empty: every weight of the batching is `Psc.Weight.plain 3`, whose
    polynomials have three coefficients: so the first variable gives three powers where it is the
    last, and two where it is not.
  `zip_append_ne`: two lists that are not empty, zipped, in front of a third: not empty.
  `rowMasks`: **the statement.** The first two clauses by the steps of `atM3_pileMasks`
    (Johnson/Desc/K13/Law/PileMasks.lean): `atM3_ok`, `batt_ok`, `atM3_rec`, `rowOf_onLedger`,
    `atM3_ledger`, CALLED. The third: the row's mask form is the run's (`Batt.rowOf`), which begins
    with the 1 + 2 k fresh entries zipped with the walk's coefficients (`run_fields`, CALLED), and
    1 ≤ k by the batching's own test (`of_fits`, CALLED).
Used of `verify-on-bytes`, pure functions: `Psc.hidingWalk`, `Psc.powers`, `Batt.rowOf`.

What is not claimed. That the block says yes anywhere. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Law.OwedRowMasks
import Johnson.Desc.K13.Law.Good2
import Johnson.Desc.K13.Law.AtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Road.Hd (powers_cons)
open VerifiableInference.Desc.First (S)

/-- At one variable or more the hiding walk's list of coefficients is not empty. -/
theorem walk_ne {k : ℕ} {h : Psc.Heard} (hk : 1 ≤ k) (hl : h.rounds.length = k) :
    (walkOf k h).1 ≠ [] := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  cases hr : h.rounds with
  | nil =>
    rw [hr] at hl
    cases hl
  | cons a l =>
    show (Psc.hidingWalk ((List.replicate (k' + 1) (Psc.Weight.plain 3)).zip
      (h.rounds.map (·.2)))).1 ≠ []
    rw [hr, List.replicate_succ, List.map_cons, List.zip_cons_cons]
    cases (List.replicate k' (Psc.Weight.plain 3)).zip (l.map (·.2)) with
    | nil =>
      show Psc.powers oneE a.2 (2 + 1) ≠ []
      rw [powers_cons]
      exact List.cons_ne_nil _ _
    | cons q rest =>
      show Psc.powers (mulE (Psc.hidingWalk (q :: rest)).2 a.2) a.2 (1 + 1) ++
        (Psc.hidingWalk (q :: rest)).1 ≠ []
      rw [powers_cons, List.cons_append]
      exact List.cons_ne_nil _ _

/-- Two lists that are not empty, zipped, in front of a third. -/
theorem zip_append_ne {α β : Type} {a : List α} {b : List β} (c : List (α × β)) (ha : a ≠ [])
    (hb : b ≠ []) : a.zip b ++ c ≠ [] := by
  cases a with
  | nil => exact absurd rfl ha
  | cons x a =>
    cases b with
    | nil => exact absurd rfl hb
    | cons y b =>
      rw [List.zip_cons_cons, List.cons_append]
      exact List.cons_ne_nil _ _

/-- **Behind a yes of kind K13's block: one row; on the index masks' message alone; with a mask
entry.** -/
theorem rowMasks : OwedRowMasks := by
  intro Cl P s s' rs gs h
  obtain ⟨out, hb, _, hr⟩ := atM3_ok h
  obtain ⟨r, rs', x, t, hd, o, _, _, hfit, _, _, _, _, hrun, _, rfl⟩ := batt_ok hb
  obtain ⟨_, _, _, _, e⟩ := atM3_rec h
  have ho : s'.out = s.out := by rw [e]
  refine ⟨Batt.rowOf s.out.pending o, hr, ?_, ?_⟩
  · rw [ho]
    exact rowOf_onLedger hfit (atM3_ledger h) hrun
  · obtain ⟨h1, _, h3, _, h5, _, _⟩ := run_fields hfit hrun
    obtain ⟨_, hk, _⟩ := of_fits x hfit
    show o.rowMasks ≠ []
    rw [h5]
    refine zip_append_ne _ (fun h0 => ?_) (walk_ne hk h1)
    rw [h0] at h3
    exact absurd h3 (by simp only [List.length_nil]; omega)

end VerifiableInference.Desc.K13.Law
