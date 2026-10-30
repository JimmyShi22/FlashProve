-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TablesReturn.lean: the tables with whole paths of OnBytes/Maker/Tables.lean return,
under a list of premises on the file as read.

Statements and proofs. Each premise but the last is a fact that a reading gives or a test on the
plain data; where it is proved is said beside it.

Main names:
  `runOfTree_some`: the sender of a tree that is in the table has a run's value, if the three
    chains have one.
  `tabsWFull_isSome`: `tabsWFull W sb r` returns, if (1) the chains fit the data (`fitsW`); (2)
    every opening of a tree passes `rowOK`; (3) each of the three chains has a run's value
    (`RunsThere`; of a chain read under a description with random bytes:
    OnBytes/Maker/ReadTrace.lean, `readChain_run`; OnBytes/Maker/ReadData.lean, `described_run`);
    (4) every opening's whole paths are there (OnBytes/Maker/ReadWalks.lean, `walked_full`);
    (5) `SameTwice W r`.
  `extTabWFull_isSome`, `extWFull_isSome`: the like for the stored table: (1); every opening of the
    stored table passes `storedOK`; (4); (5).
Limits: (1) and (2) are premises here: that a reading which returns meets them is not proved in this
file. (5) is a hypothesis that no reading gives (OnBytes/Maker/TablesTwice.lean). Nothing is said of
what the tables hold. Nothing on soundness.


-/
import OnBytes.Maker.TablesTwice

set_option autoImplicit false

namespace OnBytes.Maker

open Iop Rom Compile
open _root_.Run (OpenB Row3 atT pathFrom leafSalt)

/-- A function that returns at each member of a list returns at the list. -/
theorem mapM_returns {α β : Type} (f : α → Option β) : ∀ l : List α,
    (∀ x ∈ l, ∃ y, f x = some y) → ∃ ys, l.mapM f = some ys
  | [], _ => ⟨[], rfl⟩
  | a :: l, hl => by
    obtain ⟨y, hy⟩ := hl a List.mem_cons_self
    obtain ⟨ys, hys⟩ := mapM_returns f l fun x hx => hl x (List.mem_cons_of_mem _ hx)
    exact ⟨y :: ys, by rw [List.mapM_cons, hy, hys]; rfl⟩

/-- Each of the three chains as read has a run's value. -/
def RunsThere (r : Proof.TailRead) : Prop :=
  (∃ x, r.first.out.run = some x) ∧ (∃ x, r.shared.out.run = some x) ∧
    ∃ x, r.second.out.run = some x

theorem chainOf_run {r : Proof.TailRead} (R : RunsThere r) : ∀ c, ∃ x, (chainOf r c).run = some x
  | 0 => R.1
  | 1 => R.2.1
  | _ + 2 => R.2.2

/-- The sender of a tree that is in the table has a run's value. -/
theorem runOfTree_some (W : Three.Whole) (sb : ℕ) (r : Proof.TailRead) (R : RunsThere r)
    (x : ℕ × Opened) (h : rowOK W sb x = true) : ∃ run, runOfTree W r x.1 = some run := by
  unfold rowOK at h
  unfold runOfTree
  cases ht : W.table[x.1]? with
  | none => rw [ht] at h; cases h
  | some t => exact chainOf_run R t.chain

/-- **The trees' tables with whole paths return.** -/
theorem tabsWFull_isSome (W : Three.Whole) (sb : ℕ) (r : Proof.TailRead) (hf : fitsW W r = true)
    (ho : ∀ x ∈ ownRowsW W r, rowOK W sb x = true) (R : RunsThere r)
    (hp : ∀ x ∈ ownRowsW W r, ∃ ps, fullPaths x.2 = some ps) (T : SameTwice W r) :
    (tabsWFull W sb r).isSome = true := by
  obtain ⟨rows, hm⟩ := mapM_returns (tableOfFull W r) (ownRowsW W r) fun x hx => by
    obtain ⟨run, h1⟩ := runOfTree_some W sb r R x (ho x hx)
    obtain ⟨ps, h2⟩ := hp x hx
    exact ⟨_, by unfold tableOfFull; rw [h1, Option.bind_some, h2]; rfl⟩
  rw [tabsWFull_of_twice W sb r hf (List.all_eq_true.2 ho) rows hm T]
  rfl

/-- **The stored table's openings as one table, with whole paths, return.** -/
theorem extTabWFull_isSome (a : ℕ) (cfg : ByteArray) (W : Three.Whole) (r : Proof.TailRead)
    (hf : fitsW W r = true) (ho : ∀ x ∈ storedRowsW W r, storedOK a x = true)
    (hp : ∀ x ∈ storedRowsW W r, ∃ ps, fullPaths x.2 = some ps) (T : SameTwice W r) :
    (extTabWFull a cfg W r).isSome = true := by
  obtain ⟨ts, hm⟩ := mapM_returns
    (fun x : Fmt.Stored × Opened => (fullPaths x.2).map fun ps => (asOpenB x.2).table cfg ps)
    (storedRowsW W r) fun x hx => by
      obtain ⟨ps, h2⟩ := hp x hx
      exact ⟨(asOpenB x.2).table cfg ps, by
        show Option.map _ (fullPaths x.2) = _
        rw [h2]
        rfl⟩
  rw [extTabWFull_of_twice a cfg W r hf (List.all_eq_true.2 ho) ts hm T]
  rfl

/-- The same as a function of the position. -/
theorem extWFull_isSome (a : ℕ) (cfg : ByteArray) (W : Three.Whole) (r : Proof.TailRead)
    (hf : fitsW W r = true) (ho : ∀ x ∈ storedRowsW W r, storedOK a x = true)
    (hp : ∀ x ∈ storedRowsW W r, ∃ ps, fullPaths x.2 = some ps) (T : SameTwice W r) :
    (extWFull a cfg W r).isSome = true := by
  unfold extWFull
  rw [Option.isSome_map]
  exact extTabWFull_isSome a cfg W r hf ho hp T

end OnBytes.Maker
