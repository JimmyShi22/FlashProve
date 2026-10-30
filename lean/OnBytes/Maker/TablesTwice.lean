-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TablesTwice.lean: under the hypothesis `SameTwice` the test `sameTwice` passes in each
of the four tables of OnBytes/Maker/Tables.lean, so that the tables return where their other tests
pass.

Statements and proofs. `SameTwice W r` speaks of the file as read and of the data's numbering:
wherever two listed entries, in one opening or in two, stand at one position of one tree by the
data's number, or of the stored table, they hold one column and one salt. The test
`sameTwice` speaks of a table that is made of these openings. Here the first is shown to give the
second.

Main names:
  `sameTwice_of`: the test passes at a table in which two rows at one position have one column and
    one typed salt.
  `table_listed`: a row of an opening's table comes from what the opening lists at that position.
  `merged_twice`: the test passes at each tree's table, for rows made by `tableOf` or by
    `tableOfFull`.
  `tabsW_of_twice`, `tabsWFull_of_twice`, `extTabW_of_twice`, `extTabWFull_of_twice`: each of the
    four returns, if the chains fit, every opening passes its tests, every opening's table is made,
    and `SameTwice` holds.
Limits: `SameTwice` stays a hypothesis: it is proved of no file, and it does not follow from a
reading that returns, which has one digest of a leaf at a position that is listed twice, not one
column. Nothing on soundness.


-/
import OnBytes.Maker.Tables

set_option autoImplicit false

namespace OnBytes.Maker

open Iop Rom Compile
open _root_.Run (OpenB Row3 atT pathFrom leafSalt)

/-! ## Lists -/

/-- A key that stands in a list of pairs is found, with a value that stands there under it. -/
theorem lookup_of_mem {β : Type} : ∀ (tab : List (ℕ × β)) (k : ℕ) (v : β), (k, v) ∈ tab →
    ∃ z, tab.lookup k = some z ∧ (k, z) ∈ tab
  | [], _, _, h => by cases h
  | (k', v') :: l, k, v, h => by
    by_cases e : k = k'
    · subst e
      exact ⟨v', by simp, List.mem_cons_self⟩
    · have hl : (k, v) ∈ l := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd (congrArg Prod.fst h) e
        · exact h
      obtain ⟨z, h1, h2⟩ := lookup_of_mem l k v hl
      have hb : (k == k') = false := _root_.beq_false_of_ne e
      exact ⟨z, by rw [List.lookup_cons, hb]; exact h1, List.mem_cons_of_mem _ h2⟩

/-- What a function that returns at a whole list has returned comes from the list's members. -/
theorem mapM_from {α β : Type} (f : α → Option β) : ∀ (l : List α) (ys : List β),
    l.mapM f = some ys → ∀ y ∈ ys, ∃ x ∈ l, f x = some y
  | [], ys, e, y, hy => by
    obtain rfl : [] = ys := Option.some.inj e
    cases hy
  | a :: l, ys, e, y, hy => by
    rw [List.mapM_cons] at e
    cases h1 : f a with
    | none => rw [h1] at e; cases e
    | some b =>
      rw [h1] at e
      cases h2 : l.mapM f with
      | none => rw [h2] at e; cases e
      | some bs =>
        rw [h2] at e
        obtain rfl : b :: bs = ys := Option.some.inj e
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨a, List.mem_cons_self, h1⟩
        · obtain ⟨x, hx, hf⟩ := mapM_from f l bs h2 y hy
          exact ⟨x, List.mem_cons_of_mem _ hx, hf⟩

/-- Four lists laid side by side, the third under a function: without the fourth, and before the
function. -/
theorem zip4_mem {α β γ δ ε : Type} (f : γ → ε) : ∀ (A : List α) (B : List β) (C : List γ)
    (E : List δ) (a : α) (b : β) (e : ε) (d : δ),
    (a, b, e, d) ∈ A.zip (B.zip ((C.map f).zip E)) → ∃ c, (a, b, c) ∈ A.zip (B.zip C) ∧ e = f c
  | [], _, _, _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, _, _, h => by simp at h
  | _ :: _, _ :: _, [], _, _, _, _, _, h => by simp at h
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, h => by simp at h
  | a0 :: A, b0 :: B, c0 :: C, d0 :: E, a, b, e, d, h => by
    rw [List.map_cons, List.zip_cons_cons, List.zip_cons_cons, List.zip_cons_cons] at h
    rw [List.zip_cons_cons, List.zip_cons_cons]
    rcases List.mem_cons.1 h with h | h
    · obtain ⟨e1, e2⟩ := Prod.mk.inj h
      obtain ⟨e3, e4⟩ := Prod.mk.inj e2
      obtain ⟨e5, -⟩ := Prod.mk.inj e4
      exact ⟨c0, by rw [e1, e3]; exact List.mem_cons_self, e5⟩
    · obtain ⟨c, hc, he⟩ := zip4_mem f A B C E a b e d h
      exact ⟨c, List.mem_cons_of_mem _ hc, he⟩

/-! ## One table -/

/-- The test passes at a table in which two rows at one position have one column and one typed
salt. -/
theorem sameTwice_of {tab : List (ℕ × Row3)}
    (H : ∀ i a b, (i, a) ∈ tab → (i, b) ∈ tab → a.1 = b.1 ∧ a.2.1 = b.2.1) :
    sameTwice tab = true := by
  unfold sameTwice
  rw [List.all_eq_true]
  intro y hy
  obtain ⟨z, h1, h2⟩ := lookup_of_mem tab y.1 y.2 hy
  obtain ⟨e1, e2⟩ := H y.1 z y.2 h2 hy
  rw [h1]
  show (z.1 == y.2.1 && z.2.1 == y.2.2.1) = true
  rw [e1, e2]
  simp

/-- A row of an opening's table comes from what the opening lists at that position: the column is
the listed one, and the typed salt is the start and then the listed salt. -/
theorem table_listed (x : Opened) (start : ByteArray) (ps : List (List (Dig 256))) (i : ℕ)
    (a : Row3) (h : (i, a) ∈ (asOpenB x).table start ps) :
    ∃ s, (i, a.1, s) ∈ listed x ∧ a.2.1 = leafSalt start s := by
  obtain ⟨c, sl, p⟩ := a
  exact zip4_mem (leafSalt start) x.2.1 x.2.2.cols x.2.2.salts ps i c sl p h

/-! ## The trees' tables -/

/-- What both makers of an opening's table do. -/
def MakesTable (W : Three.Whole) (r : Proof.TailRead)
    (g : ℕ × Opened → Option (ℕ × List (ℕ × Row3))) : Prop :=
  ∀ x row, g x = some row → row.1 = x.1 ∧
    ∃ run ps, runOfTree W r x.1 = some run ∧ row.2 = (asOpenB x.2).table run ps

theorem tableOf_makes (W : Three.Whole) (r : Proof.TailRead) : MakesTable W r (tableOf W r) := by
  intro x row h
  unfold tableOf at h
  cases hr : runOfTree W r x.1 with
  | none => rw [hr] at h; cases h
  | some run =>
    rw [hr] at h
    obtain rfl := Option.some.inj h
    exact ⟨rfl, run, _, rfl, rfl⟩

theorem tableOfFull_makes (W : Three.Whole) (r : Proof.TailRead) :
    MakesTable W r (tableOfFull W r) := by
  intro x row h
  unfold tableOfFull at h
  cases hr : runOfTree W r x.1 with
  | none => rw [hr] at h; cases h
  | some run =>
    rw [hr] at h
    cases hp : fullPaths x.2 with
    | none =>
      rw [Option.bind_some, hp] at h
      cases h
    | some ps =>
      rw [Option.bind_some, hp] at h
      obtain rfl := Option.some.inj h
      exact ⟨rfl, run, ps, rfl, rfl⟩

/-- **The test passes at each tree's table.** -/
theorem merged_twice (W : Three.Whole) (r : Proof.TailRead)
    (g : ℕ × Opened → Option (ℕ × List (ℕ × Row3))) (hg : MakesTable W r g) (T : SameTwice W r)
    (rows : List (ℕ × List (ℕ × Row3))) (hm : (ownRowsW W r).mapM g = some rows) :
    (merged rows).all (fun t => sameTwice t.2) = true := by
  rw [List.all_eq_true]
  intro t ht
  unfold merged at ht
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 ht
  have from_ : ∀ i (a : Row3), (i, a) ∈ (rows.filter (·.1 == j)).flatMap (·.2) →
      ∃ x ∈ ownRowsW W r, x.1 = j ∧ ∃ run s, runOfTree W r j = some run ∧
        (i, a.1, s) ∈ listed x.2 ∧ a.2.1 = leafSalt run s := by
    intro i a ha
    obtain ⟨row, hrow, hin⟩ := List.mem_flatMap.1 ha
    obtain ⟨hr1, hr2⟩ := List.mem_filter.1 hrow
    have ej : row.1 = j := by simpa using hr2
    obtain ⟨x, hx, hgx⟩ := mapM_from g _ rows hm row hr1
    obtain ⟨e1, run, ps, e2, e3⟩ := hg x row hgx
    rw [e3] at hin
    obtain ⟨s, hs, hsl⟩ := table_listed x.2 run ps i a hin
    have exj : x.1 = j := e1.symm.trans ej
    exact ⟨x, hx, exj, run, s, exj ▸ e2, hs, hsl⟩
  refine sameTwice_of fun i a b ha hb => ?_
  obtain ⟨x, hx, ex, run, s, hr, hs, hsl⟩ := from_ i a ha
  obtain ⟨x', hx', ex', run', s', hr', hs', hsl'⟩ := from_ i b hb
  obtain rfl : run = run' := Option.some.inj (hr.symm.trans hr')
  have e := T.1 x hx x' hx' (ex.trans ex'.symm) _ hs _ hs' rfl
  obtain ⟨e1, e2⟩ := Prod.mk.inj e
  exact ⟨e1, by rw [hsl, hsl', e2]⟩

/-- **`tabsW` returns**, if the chains fit, every opening passes its tests, every opening's table is
made, and `SameTwice` holds. -/
theorem tabsW_of_twice (W : Three.Whole) (saltBytes : ℕ) (r : Proof.TailRead)
    (hf : fitsW W r = true) (ho : (ownRowsW W r).all (rowOK W saltBytes) = true)
    (rows : List (ℕ × List (ℕ × Row3)))
    (hm : (ownRowsW W r).mapM (tableOf W r) = some rows) (T : SameTwice W r) :
    tabsW W saltBytes r = some (merged rows) := by
  unfold tabsW
  rw [hf, ho, hm]
  show (if (merged rows).all (fun t => sameTwice t.2) = true then some (merged rows) else none) = _
  rw [if_pos (merged_twice W r _ (tableOf_makes W r) T rows hm)]

/-- **`tabsWFull` returns**, under the same. -/
theorem tabsWFull_of_twice (W : Three.Whole) (saltBytes : ℕ) (r : Proof.TailRead)
    (hf : fitsW W r = true) (ho : (ownRowsW W r).all (rowOK W saltBytes) = true)
    (rows : List (ℕ × List (ℕ × Row3)))
    (hm : (ownRowsW W r).mapM (tableOfFull W r) = some rows) (T : SameTwice W r) :
    tabsWFull W saltBytes r = some (merged rows) := by
  unfold tabsWFull
  rw [hf, ho, hm]
  show (if (merged rows).all (fun t => sameTwice t.2) = true then some (merged rows) else none) = _
  rw [if_pos (merged_twice W r _ (tableOfFull_makes W r) T rows hm)]

/-! ## The stored table's -/

/-- The test passes at tables of the stored table's openings laid behind each other. -/
theorem stored_twice (W : Three.Whole) (r : Proof.TailRead) (cfg : ByteArray) (T : SameTwice W r)
    (tab : List (ℕ × Row3))
    (hx : ∀ i a, (i, a) ∈ tab → ∃ x ∈ storedRowsW W r, ∃ ps, (i, a) ∈ (asOpenB x.2).table cfg ps) :
    sameTwice tab = true := by
  refine sameTwice_of fun i a b ha hb => ?_
  obtain ⟨x, mx, ps, hxa⟩ := hx i a ha
  obtain ⟨x', mx', ps', hxb⟩ := hx i b hb
  obtain ⟨s, hs, hsl⟩ := table_listed x.2 cfg ps i a hxa
  obtain ⟨s', hs', hsl'⟩ := table_listed x'.2 cfg ps' i b hxb
  have e := T.2 x mx x' mx' _ hs _ hs' rfl
  obtain ⟨e1, e2⟩ := Prod.mk.inj e
  exact ⟨e1, by rw [hsl, hsl', e2]⟩

/-- **`extTabW` returns**, if the chains fit, every opening of the stored table passes its tests,
and `SameTwice` holds. -/
theorem extTabW_of_twice (a : ℕ) (cfg : ByteArray) (W : Three.Whole) (r : Proof.TailRead)
    (hf : fitsW W r = true) (ho : (storedRowsW W r).all (storedOK a) = true) (T : SameTwice W r) :
    extTabW a cfg W r =
      some ((storedRowsW W r).flatMap fun x => (asOpenB x.2).table cfg (asOpenB x.2).paths) := by
  unfold extTabW
  rw [hf, ho]
  show (if sameTwice ((storedRowsW W r).flatMap fun x =>
      (asOpenB x.2).table cfg (asOpenB x.2).paths) = true then _ else none) = _
  rw [if_pos (stored_twice W r cfg T _ fun i b hb => by
    obtain ⟨x, hx, hin⟩ := List.mem_flatMap.1 hb
    exact ⟨x, hx, _, hin⟩)]

/-- **`extTabWFull` returns**, if also every opening's whole paths are there. -/
theorem extTabWFull_of_twice (a : ℕ) (cfg : ByteArray) (W : Three.Whole) (r : Proof.TailRead)
    (hf : fitsW W r = true) (ho : (storedRowsW W r).all (storedOK a) = true)
    (ts : List (List (ℕ × Row3)))
    (hm : ((storedRowsW W r).mapM fun x =>
      (fullPaths x.2).map fun ps => (asOpenB x.2).table cfg ps) = some ts) (T : SameTwice W r) :
    extTabWFull a cfg W r = some ts.flatten := by
  unfold extTabWFull
  rw [hf, ho, hm]
  show (if sameTwice ts.flatten = true then some ts.flatten else none) = _
  rw [if_pos (stored_twice W r cfg T _ fun i b hb => by
    obtain ⟨t, ht, hin⟩ := List.mem_flatten.1 hb
    obtain ⟨x, hx, hfx⟩ := mapM_from _ _ ts hm t ht
    cases hp : fullPaths x.2 with
    | none => rw [hp] at hfx; cases hfx
    | some ps =>
      rw [hp] at hfx
      obtain rfl := Option.some.inj hfx
      exact ⟨x, hx, ps, hin⟩)]

end OnBytes.Maker
