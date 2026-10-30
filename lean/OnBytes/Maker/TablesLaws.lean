-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TablesLaws.lean: what the tables of OnBytes/Maker/Tables.lean hold.

`tabsW` and `tabsWFull` lay all openings of the trees of a file into one list of tables, keyed by
the tree's number over the whole file; `extTabW` and `extTabWFull` lay the stored table's openings
into one table. The two forms differ in the paths alone. This file shows: if one of them returns,
then every column that an opening of the file lists at a place is what a look-up finds at that
place.

Main definitions: `TabsHold`, `ExtHolds`: what such tables hold, whichever paths they have.
Main theorems.
  `lookup_self`, `merged_lookup`, `mem_of_lookup`, `merged_row`: the look-up in `merged`.
  `sameTwice_lookup`: in a table that passes `sameTwice`, the look-up at a row's place finds that
    row's column and salt.
  `table_row`: a listed column of an opening has a row in the opening's table, whatever the paths.
  `mapM_mem`, `mapM_length`: what a list of results holds.
  `rowOK_spec`, `storedOK_spec`: what the tests on one opening say.
  `tabsW_holds`, `tabsWFull_holds`, `extTabW_holds`, `extTabWFull_holds`.

The laws read a row's column, and say that there is a salt and a path.
No other file calls `tabsW_holds` or `extTabW_holds`.

What is not claimed. That any of the four returns. Nothing on hashes or roots, or on soundness.


-/
import OnBytes.Maker.Tables
import Run.PageIsViewProofs

set_option autoImplicit false

namespace OnBytes.Maker

open Iop Compile
open _root_.Run (OpenB Row3 atT)
open _root_.Run.PQ (SgX mem_zip_ext)

/-- The look-up in a list of pairs "a number, a function's value at it". -/
theorem lookup_self {β : Type} (f : ℕ → β) : ∀ (l : List ℕ) (j : ℕ), j ∈ l →
    (l.map fun i => (i, f i)).lookup j = some (f j)
  | [], _, h => by cases h
  | a :: l, j, h => by
    rw [List.map_cons, List.lookup_cons]
    by_cases e : j = a
    · subst e
      rw [beq_self_eq_true]
    · rw [beq_eq_false_iff_ne.2 e]
      exact lookup_self f l j ((List.mem_cons.1 h).resolve_left e)

/-- Under a number that some row bears, `merged` has the tables under that number, appended. -/
theorem merged_lookup (rows : List (ℕ × List (ℕ × Row3))) (j : ℕ) (h : j ∈ rows.map (·.1)) :
    (merged rows).lookup j = some ((rows.filter (·.1 == j)).flatMap (·.2)) := by
  unfold merged
  exact lookup_self
    (fun i : ℕ => (rows.filter fun x : ℕ × List (ℕ × Row3) => x.1 == i).flatMap fun x => x.2)
    _ j (List.mem_eraseDups.2 h)

/-- What a look-up finds is a member. -/
theorem mem_of_lookup {β : Type} : ∀ (l : List (ℕ × β)) (j : ℕ) (b : β),
    l.lookup j = some b → (j, b) ∈ l
  | [], _, _, h => by cases h
  | (a, b0) :: l, j, b, h => by
    rw [List.lookup_cons] at h
    by_cases e : j = a
    · subst e
      rw [beq_self_eq_true] at h
      cases h
      exact List.mem_cons_self
    · rw [beq_eq_false_iff_ne.2 e] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup l j b h)

/-- In a table that passes `sameTwice`, the look-up at a row's place finds the row's column and
salt. -/
theorem sameTwice_lookup (tab : List (ℕ × Row3)) (h : sameTwice tab = true) (x : ℕ)
    (c : List UInt64) (s : Rom.Bits) (pt : List (Dig 256)) (hm : (x, c, s, pt) ∈ tab) :
    ∃ pt', tab.lookup x = some (c, s, pt') := by
  have h1 := List.all_eq_true.1 h _ hm
  dsimp only at h1
  cases e : tab.lookup x with
  | none => rw [e] at h1; cases h1
  | some z =>
    rw [e] at h1
    obtain ⟨z1, z2, z3⟩ := z
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    exact ⟨z3, by rw [h1.1, h1.2]⟩

/-- A listed column of an opening has a row in the opening's table, whatever the paths are, if there
are as many columns and salts as places, and no fewer paths. -/
theorem table_row (O : OpenB) (run : ByteArray) (paths : List (List (Dig 256)))
    (h1 : O.cols.length = O.idx.length) (h2 : O.salts.length = O.idx.length)
    (h3 : O.idx.length ≤ paths.length) (x : ℕ) (c : List UInt64) (hm : (x, c) ∈ O.idx.zip O.cols) :
    ∃ s pt, (x, c, s, pt) ∈ O.table run paths := by
  obtain ⟨⟨s, pt⟩, hc⟩ := mem_zip_ext O.idx O.cols
    ((O.salts.map (_root_.Run.leafSalt run)).zip paths) x c hm
    (by rw [List.length_zip, List.length_map]; omega)
  exact ⟨s, pt, hc⟩

/-- If a function gives a value at every member of a list, each member's value is in the list of
values. -/
theorem mapM_mem {α β : Type} (f : α → Option β) : ∀ (l : List α) (bs : List β),
    l.mapM f = some bs → ∀ a ∈ l, ∃ b ∈ bs, f a = some b
  | [], _, _, _, ha => by cases ha
  | a0 :: l, bs, h, a, ha => by
    rw [List.mapM_cons] at h
    cases e0 : f a0 with
    | none => rw [e0] at h; cases h
    | some b0 =>
      cases e1 : l.mapM f with
      | none => rw [e0, e1] at h; cases h
      | some bs0 =>
        rw [e0, e1] at h
        have hb : bs = b0 :: bs0 := (Option.some.inj h).symm
        subst hb
        rcases List.mem_cons.1 ha with e | ha'
        · subst e
          exact ⟨b0, List.mem_cons_self, e0⟩
        · obtain ⟨b, hb, hf⟩ := mapM_mem f l bs0 e1 a ha'
          exact ⟨b, List.mem_cons_of_mem _ hb, hf⟩

/-- The list of values is as long as the list. -/
theorem mapM_length {α β : Type} (f : α → Option β) : ∀ (l : List α) (bs : List β),
    l.mapM f = some bs → bs.length = l.length
  | [], bs, h => by
    rw [List.mapM_nil] at h
    cases h
    rfl
  | a0 :: l, bs, h => by
    rw [List.mapM_cons] at h
    cases e0 : f a0 with
    | none => rw [e0] at h; cases h
    | some b0 =>
      cases e1 : l.mapM f with
      | none => rw [e0, e1] at h; cases h
      | some bs0 =>
        rw [e0, e1] at h
        have hb : bs = b0 :: bs0 := (Option.some.inj h).symm
        subst hb
        rw [List.length_cons, List.length_cons, mapM_length f l bs0 e1]

/-- The look-up in `merged`, where each of its tables passes `sameTwice`: a row of a table under j
is found under j, with its column and salt. -/
theorem merged_row (rows : List (ℕ × List (ℕ × Row3)))
    (hs : ∀ t ∈ merged rows, sameTwice t.2 = true) (j : ℕ) (tb : List (ℕ × Row3))
    (hrow : (j, tb) ∈ rows) (x : ℕ) (c : List UInt64) (s : Rom.Bits) (pt : List (Dig 256))
    (hin : (x, c, s, pt) ∈ tb) :
    ∃ tab pt', (merged rows).lookup j = some tab ∧ tab.lookup x = some (c, s, pt') := by
  have hl := merged_lookup rows j (List.mem_map.2 ⟨_, hrow, rfl⟩)
  have hmem : (x, c, s, pt) ∈ (rows.filter (·.1 == j)).flatMap (·.2) :=
    List.mem_flatMap.2 ⟨_, List.mem_filter.2 ⟨hrow, beq_self_eq_true j⟩, hin⟩
  obtain ⟨pt', hp⟩ := sameTwice_lookup _ (hs (j, _) (mem_of_lookup _ _ _ hl)) x c s pt hmem
  exact ⟨_, pt', hl, hp⟩

/-! ## What the tables hold -/

/-- **What tables of the trees' openings hold**, whichever paths they have: the three chains fit the
data; each opening of a tree has passed its tests (the tree is in the data's table, the shape as
read is the table's, the library's own test on an opening); a column that an opening of the tree
number j lists at the place x is what the look-up finds under j at x. -/
structure TabsHold (W : Three.Whole) (sb : ℕ) (r : Proof.TailRead)
    (tabs : List (ℕ × List (ℕ × Row3))) : Prop where
  fits : fitsW W r = true
  row : ∀ j z, (j, z) ∈ ownRowsW W r →
    ∃ t, W.table[j]? = some t ∧ z.1 = t.shape ∧ (asOpenB z).ok sb t.shape.W = true
  look : ∀ j z, (j, z) ∈ ownRowsW W r → ∀ x c, (x, c) ∈ z.2.1.zip z.2.2.cols →
    ∃ tab s pt, tabs.lookup j = some tab ∧ tab.lookup x = some (c, s, pt)

/-- **What a table of the stored table's openings holds.** -/
structure ExtHolds (a : ℕ) (W : Three.Whole) (r : Proof.TailRead) (tab : List (ℕ × Row3)) :
    Prop where
  row : ∀ t z, (t, z) ∈ storedRowsW W r →
    z.1 = t.sh ∧ t.sh.a = a ∧ t.item = 0 ∧ (asOpenB z).ok t.salt t.sh.W = true
  look : ∀ t z, (t, z) ∈ storedRowsW W r → ∀ x c, (x, c) ∈ z.2.1.zip z.2.2.cols →
    ∃ s pt, tab.lookup x = some (c, s, pt)

/-- What `rowOK` says. -/
theorem rowOK_spec {W : Three.Whole} {sb : ℕ} {j : ℕ} {z : Opened} (h : rowOK W sb (j, z) = true) :
    ∃ t, W.table[j]? = some t ∧ z.1 = t.shape ∧ (asOpenB z).ok sb t.shape.W = true := by
  unfold rowOK at h
  dsimp only at h
  cases e : W.table[j]? with
  | none => rw [e] at h; cases h
  | some t =>
    rw [e] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨t, rfl, h.1, h.2⟩

/-- What `storedOK` says. -/
theorem storedOK_spec {a : ℕ} {t : Fmt.Stored} {z : Opened} (h : storedOK a (t, z) = true) :
    z.1 = t.sh ∧ t.sh.a = a ∧ t.item = 0 ∧ (asOpenB z).ok t.salt t.sh.W = true := by
  unfold storedOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- As many whole paths as listed places. -/
theorem fullPaths_length {z : Opened} {ps : List (List (Dig 256))} (h : fullPaths z = some ps) :
    ps.length = z.2.1.length := mapM_length _ _ _ h

section
variable {W : Three.Whole} {sb : ℕ} {r : Proof.TailRead} {tabs : List (ℕ × List (ℕ × Row3))}

/-- **`tabsW`'s tables hold the file's columns.** -/
theorem tabsW_holds (h : tabsW W sb r = some tabs) : TabsHold W sb r tabs := by
  unfold tabsW at h
  split at h
  · rename_i h0
    rw [Bool.and_eq_true] at h0
    obtain ⟨rows, hr, h1⟩ := Option.bind_eq_some_iff.1 h
    split at h1
    · rename_i h2
      obtain rfl := Option.some.inj h1
      have hrow := fun j z (hz : (j, z) ∈ ownRowsW W r) => rowOK_spec (List.all_eq_true.1 h0.2 _ hz)
      refine ⟨h0.1, hrow, fun j z hz x c hm => ?_⟩
      obtain ⟨t, -, -, hok⟩ := hrow j z hz
      obtain ⟨row, hin, hf⟩ := mapM_mem _ _ _ hr _ hz
      unfold tableOf at hf
      obtain ⟨run, -, rfl⟩ := Option.map_eq_some_iff.1 hf
      obtain ⟨o1, o2, -, -, -⟩ := _root_.Run.TieTree.ok_spec (asOpenB z) sb t.shape.W hok
      obtain ⟨s, pt, hx⟩ := table_row (asOpenB z) run (asOpenB z).paths o1 o2
        (Nat.le_of_eq (Octopus.length_fill _ _ _).symm) x c hm
      obtain ⟨tab, pt', e1, e2⟩ := merged_row rows (List.all_eq_true.1 h2) j _ hin x c s pt hx
      exact ⟨tab, s, pt', e1, e2⟩
    · cases h1
  · cases h

/-- **`tabsWFull`'s tables hold the file's columns.** -/
theorem tabsWFull_holds (h : tabsWFull W sb r = some tabs) : TabsHold W sb r tabs := by
  unfold tabsWFull at h
  split at h
  · rename_i h0
    rw [Bool.and_eq_true] at h0
    obtain ⟨rows, hr, h1⟩ := Option.bind_eq_some_iff.1 h
    split at h1
    · rename_i h2
      obtain rfl := Option.some.inj h1
      have hrow := fun j z (hz : (j, z) ∈ ownRowsW W r) => rowOK_spec (List.all_eq_true.1 h0.2 _ hz)
      refine ⟨h0.1, hrow, fun j z hz x c hm => ?_⟩
      obtain ⟨t, -, -, hok⟩ := hrow j z hz
      obtain ⟨row, hin, hf⟩ := mapM_mem _ _ _ hr _ hz
      unfold tableOfFull at hf
      obtain ⟨run, -, hf'⟩ := Option.bind_eq_some_iff.1 hf
      obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.1 hf'
      obtain ⟨o1, o2, -, -, -⟩ := _root_.Run.TieTree.ok_spec (asOpenB z) sb t.shape.W hok
      obtain ⟨s, pt, hx⟩ := table_row (asOpenB z) run ps o1 o2
        (Nat.le_of_eq (fullPaths_length hps).symm) x c hm
      obtain ⟨tab, pt', e1, e2⟩ := merged_row rows (List.all_eq_true.1 h2) j _ hin x c s pt hx
      exact ⟨tab, s, pt', e1, e2⟩
    · cases h1
  · cases h

end

section
variable {a : ℕ} {cfg : ByteArray} {W : Three.Whole} {r : Proof.TailRead} {tab : List (ℕ × Row3)}

/-- **`extTabW`'s table holds the file's columns.** -/
theorem extTabW_holds (h : extTabW a cfg W r = some tab) : ExtHolds a W r tab := by
  unfold extTabW at h
  split at h
  · rename_i h0
    rw [Bool.and_eq_true] at h0
    dsimp only at h
    split at h
    · rename_i h2
      obtain rfl := Option.some.inj h
      have hrow := fun t z (hz : (t, z) ∈ storedRowsW W r) =>
        storedOK_spec (List.all_eq_true.1 h0.2 _ hz)
      refine ⟨hrow, fun t z hz x c hm => ?_⟩
      obtain ⟨-, -, -, hok⟩ := hrow t z hz
      obtain ⟨o1, o2, -, -, -⟩ := _root_.Run.TieTree.ok_spec (asOpenB z) t.salt t.sh.W hok
      obtain ⟨s, pt, hx⟩ := table_row (asOpenB z) cfg (asOpenB z).paths o1 o2
        (Nat.le_of_eq (Octopus.length_fill _ _ _).symm) x c hm
      obtain ⟨pt', hp⟩ := sameTwice_lookup _ h2 x c s pt (List.mem_flatMap.2 ⟨_, hz, hx⟩)
      exact ⟨s, pt', hp⟩
    · cases h
  · cases h

/-- **`extTabWFull`'s table holds the file's columns.** -/
theorem extTabWFull_holds (h : extTabWFull a cfg W r = some tab) : ExtHolds a W r tab := by
  unfold extTabWFull at h
  split at h
  · rename_i h0
    rw [Bool.and_eq_true] at h0
    obtain ⟨ts, hr, h1⟩ := Option.bind_eq_some_iff.1 h
    split at h1
    · rename_i h2
      obtain rfl := Option.some.inj h1
      have hrow := fun t z (hz : (t, z) ∈ storedRowsW W r) =>
        storedOK_spec (List.all_eq_true.1 h0.2 _ hz)
      refine ⟨hrow, fun t z hz x c hm => ?_⟩
      obtain ⟨-, -, -, hok⟩ := hrow t z hz
      obtain ⟨tb, hin, hf⟩ := mapM_mem _ _ _ hr _ hz
      obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.1 hf
      obtain ⟨o1, o2, -, -, -⟩ := _root_.Run.TieTree.ok_spec (asOpenB z) t.salt t.sh.W hok
      obtain ⟨s, pt, hx⟩ := table_row (asOpenB z) cfg ps o1 o2
        (Nat.le_of_eq (fullPaths_length hps).symm) x c hm
      obtain ⟨pt', hp⟩ := sameTwice_lookup _ h2 x c s pt (List.mem_flatten.2 ⟨_, hin, hx⟩)
      exact ⟨s, pt', hp⟩
    · cases h1
  · cases h

end

end OnBytes.Maker
