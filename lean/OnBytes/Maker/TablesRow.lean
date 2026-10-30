-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TablesRow.lean: a row of the tables of a whole file's openings with whole paths
(OnBytes/Maker/Tables.lean, `tabsWFull`, `extTabWFull`) comes, column, salt and path together, from
one opening of the file.

OnBytes/Maker/TablesBack.lean and OnBytes/Maker/TablesPath.lean each say of a row "there is an
opening of the file such that ..". Here it is one opening for all that a row holds: whoever wants
the leaf's hash and the path off one record of vertices needs that.

  `mem_zip4_all`      a member of four lists zipped: the first three, and the first with the last.
  `TabsRow`, `tabsWFull_row`
                      a row that the look-ups find under the tree j at the place x: ONE opening z of
                      the tree j in the file lists, at x, the row's column and a salt s0 (`listed`);
                      the row's salt is the sender's run's value and then s0; s0 has sb bytes, sb
                      being the number at which the tables were made; the row's path is read out of
                      z's own record at x.
  `ExtRow`, `extTabWFull_row`
                      for the stored table: ONE opening z, beside its description t, lists at x the
                      row's column and a salt s0; the row's salt is cfg and then s0; s0 has t.salt
                      bytes; the path is read out of z's own record at x.
  `TabsRow.back`, `TabsRow.path`, `ExtRow.back`, `ExtRow.path`
                      `TabsBack`, `TabsPath`, `ExtBack`, `ExtPath` follow from these.
  `saltsFit`, `saltsFit_spec`
                      a test on the data alone: every stored table of the three chains' rounds has
                      salts of sb bytes; then so has each stored table that the file opens.

Not claimed. That the tables return a value. Which of several openings that list x it is. Nothing on
hashes; nothing on soundness.


-/
import OnBytes.Maker.TablesPath

set_option autoImplicit false

namespace OnBytes.Maker

open Iop Rom Compile
open _root_.Run (OpenB Row3 atT pathFrom leafSalt)

/-- A member of four lists zipped: the first three, and the first with the last. -/
theorem mem_zip4_all {α β γ δ : Type} : ∀ {l₁ : List α} {l₂ : List β} {l₃ : List γ}
    {l₄ : List δ} {a : α} {b : β} {c : γ} {d : δ},
    (a, b, c, d) ∈ l₁.zip (l₂.zip (l₃.zip l₄)) →
      (a, b, c) ∈ l₁.zip (l₂.zip l₃) ∧ (a, d) ∈ l₁.zip l₄
  | [], _, _, _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, _, _, h => by simp at h
  | _ :: _, _ :: _, [], _, _, _, _, _, h => by simp at h
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, h => by simp at h
  | x :: l₁, y :: l₂, z :: l₃, w :: l₄, a, b, c, d, h => by
    rw [List.zip_cons_cons, List.zip_cons_cons, List.zip_cons_cons] at h
    rw [List.zip_cons_cons, List.zip_cons_cons, List.zip_cons_cons]
    rcases List.mem_cons.1 h with e | h'
    · cases e
      exact ⟨List.mem_cons_self, List.mem_cons_self⟩
    · obtain ⟨h1, h2⟩ := mem_zip4_all h'
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

/-- A member of three lists zipped, the third mapped. -/
theorem mem_zip3_map {α β γ δ : Type} (f : γ → δ) : ∀ {l₁ : List α} {l₂ : List β} {l₃ : List γ}
    {a : α} {b : β} {d : δ}, (a, b, d) ∈ l₁.zip (l₂.zip (l₃.map f)) →
      ∃ c, (a, b, c) ∈ l₁.zip (l₂.zip l₃) ∧ d = f c
  | [], _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h
  | _ :: _, _ :: _, [], _, _, _, h => by simp at h
  | x :: l₁, y :: l₂, z :: l₃, a, b, d, h => by
    rw [List.map_cons, List.zip_cons_cons, List.zip_cons_cons] at h
    rw [List.zip_cons_cons, List.zip_cons_cons]
    rcases List.mem_cons.1 h with e | h'
    · cases e
      exact ⟨z, List.mem_cons_self, rfl⟩
    · obtain ⟨c, h1, h2⟩ := mem_zip3_map f h'
      exact ⟨c, List.mem_cons_of_mem _ h1, h2⟩

/-- A row of one opening's table with whole paths. -/
theorem table_row_all (z : Opened) (run : ByteArray) (ps : List (List (Dig 256)))
    (hps : fullPaths z = some ps) (x : ℕ) (c : List UInt64) (s : Bits) (pt : List (Dig 256))
    (h : (x, c, s, pt) ∈ (asOpenB z).table run ps) :
    ∃ s0, (x, c, s0) ∈ listed z ∧ s = leafSalt run s0 ∧
      pathFrom z.1.a z.2.2.seen x = some pt := by
  unfold OpenB.table at h
  obtain ⟨h1, h2⟩ := mem_zip4_all h
  obtain ⟨s0, h3, rfl⟩ := mem_zip3_map (leafSalt run) h1
  exact ⟨s0, h3, rfl, mapM_zip _ _ _ hps (x, pt) h2⟩

/-! ## The trees' tables -/

/-- **A row of tables of the trees' openings, from one opening.** -/
def TabsRow (W : Three.Whole) (sb : ℕ) (r : Proof.TailRead)
    (tabs : List (ℕ × List (ℕ × Row3))) : Prop :=
  ∀ j tab x c s pt, tabs.lookup j = some tab → tab.lookup x = some (c, s, pt) →
    ∃ z run s0, (j, z) ∈ ownRowsW W r ∧ (x, c, s0) ∈ listed z ∧
      runOfTree W r j = some run ∧ s0.size = sb ∧ s = leafSalt run s0 ∧
      pathFrom z.1.a z.2.2.seen x = some pt

theorem tabsWFull_row {W : Three.Whole} {sb : ℕ} {r : Proof.TailRead}
    {tabs : List (ℕ × List (ℕ × Row3))} (h : tabsWFull W sb r = some tabs) :
    TabsRow W sb r tabs := by
  unfold tabsWFull at h
  split at h
  · rename_i h0
    rw [Bool.and_eq_true] at h0
    obtain ⟨rows, hr, h1⟩ := Option.bind_eq_some_iff.1 h
    split at h1
    · obtain rfl := Option.some.inj h1
      intro j tab x c s pt hj hx
      have hm := mem_of_lookup _ _ _ hj
      unfold merged at hm
      obtain ⟨j', -, e⟩ := List.mem_map.1 hm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      obtain ⟨row, hrow, hin⟩ := List.mem_flatMap.1 (mem_of_lookup _ _ _ hx)
      obtain ⟨hrow1, hrow2⟩ := List.mem_filter.1 hrow
      obtain ⟨⟨j0, z⟩, hz, hf⟩ := mapM_back _ _ _ hr row hrow1
      unfold tableOfFull at hf
      obtain ⟨run, hrun, hf'⟩ := Option.bind_eq_some_iff.1 hf
      obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.1 hf'
      obtain rfl : j0 = j' := by simpa using hrow2
      obtain ⟨t, -, -, hok⟩ := rowOK_spec (List.all_eq_true.1 h0.2 _ hz)
      obtain ⟨s0, b1, b2, b3⟩ := table_row_all z run ps hps x c s pt hin
      exact ⟨z, run, s0, hz, b1, hrun,
        (_root_.Run.TieTree.ok_spec (asOpenB z) sb t.shape.W hok).2.2.1 s0
          (List.of_mem_zip (List.of_mem_zip b1).2).2, b2, b3⟩
    · cases h1
  · cases h

/-- A listed place beside its column. -/
theorem listed_col {z : Opened} {x : ℕ} {c : List UInt64} {s0 : ByteArray}
    (h : (x, c, s0) ∈ listed z) : (x, c) ∈ z.2.1.zip z.2.2.cols := by
  unfold listed at h
  generalize z.2.1 = l₁ at h ⊢
  generalize z.2.2.cols = l₂ at h ⊢
  generalize z.2.2.salts = l₃ at h
  induction l₁ generalizing l₂ l₃ with
  | nil => simp at h
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp at h
    | cons b l₂ =>
      cases l₃ with
      | nil => simp at h
      | cons d l₃ =>
        rw [List.zip_cons_cons, List.zip_cons_cons] at h
        rw [List.zip_cons_cons]
        rcases List.mem_cons.1 h with e | h'
        · cases e
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih l₂ l₃ h')

theorem TabsRow.back {W : Three.Whole} {sb : ℕ} {r : Proof.TailRead}
    {tabs : List (ℕ × List (ℕ × Row3))} (h : TabsRow W sb r tabs) : TabsBack W sb r tabs :=
  fun j tab x c s pt hj hx => by
    obtain ⟨z, run, s0, hz, hl, hr, hs0, hs, hp⟩ := h j tab x c s pt hj hx
    exact ⟨z, run, s0, hz, listed_col hl, hr, hs0, hs, pathFrom_length hp⟩

theorem TabsRow.path {W : Three.Whole} {sb : ℕ} {r : Proof.TailRead}
    {tabs : List (ℕ × List (ℕ × Row3))} (h : TabsRow W sb r tabs) : TabsPath W r tabs :=
  fun j tab x c s pt hj hx => by
    obtain ⟨z, run, s0, hz, hl, -, -, -, hp⟩ := h j tab x c s pt hj hx
    exact ⟨z, hz, (List.of_mem_zip (listed_col hl)).1, hp⟩

/-! ## The stored table's -/

/-- **A row of a table of the stored table's openings, from one opening.** -/
def ExtRow (cfg : ByteArray) (W : Three.Whole) (r : Proof.TailRead) (tab : List (ℕ × Row3)) :
    Prop :=
  ∀ x c s pt, tab.lookup x = some (c, s, pt) →
    ∃ t z s0, (t, z) ∈ storedRowsW W r ∧ (x, c, s0) ∈ listed z ∧ s0.size = t.salt ∧
      s = leafSalt cfg s0 ∧ pathFrom z.1.a z.2.2.seen x = some pt

theorem extTabWFull_row {a : ℕ} {cfg : ByteArray} {W : Three.Whole} {r : Proof.TailRead}
    {tab : List (ℕ × Row3)} (h : extTabWFull a cfg W r = some tab) : ExtRow cfg W r tab := by
  unfold extTabWFull at h
  split at h
  · rename_i h0
    rw [Bool.and_eq_true] at h0
    obtain ⟨ts, hr, h1⟩ := Option.bind_eq_some_iff.1 h
    split at h1
    · obtain rfl := Option.some.inj h1
      intro x c s pt hx
      obtain ⟨tb, htb, hin⟩ := List.mem_flatten.1 (mem_of_lookup _ _ _ hx)
      obtain ⟨⟨t, z⟩, hz, hf⟩ := mapM_back _ _ _ hr tb htb
      obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.1 hf
      obtain ⟨-, -, -, hok⟩ := storedOK_spec (List.all_eq_true.1 h0.2 _ hz)
      obtain ⟨s0, b1, b2, b3⟩ := table_row_all z cfg ps hps x c s pt hin
      exact ⟨t, z, s0, hz, b1,
        (_root_.Run.TieTree.ok_spec (asOpenB z) t.salt t.sh.W hok).2.2.1 s0
          (List.of_mem_zip (List.of_mem_zip b1).2).2, b2, b3⟩
    · cases h1
  · cases h

theorem ExtRow.back {cfg : ByteArray} {W : Three.Whole} {r : Proof.TailRead}
    {tab : List (ℕ × Row3)} (h : ExtRow cfg W r tab) : ExtBack cfg W r tab :=
  fun x c s pt hx => by
    obtain ⟨t, z, s0, hz, hl, hs0, hs, hp⟩ := h x c s pt hx
    exact ⟨t, z, s0, hz, listed_col hl, hs0, hs, pathFrom_length hp⟩

theorem ExtRow.path {cfg : ByteArray} {W : Three.Whole} {r : Proof.TailRead}
    {tab : List (ℕ × Row3)} (h : ExtRow cfg W r tab) : ExtPath W r tab :=
  fun x c s pt hx => by
    obtain ⟨t, z, s0, hz, hl, -, -, hp⟩ := h x c s pt hx
    exact ⟨t, z, hz, (List.of_mem_zip (listed_col hl)).1, hp⟩

/-! ## The stored tables' salts -/

/-- A test on the data alone: every stored table of the three chains' rounds has salts of sb
bytes. -/
def saltsFit (sb : ℕ) (W : Three.Whole) : Bool :=
  (W.ds₁ ++ (W.ds₂ ++ W.ds₃)).all fun d => d.stored.all fun t => t.salt == sb

/-- Then so has each stored table that the file opens. -/
theorem saltsFit_spec {sb : ℕ} {W : Three.Whole} (h : saltsFit sb W = true) (r : Proof.TailRead) :
    ∀ t z, (t, z) ∈ storedRowsW W r → t.salt = sb := by
  intro t z hz
  have key : ∀ (ds : List Three.RDL) (o : Fmt.ChainOut), (t, z) ∈ storedRows ds o →
      ∃ d ∈ ds, t ∈ d.stored := fun ds o hm => by
    obtain ⟨u, hu, hq⟩ := List.mem_flatMap.1 hm
    exact ⟨u.1, (List.of_mem_zip hu).1, (List.of_mem_zip hq).1⟩
  have hd : ∃ d ∈ W.ds₁ ++ (W.ds₂ ++ W.ds₃), t ∈ d.stored := by
    rcases List.mem_append.1 hz with h1 | h1
    · obtain ⟨d, hd, ht⟩ := key _ _ h1
      exact ⟨d, List.mem_append_left _ hd, ht⟩
    · rcases List.mem_append.1 h1 with h2 | h2
      · obtain ⟨d, hd, ht⟩ := key _ _ h2
        exact ⟨d, List.mem_append_right _ (List.mem_append_left _ hd), ht⟩
      · obtain ⟨d, hd, ht⟩ := key _ _ h2
        exact ⟨d, List.mem_append_right _ (List.mem_append_right _ hd), ht⟩
  obtain ⟨d, hd, ht⟩ := hd
  exact beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 h d hd) t ht)

end OnBytes.Maker
