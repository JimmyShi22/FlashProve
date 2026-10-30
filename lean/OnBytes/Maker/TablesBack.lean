-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TablesBack.lean: the tables of a whole file's openings with whole paths
(OnBytes/Maker/Tables.lean, `tabsWFull`, `extTabWFull`) hold nothing but what the file's openings
list.

OnBytes/Maker/TablesLaws.lean goes from an opening of the file to a row of the tables. This file
goes back, and says of each row what its salt and its path are made of.

  `mapM_back`         each value of `List.mapM` is the value at a member of the list.
  `pathFrom_length`   a whole path has one digest for each level of its tree.
  `table_back`        a row of one opening's table: its place is listed, its salt is the typed salt
                      of one of the opening's salts, its path is one of the paths given.
  `TabsBack`, `tabsWFull_back`
                      a row that the look-ups find under the tree j at the place x: an opening of
                      the tree j in the file lists x; the salt is the sender's run's value and then
                      a salt of as many bytes as the plan says; the path is as long as the tree is
                      deep.
  `ExtBack`, `extTabWFull_back`
                      the same for the stored table.
  `length_leafSalt`   the number of bits of a typed salt.

Not claimed. That the tables return a value. Nothing on hashes; nothing on soundness.
Of a row of a whole file's tables (`TabsBack`, `ExtBack`) the place and the column alone are tied to
what an opening lists. Of its salt only this: it is the typed salt of SOME string of as many bytes
as the plan says; not that the string is one of that opening's salts, nor the one at the row's
place. Of its path only its length.


-/
import OnBytes.Maker.TablesLaws
import Run.CodingBitsLaws

set_option autoImplicit false

namespace OnBytes.Maker

open Iop Rom Compile
open _root_.Run (OpenB Row3 atT pathFrom leafSalt bytesToBits)

/-! ## Lists -/

/-- Each value of `List.mapM` is the value at a member of the list. -/
theorem mapM_back {α β : Type} (f : α → Option β) : ∀ (l : List α) (bs : List β),
    l.mapM f = some bs → ∀ b ∈ bs, ∃ a ∈ l, f a = some b
  | [], bs, h, b, hb => by
    rw [List.mapM_nil] at h
    obtain rfl := Option.some.inj h
    cases hb
  | a0 :: l, bs, h, b, hb => by
    rw [List.mapM_cons] at h
    cases e0 : f a0 with
    | none => rw [e0] at h; cases h
    | some b0 =>
      cases e1 : l.mapM f with
      | none => rw [e0, e1] at h; cases h
      | some bs0 =>
        rw [e0, e1] at h
        have hbs : bs = b0 :: bs0 := (Option.some.inj h).symm
        subst hbs
        rcases List.mem_cons.1 hb with e | hb'
        · subst e
          exact ⟨a0, List.mem_cons_self, e0⟩
        · obtain ⟨a, ha, hf⟩ := mapM_back f l bs0 e1 b hb'
          exact ⟨a, List.mem_cons_of_mem _ ha, hf⟩

/-- A whole path has one digest for each level of its tree. -/
theorem pathFrom_length {a : ℕ} {seen : List (ℕ × ℕ × ByteArray)} {x : ℕ} {pt : List (Dig 256)}
    (h : pathFrom a seen x = some pt) : pt.length = a := by
  unfold pathFrom at h
  rw [mapM_length _ _ _ h, List.length_range]

/-- A member of four lists zipped is a member of each. -/
theorem mem_zip4 {α β γ δ : Type} {l₁ : List α} {l₂ : List β} {l₃ : List γ} {l₄ : List δ}
    {a : α} {b : β} {c : γ} {d : δ} (h : (a, b, c, d) ∈ l₁.zip (l₂.zip (l₃.zip l₄))) :
    (a, b) ∈ l₁.zip l₂ ∧ c ∈ l₃ ∧ d ∈ l₄ := by
  have h2 := (List.of_mem_zip h).2
  have h3 := (List.of_mem_zip h2).2
  refine ⟨?_, (List.of_mem_zip h3).1, (List.of_mem_zip h3).2⟩
  induction l₁ generalizing l₂ l₃ l₄ with
  | nil => simp at h
  | cons x l₁ ih =>
    cases l₂ with
    | nil => simp at h
    | cons y l₂ =>
      cases l₃ with
      | nil => simp at h
      | cons z l₃ =>
        cases l₄ with
        | nil => simp at h
        | cons w l₄ =>
          rw [List.zip_cons_cons, List.zip_cons_cons, List.zip_cons_cons] at h
          rw [List.zip_cons_cons]
          rcases List.mem_cons.1 h with e | h'
          · cases e
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _
              (ih h' (List.of_mem_zip h').2 (List.of_mem_zip (List.of_mem_zip h').2).2)

/-- A row of one opening's table. -/
theorem table_back (O : OpenB) (run : ByteArray) (paths : List (List (Dig 256))) (x : ℕ)
    (c : List UInt64) (s : Bits) (pt : List (Dig 256)) (h : (x, c, s, pt) ∈ O.table run paths) :
    (x, c) ∈ O.idx.zip O.cols ∧ (∃ s0 ∈ O.salts, s = leafSalt run s0) ∧ pt ∈ paths := by
  unfold OpenB.table at h
  obtain ⟨h1, h2, h3⟩ := mem_zip4 h
  obtain ⟨s0, hs0, rfl⟩ := List.mem_map.1 h2
  exact ⟨h1, ⟨s0, hs0, rfl⟩, h3⟩

/-! ## The trees' tables -/

/-- **What tables of the trees' openings hold at most.** -/
def TabsBack (W : Three.Whole) (sb : ℕ) (r : Proof.TailRead)
    (tabs : List (ℕ × List (ℕ × Row3))) : Prop :=
  ∀ j tab x c s pt, tabs.lookup j = some tab → tab.lookup x = some (c, s, pt) →
    ∃ z run s0, (j, z) ∈ ownRowsW W r ∧ (x, c) ∈ z.2.1.zip z.2.2.cols ∧
      runOfTree W r j = some run ∧ s0.size = sb ∧ s = leafSalt run s0 ∧ pt.length = z.1.a

theorem tabsWFull_back {W : Three.Whole} {sb : ℕ} {r : Proof.TailRead}
    {tabs : List (ℕ × List (ℕ × Row3))} (h : tabsWFull W sb r = some tabs) :
    TabsBack W sb r tabs := by
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
      obtain ⟨b1, ⟨s0, hs0, rfl⟩, b3⟩ := table_back (asOpenB z) run ps x c s pt hin
      obtain ⟨x', -, hx'⟩ := mapM_back _ _ _ hps pt b3
      exact ⟨z, run, s0, hz, b1, hrun,
        (_root_.Run.TieTree.ok_spec (asOpenB z) sb t.shape.W hok).2.2.1 s0 hs0, rfl,
        pathFrom_length hx'⟩
    · cases h1
  · cases h

/-! ## The stored table's -/

/-- **What a table of the stored table's openings holds at most.** -/
def ExtBack (cfg : ByteArray) (W : Three.Whole) (r : Proof.TailRead) (tab : List (ℕ × Row3)) :
    Prop :=
  ∀ x c s pt, tab.lookup x = some (c, s, pt) →
    ∃ t z s0, (t, z) ∈ storedRowsW W r ∧ (x, c) ∈ z.2.1.zip z.2.2.cols ∧ s0.size = t.salt ∧
      s = leafSalt cfg s0 ∧ pt.length = z.1.a

theorem extTabWFull_back {a : ℕ} {cfg : ByteArray} {W : Three.Whole} {r : Proof.TailRead}
    {tab : List (ℕ × Row3)} (h : extTabWFull a cfg W r = some tab) : ExtBack cfg W r tab := by
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
      obtain ⟨b1, ⟨s0, hs0, rfl⟩, b3⟩ := table_back (asOpenB z) cfg ps x c s pt hin
      obtain ⟨x', -, hx'⟩ := mapM_back _ _ _ hps pt b3
      exact ⟨t, z, s0, hz, b1,
        (_root_.Run.TieTree.ok_spec (asOpenB z) t.salt t.sh.W hok).2.2.1 s0 hs0, rfl,
        pathFrom_length hx'⟩
    · cases h1
  · cases h

/-- The typed salt's length. -/
theorem length_leafSalt (run s : ByteArray) :
    (leafSalt run s).length = 8 * run.size + 8 * s.size := by
  unfold leafSalt
  rw [List.length_append, _root_.Run.length_bytesToBits, _root_.Run.length_bytesToBits]

end OnBytes.Maker
