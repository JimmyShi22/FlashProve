-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TablesPath.lean: the paths in the tables of a whole file's openings with whole paths
(OnBytes/Maker/Tables.lean, `tabsWFull`, `extTabWFull`), entry by entry.

A reader's walk over a pruned set of paths leaves a record of the vertices that it has met: depth,
number in the level, digest. A whole path of a leaf is read out of that record
(Run/ParseFull.lean, `pathFrom`): at each level, from the leaves up, the record's vertex at the
sibling's number. This file says that of each row of the tables.

  `vertexOf a seen m n`   the record's digest at the level m above the leaves of a tree of depth a,
                          at the number n; the digest of zeros where the record has none.
  `pathFrom_eq`           a value of `pathFrom` is, level by level, `vertexOf` at the sibling's
                          number.
  `mapM_zip`, `mem_zip4_ends`
                          on lists.
  `TabsPath`, `tabsWFull_path`
                          a row that the look-ups find under the tree j at the place x: an opening
                          of the tree j in the file lists x, and the row's path is read out of that
                          opening's record at x.
  `ExtPath`, `extTabWFull_path`
                          the same for the stored table.
  `opensT_path`           the path of an opening that the typing lays at a position of a stretch.

Where a tree is opened twice, which of the openings that list x it is, is not said: two places of
one tree can have their paths out of two records. That two records of one tree hold one digest at
one vertex is not said here.

Not claimed. That a record's vertices are hashes of anything. Nothing on soundness.


-/
import OnBytes.Maker.OpensFit

set_option autoImplicit false

namespace OnBytes.Maker

open Iop Rom Compile
open _root_.Run (OpenB Row3 atT pathFrom seenAt bytesToDig)

/-- The record's digest at the level m above the leaves, at the number n. -/
def vertexOf (a : ℕ) (seen : List (ℕ × ℕ × ByteArray)) (m n : ℕ) : Dig 256 :=
  ((seenAt seen (a - m) n).map bytesToDig).getD default

/-! ## Lists -/

/-- The values of `List.mapM`, one by one. -/
theorem mapM_eq_map {α β : Type} (f : α → Option β) (d : β) : ∀ (l : List α) (bs : List β),
    l.mapM f = some bs → bs = l.map fun a => (f a).getD d
  | [], bs, h => by
    rw [List.mapM_nil] at h
    exact (Option.some.inj h).symm
  | a0 :: l, bs, h => by
    rw [List.mapM_cons] at h
    cases e0 : f a0 with
    | none => rw [e0] at h; cases h
    | some b0 =>
      cases e1 : l.mapM f with
      | none => rw [e0, e1] at h; cases h
      | some bs0 =>
        rw [e0, e1] at h
        have hbs : bs = b0 :: bs0 := (Option.some.inj h).symm
        rw [hbs, List.map_cons, e0, ← mapM_eq_map f d l bs0 e1]
        rfl

/-- A member beside its value. -/
theorem mapM_zip {α β : Type} (f : α → Option β) : ∀ (l : List α) (bs : List β),
    l.mapM f = some bs → ∀ p ∈ l.zip bs, f p.1 = some p.2
  | [], _, _, _, hp => by simp at hp
  | a0 :: l, bs, h, p, hp => by
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
        rw [List.zip_cons_cons] at hp
        rcases List.mem_cons.1 hp with e | hp'
        · subst e
          exact e0
        · exact mapM_zip f l bs0 e1 p hp'

/-- The first and the last of a member of four lists zipped. -/
theorem mem_zip4_ends {α β γ δ : Type} : ∀ {l₁ : List α} {l₂ : List β} {l₃ : List γ}
    {l₄ : List δ} {a : α} {b : β} {c : γ} {d : δ},
    (a, b, c, d) ∈ l₁.zip (l₂.zip (l₃.zip l₄)) → (a, d) ∈ l₁.zip l₄
  | [], _, _, _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, _, _, h => by simp at h
  | _ :: _, _ :: _, [], _, _, _, _, _, h => by simp at h
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, h => by simp at h
  | x :: l₁, y :: l₂, z :: l₃, w :: l₄, a, b, c, d, h => by
    rw [List.zip_cons_cons, List.zip_cons_cons, List.zip_cons_cons] at h
    rw [List.zip_cons_cons]
    rcases List.mem_cons.1 h with e | h'
    · cases e
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_zip4_ends h')

/-- **A whole path, level by level.** -/
theorem pathFrom_eq {a : ℕ} {seen : List (ℕ × ℕ × ByteArray)} {x : ℕ} {pt : List (Dig 256)}
    (h : pathFrom a seen x = some pt) :
    pt = (List.range a).map fun m => vertexOf a seen m ((x / 2 ^ m) ^^^ 1) :=
  mapM_eq_map _ default _ _ h

/-- The path of a row of one opening's table with whole paths. -/
theorem table_path (z : Opened) (run : ByteArray) (ps : List (List (Dig 256)))
    (hps : fullPaths z = some ps) (x : ℕ) (c : List UInt64) (s : Bits) (pt : List (Dig 256))
    (h : (x, c, s, pt) ∈ (asOpenB z).table run ps) : pathFrom z.1.a z.2.2.seen x = some pt := by
  unfold OpenB.table at h
  exact mapM_zip _ _ _ hps (x, pt) (mem_zip4_ends h)

/-! ## The tables -/

/-- **The paths in tables of the trees' openings.** -/
def TabsPath (W : Three.Whole) (r : Proof.TailRead) (tabs : List (ℕ × List (ℕ × Row3))) : Prop :=
  ∀ j tab x c s pt, tabs.lookup j = some tab → tab.lookup x = some (c, s, pt) →
    ∃ z, (j, z) ∈ ownRowsW W r ∧ x ∈ z.2.1 ∧ pathFrom z.1.a z.2.2.seen x = some pt

theorem tabsWFull_path {W : Three.Whole} {sb : ℕ} {r : Proof.TailRead}
    {tabs : List (ℕ × List (ℕ × Row3))} (h : tabsWFull W sb r = some tabs) :
    TabsPath W r tabs := by
  unfold tabsWFull at h
  split at h
  · obtain ⟨rows, hr, h1⟩ := Option.bind_eq_some_iff.1 h
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
      obtain ⟨run, -, hf'⟩ := Option.bind_eq_some_iff.1 hf
      obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.1 hf'
      obtain rfl : j0 = j' := by simpa using hrow2
      exact ⟨z, hz, (List.of_mem_zip (table_back (asOpenB z) run ps x c s pt hin).1).1,
        table_path z run ps hps x c s pt hin⟩
    · cases h1
  · cases h

/-- **The paths in a table of the stored table's openings.** -/
def ExtPath (W : Three.Whole) (r : Proof.TailRead) (tab : List (ℕ × Row3)) : Prop :=
  ∀ x c s pt, tab.lookup x = some (c, s, pt) →
    ∃ t z, (t, z) ∈ storedRowsW W r ∧ x ∈ z.2.1 ∧ pathFrom z.1.a z.2.2.seen x = some pt

theorem extTabWFull_path {a : ℕ} {cfg : ByteArray} {W : Three.Whole} {r : Proof.TailRead}
    {tab : List (ℕ × Row3)} (h : extTabWFull a cfg W r = some tab) : ExtPath W r tab := by
  unfold extTabWFull at h
  split at h
  · obtain ⟨ts, hr, h1⟩ := Option.bind_eq_some_iff.1 h
    split at h1
    · obtain rfl := Option.some.inj h1
      intro x c s pt hx
      obtain ⟨tb, htb, hin⟩ := List.mem_flatten.1 (mem_of_lookup _ _ _ hx)
      obtain ⟨⟨t, z⟩, hz, hf⟩ := mapM_back _ _ _ hr tb htb
      obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.1 hf
      exact ⟨t, z, hz, (List.of_mem_zip (table_back (asOpenB z) cfg ps x c s pt hin).1).1,
        table_path z cfg ps hps x c s pt hin⟩
    · cases h1
  · cases h

/-! ## At a position -/

/-- **The path of an opening that the typing lays at a position of a stretch**: read, level by
level, out of the record of an opening of the position's tree that lists the position's leaf. -/
theorem opensT_path {W : Three.Whole} {r : Proof.TailRead} {tabs : List (ℕ × List (ℕ × Row3))}
    (hp : TabsPath W r tabs) (C : _root_.Run.PQ.CK) (ds : List RDT) (base : ℕ)
    (q : OPos (uLT C ds)) (op : Opening 256 (OSym (uLT C ds) q))
    (h : opensT C ds base tabs q = some op) :
    ∃ z, (base + treeAt C ds q, z) ∈ ownRowsW W r ∧ leafAt C ds q ∈ z.2.1 ∧
      op.path = (List.range z.1.a).map fun m =>
        vertexOf z.1.a z.2.2.seen m ((leafAt C ds q / 2 ^ m) ^^^ 1) := by
  obtain ⟨tab, c, ht, hl, -⟩ := opensT_some C ds base tabs q op h
  obtain ⟨z, hz, hx, hpt⟩ := hp _ _ _ _ _ _ ht hl
  exact ⟨z, hz, hx, pathFrom_eq hpt⟩

end OnBytes.Maker
