-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/TwiceOrCollide.lean: in a file as read, two listed entries at one position of one
tree, or of the stored table, have one leaf hash; so either they hold one column and one salt
throughout (`SameTwice`, OnBytes/Maker/Tables.lean), or the file shows two different pairs of a
column and a salt with one leaf hash at one shape, one start and one position.

Statements and proofs, with the hash as a letter h. The two records of
OnBytes/Maker/Page/OwesH.lean say: two openings of one tree give one value to each vertex, and at
each listed position the bottom level holds the format's leaf hash of the column and the salt as
read. Laid together at a position that is listed twice, they give one hash of two entries.

Main names:
  `walked_pos`: the listed positions of an opening that was read lie below 2 ^ depth.
  `ShapeOne W r`, `ShapeOneE W r`: two openings under one number, and two openings of stored tables,
    have one shape as read. `shapeOne_of_rowOK`: the first from the tables' own test `rowOK`.
  `own_one_leaf`, `stored_one_leaf`: one leaf hash.
  `CollidesIn h W r cfg`: the file shows a collision: two members of `ownRowsW` under one number (or
    of `storedRowsW`), an entry that each lists, at one position, with different columns or salts
    and one leaf hash, at the start `runOfTree W r j` (or cfg).
  `sameTwice_or_collidesIn`: one of the two.
Under "there is" in `CollidesIn`: the two openings and the two entries, each a member of the file's
own lists; the start, fixed by `runOfTree W r x.1 = some start`.
Why the collision is stated of the file's own members: that SOME two inputs of a hash with answers
of 32 bytes have one answer is true of every such hash, by counting, and says nothing of a file.
Limits: `CollidesIn` speaks of pairs of a column and a salt, not of the hash's five arguments: that
the two pairs give two different strings of bytes under one label is the matter of
OnBytes/Maker/Page/LeafInputs.lean. The
two records and the two conditions on shapes are premises. Which of the two cases holds is decided
by no program here (the proof is by cases on a proposition). Nothing on how hard a collision is to
find. Nothing on opening-form binding, no two openings of a commitment, correctness of extraction,
what a root fixes or whatever else names a committer or a prover. Nothing on soundness.

-/
import OnBytes.Maker.Page.OwesH

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ _root_.Run.WalkTie OnBytes.Maker
open OnBytes.Proof (TailRead)

/-- The listed positions of an opening that was read lie below 2 ^ depth. -/
theorem walked_pos (h : HId) (cfg : ByteArray) {y : OpenedY} (W : Walked h cfg y) :
    ∀ p ∈ y.2.1, p < 2 ^ y.1.a := by
  obtain ⟨f, salt, start, b, i, e⟩ := W
  obtain ⟨hl, -⟩ := reader_seen h cfg f salt y.1 start y.2.1 b i y.2.2 e
  exact (listOK_spec y.1.a y.2.1 hl).2.2

/-- The condition under which two openings' values at a vertex are compared, at a listed leaf. -/
theorem leaf_place (h : HId) (cfg : ByteArray) {y : OpenedY} (W : Walked h cfg y) {p : ℕ}
    (hp : p ∈ y.2.1) : y.1.a ≠ 0 ∨ p = 0 := by
  by_cases h0 : y.1.a = 0
  · right
    have := walked_pos h cfg W p hp
    rw [h0] at this
    omega
  · exact Or.inl h0

/-- Two openings under one number have one shape as read. -/
def ShapeOne (W : Three.Whole) (r : TailRead) : Prop :=
  ∀ x ∈ ownRowsW W r, ∀ y ∈ ownRowsW W r, x.1 = y.1 → x.2.1 = y.2.1

/-- Two openings of stored tables have one shape as read. -/
def ShapeOneE (W : Three.Whole) (r : TailRead) : Prop :=
  ∀ x ∈ storedRowsW W r, ∀ y ∈ storedRowsW W r, x.2.1 = y.2.1

/-- The tables' own test on a tree's opening gives the first. -/
theorem shapeOne_of_rowOK {W : Three.Whole} {r : TailRead} {sb : ℕ}
    (h : ∀ x ∈ ownRowsW W r, rowOK W sb x = true) : ShapeOne W r := by
  have key : ∀ x ∈ ownRowsW W r, ∀ t, W.table[x.1]? = some t → x.2.1 = t.shape := by
    intro x hx t ht
    have := h x hx
    unfold rowOK at this
    rw [ht] at this
    exact eq_of_beq (Bool.and_eq_true_iff.1 this).1
  intro x hx y hy e
  have hx' := h x hx
  unfold rowOK at hx'
  cases ht : W.table[x.1]? with
  | none => rw [ht] at hx'; cases hx'
  | some t => rw [key x hx t ht, key y hy t (e ▸ ht)]

section
variable {h : HId} {W : Three.Whole} {r : TailRead} {cfg st : ByteArray}

/-- **Two listed entries at one position of one tree have one leaf hash.** -/
theorem own_one_leaf (A : TreesOwedH h W r cfg) (hs : ShapeOne W r) :
    ∀ x ∈ ownRowsW W r, ∀ y ∈ ownRowsW W r, x.1 = y.1 → ∀ u ∈ listed x.2, ∀ v ∈ listed y.2,
      u.1 = v.1 → ∃ start, runOfTree W r x.1 = some start ∧
        leafHash h x.2.1 start u.1 u.2.1 u.2.2 = leafHash h x.2.1 start u.1 v.2.1 v.2.2 := by
  intro x hx y hy e u hu v hv ep
  obtain ⟨s, hs1, Lx⟩ := A.leaf x hx
  obtain ⟨s', hs2, Ly⟩ := A.leaf y hy
  rw [← e, hs1] at hs2
  obtain rfl := Option.some.inj hs2
  have a1 := Lx u.1 u.2.1 u.2.2 hu
  have a2 := Ly v.1 v.2.1 v.2.2 hv
  rw [← hs x hx y hy e, ← ep] at a2
  exact ⟨s, hs1, A.one x hx y hy e _ _ _ _
    (leaf_place h cfg (A.walked x hx) (List.of_mem_zip hu).1) a1 a2⟩

/-- **Two listed entries at one position of the stored table have one leaf hash.** -/
theorem stored_one_leaf (B : StoredOwedH h W r cfg st) (hs : ShapeOneE W r) :
    ∀ x ∈ storedRowsW W r, ∀ y ∈ storedRowsW W r, ∀ u ∈ listed x.2, ∀ v ∈ listed y.2, u.1 = v.1 →
      leafHash h x.2.1 cfg u.1 u.2.1 u.2.2 = leafHash h x.2.1 cfg u.1 v.2.1 v.2.2 := by
  intro x hx y hy u hu v hv ep
  have a1 := B.leaf x hx u.1 u.2.1 u.2.2 hu
  have a2 := B.leaf y hy v.1 v.2.1 v.2.2 hv
  rw [← hs x hx y hy, ← ep] at a2
  exact B.one x hx y hy _ _ _ _ (leaf_place h cfg (B.walked x hx) (List.of_mem_zip hu).1) a1 a2

end

/-- **The file shows a collision of the leaf hash.** -/
def CollidesIn (h : HId) (W : Three.Whole) (r : TailRead) (cfg : ByteArray) : Prop :=
  (∃ x ∈ ownRowsW W r, ∃ y ∈ ownRowsW W r, ∃ u ∈ listed x.2, ∃ v ∈ listed y.2, ∃ start,
    x.1 = y.1 ∧ u.1 = v.1 ∧ u.2 ≠ v.2 ∧ runOfTree W r x.1 = some start ∧
      leafHash h x.2.1 start u.1 u.2.1 u.2.2 = leafHash h x.2.1 start u.1 v.2.1 v.2.2) ∨
  ∃ x ∈ storedRowsW W r, ∃ y ∈ storedRowsW W r, ∃ u ∈ listed x.2, ∃ v ∈ listed y.2,
    u.1 = v.1 ∧ u.2 ≠ v.2 ∧
      leafHash h x.2.1 cfg u.1 u.2.1 u.2.2 = leafHash h x.2.1 cfg u.1 v.2.1 v.2.2

/-- **Either every position that is listed twice holds one column and one salt, or the file shows a
collision of the leaf hash.** -/
theorem sameTwice_or_collidesIn {h : HId} {W : Three.Whole} {r : TailRead} {cfg st : ByteArray}
    (A : TreesOwedH h W r cfg) (B : StoredOwedH h W r cfg st) (s₁ : ShapeOne W r)
    (s₂ : ShapeOneE W r) : SameTwice W r ∨ CollidesIn h W r cfg := by
  by_cases hc : CollidesIn h W r cfg
  · exact Or.inr hc
  · refine Or.inl ⟨fun x hx y hy e u hu v hv ep => ?_, fun x hx y hy u hu v hv ep => ?_⟩
    · by_contra hne
      obtain ⟨s, h1, h2⟩ := own_one_leaf A s₁ x hx y hy e u hu v hv ep
      exact hc (Or.inl ⟨x, hx, y, hy, u, hu, v, hv, s, e, ep, hne, h1, h2⟩)
    · by_contra hne
      exact hc (Or.inr ⟨x, hx, y, hy, u, hu, v, hv, ep, hne,
        stored_one_leaf B s₂ x hx y hy u hu v hv ep⟩)

end OnBytes.Maker.Page
