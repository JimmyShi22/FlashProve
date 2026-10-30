-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/LeafInputs.lean: two different pairs of a column and a salt, of one number of
words and one number of bytes, give two different strings of bytes to the leaf's hash call; so in a
file that shows a collision of the leaf hash (`CollidesIn`,
OnBytes/Maker/Page/TwiceOrCollide.lean) two entries out of the file's own lists give two different
strings of bytes with one answer of the hash, at one number, one label, one index and one start.

Statements and proofs, with the hash as a letter h. What is hashed for a leaf is the column's words,
8 bytes each, a fill of zero bytes whose length is a function of the column's and the salt's
lengths, and the salt (`Fmt.leafBytes`, Fmt/Rules7.lean). The call's number, label, index and start
hold the shape, the two lengths, the position and the start.

Main names:
  `colBytes_inj`, `leafBytes_inj`: one to one at fixed lengths.
  `listed_sizes`: an entry that an opening lists has the width and the bytes of a salt at which the
    library's test on openings passed.
  `SizesOne W r`: any two listed entries under one tree's number, and any two of the stored
    table's, have one number of words and one number of bytes. `sizesOne_of`: from the tables' own
    tests `rowOK` and `storedOK`, one shape as
    read and one number of bytes of a salt among the stored tables.
  `CollidesInB h W r cfg`: `CollidesIn` with the hash's own arguments written out: the two entries'
    strings of bytes differ, and h has one answer at both.
  `CollidesIn.bytes`: `CollidesIn h W r cfg → SizesOne W r → CollidesInB h W r cfg`.
Under "there is" in `CollidesInB`: the two openings and the two entries, each a member of the file's
own lists; the start, fixed by `runOfTree W r x.1 = some start`.
Limits: `SizesOne` is a premise of the last law. In `CollidesInB` both calls stand under one label,
that of the first opening's shape and the first entry's lengths: that the second call is what the
reader itself hashes for the second entry is no clause of it. Nothing on how hard a collision is to
find. Nothing on opening-form binding, no two openings of a commitment, correctness of extraction,
what a root fixes or whatever else names a committer or a prover. Nothing on soundness.

-/
import OnBytes.Maker.Page.TwiceOrCollide
import Fmt.Rules23In
import Run.OpenDomProofs

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Maker
open OnBytes.Proof (TailRead)

/-- A column's bytes, at a fixed number of words, are one to one. -/
theorem colBytes_inj : ∀ c c' : List UInt64, c.length = c'.length →
    Fmt.colBytes c = Fmt.colBytes c' → c = c'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | x :: c, y :: c', h, e => by
    unfold Fmt.colBytes at e
    rw [List.map_cons, List.map_cons, Fmt.cat_cons, Fmt.cat_cons] at e
    obtain ⟨e1, e2⟩ := Fmt.append_cancel _ _ _ _ (by rw [Fmt.size_u64, Fmt.size_u64]) e
    have hx : x = y := by
      have := congrArg (fun b => Fmt.wordAt b 0) e1
      simpa [Fmt.wordAt_u64] using this
    rw [hx, colBytes_inj c c' (Nat.succ.inj h) e2]

/-- **What is hashed for a leaf, at fixed lengths, is one to one.** -/
theorem leafBytes_inj (c c' : List UInt64) (s s' : ByteArray) (hl : c.length = c'.length)
    (hs : s.size = s'.size) (e : Fmt.leafBytes c s = Fmt.leafBytes c' s') : c = c' ∧ s = s' := by
  unfold Fmt.leafBytes at e
  rw [hl, hs] at e
  obtain ⟨e1, e2⟩ := Fmt.append_cancel _ _ _ _ (by
    rw [ByteArray.size_append, ByteArray.size_append, size_colBytes, size_colBytes, hl]) e
  obtain ⟨e3, -⟩ := Fmt.append_cancel _ _ _ _ (by rw [size_colBytes, size_colBytes, hl]) e1
  exact ⟨colBytes_inj c c' hl e3, e2⟩

/-- An entry that an opening lists has the width and the bytes of a salt at which the library's test
on openings passed. -/
theorem listed_sizes {x : Opened} {sb w : ℕ} (hok : (asOpenB x).ok sb w = true)
    {u : ℕ × List UInt64 × ByteArray} (hu : u ∈ listed x) : u.2.1.length = w ∧ u.2.2.size = sb := by
  unfold OpenB.ok at hok
  simp only [Bool.and_eq_true] at hok
  have hz := (List.of_mem_zip hu).2
  have h1 : u.2.1 ∈ x.2.2.cols := (List.of_mem_zip hz).1
  have h2 : u.2.2 ∈ x.2.2.salts := (List.of_mem_zip hz).2
  exact ⟨eq_of_beq (List.all_eq_true.1 hok.1.1.1.2 _ h1),
    eq_of_beq (List.all_eq_true.1 hok.1.1.2 _ h2)⟩

/-- Any two listed entries under one tree's number, and any two of the stored table's, have one
number of words and one number of bytes. -/
def SizesOne (W : Three.Whole) (r : TailRead) : Prop :=
  (∀ x ∈ ownRowsW W r, ∀ y ∈ ownRowsW W r, x.1 = y.1 → ∀ u ∈ listed x.2, ∀ v ∈ listed y.2,
    u.2.1.length = v.2.1.length ∧ u.2.2.size = v.2.2.size) ∧
  ∀ x ∈ storedRowsW W r, ∀ y ∈ storedRowsW W r, ∀ u ∈ listed x.2, ∀ v ∈ listed y.2,
    u.2.1.length = v.2.1.length ∧ u.2.2.size = v.2.2.size

/-- From the tables' own tests. hz: the stored tables that are opened have one number of bytes of a
salt. -/
theorem sizesOne_of {W : Three.Whole} {r : TailRead} {sb a : ℕ}
    (h₁ : ∀ x ∈ ownRowsW W r, rowOK W sb x = true)
    (h₂ : ∀ y ∈ storedRowsW W r, storedOK a y = true) (sE : ShapeOneE W r)
    (hz : ∀ x ∈ storedRowsW W r, ∀ y ∈ storedRowsW W r, x.1.salt = y.1.salt) : SizesOne W r := by
  have own : ∀ x ∈ ownRowsW W r, ∀ t, W.table[x.1]? = some t →
      (asOpenB x.2).ok sb t.shape.W = true := by
    intro x hx t ht
    have := h₁ x hx
    unfold rowOK at this
    rw [ht] at this
    exact (Bool.and_eq_true_iff.1 this).2
  have st : ∀ y ∈ storedRowsW W r, y.2.1 = y.1.sh ∧ (asOpenB y.2).ok y.1.salt y.1.sh.W = true := by
    intro y hy
    have := h₂ y hy
    unfold storedOK at this
    simp only [Bool.and_eq_true] at this
    exact ⟨eq_of_beq this.1.1.1, this.2⟩
  refine ⟨fun x hx y hy e u hu v hv => ?_, fun x hx y hy u hu v hv => ?_⟩
  · have hx' := h₁ x hx
    unfold rowOK at hx'
    cases ht : W.table[x.1]? with
    | none => rw [ht] at hx'; cases hx'
    | some t =>
      obtain ⟨a1, a2⟩ := listed_sizes (own x hx t ht) hu
      obtain ⟨b1, b2⟩ := listed_sizes (own y hy t (e ▸ ht)) hv
      exact ⟨a1.trans b1.symm, a2.trans b2.symm⟩
  · obtain ⟨p1, p2⟩ := st x hx
    obtain ⟨q1, q2⟩ := st y hy
    obtain ⟨a1, a2⟩ := listed_sizes p2 hu
    obtain ⟨b1, b2⟩ := listed_sizes q2 hv
    have es : x.1.sh = y.1.sh := p1.symm.trans ((sE x hx y hy).trans q1)
    exact ⟨a1.trans ((congrArg (·.W) es).trans b1.symm), a2.trans ((hz x hx y hy).trans b2.symm)⟩

/-- **The file shows a collision of the hash**: two entries out of its own lists give two different
strings of bytes with one answer, at one number, label, index and start. -/
def CollidesInB (h : HId) (W : Three.Whole) (r : TailRead) (cfg : ByteArray) : Prop :=
  (∃ x ∈ ownRowsW W r, ∃ y ∈ ownRowsW W r, ∃ u ∈ listed x.2, ∃ v ∈ listed y.2, ∃ start,
    x.1 = y.1 ∧ u.1 = v.1 ∧ runOfTree W r x.1 = some start ∧
      Fmt.leafBytes u.2.1 u.2.2 ≠ Fmt.leafBytes v.2.1 v.2.2 ∧
      h (Fmt.leafNo x.2.1.stored) (Fmt.leafPlace x.2.1.tree u.2.1.length (u.2.2.size / 8))
          (2 ^ x.2.1.a + u.1) start (Fmt.leafBytes u.2.1 u.2.2) =
        h (Fmt.leafNo x.2.1.stored) (Fmt.leafPlace x.2.1.tree u.2.1.length (u.2.2.size / 8))
          (2 ^ x.2.1.a + u.1) start (Fmt.leafBytes v.2.1 v.2.2)) ∨
  ∃ x ∈ storedRowsW W r, ∃ y ∈ storedRowsW W r, ∃ u ∈ listed x.2, ∃ v ∈ listed y.2,
    u.1 = v.1 ∧ Fmt.leafBytes u.2.1 u.2.2 ≠ Fmt.leafBytes v.2.1 v.2.2 ∧
      h (Fmt.leafNo x.2.1.stored) (Fmt.leafPlace x.2.1.tree u.2.1.length (u.2.2.size / 8))
          (2 ^ x.2.1.a + u.1) cfg (Fmt.leafBytes u.2.1 u.2.2) =
        h (Fmt.leafNo x.2.1.stored) (Fmt.leafPlace x.2.1.tree u.2.1.length (u.2.2.size / 8))
          (2 ^ x.2.1.a + u.1) cfg (Fmt.leafBytes v.2.1 v.2.2)

/-- **From pairs of a column and a salt to the hash's own arguments, at the same members of the
file's lists.** -/
theorem CollidesIn.bytes {h : HId} {W : Three.Whole} {r : TailRead} {cfg : ByteArray}
    (c : CollidesIn h W r cfg) (z : SizesOne W r) : CollidesInB h W r cfg := by
  rcases c with ⟨x, hx, y, hy, u, hu, v, hv, s, e, ep, hne, hr, eq⟩ |
    ⟨x, hx, y, hy, u, hu, v, hv, ep, hne, eq⟩
  · obtain ⟨l1, l2⟩ := z.1 x hx y hy e u hu v hv
    unfold leafHash at eq
    rw [← l1, ← l2] at eq
    exact Or.inl ⟨x, hx, y, hy, u, hu, v, hv, s, e, ep, hr, fun eb =>
      hne (Prod.ext (leafBytes_inj _ _ _ _ l1 l2 eb).1 (leafBytes_inj _ _ _ _ l1 l2 eb).2), eq⟩
  · obtain ⟨l1, l2⟩ := z.2 x hx y hy u hu v hv
    unfold leafHash at eq
    rw [← l1, ← l2] at eq
    exact Or.inr ⟨x, hx, y, hy, u, hu, v, hv, ep, fun eb =>
      hne (Prod.ext (leafBytes_inj _ _ _ _ l1 l2 eb).1 (leafBytes_inj _ _ _ _ l1 l2 eb).2), eq⟩

end OnBytes.Maker.Page
