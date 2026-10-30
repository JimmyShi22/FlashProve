-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/RecNodes.lean: the table of vertices of a tree of a whole file (`vertexOf` at `recOf`,
OnBytes/Maker/WalksAt.lean) is consistent on the ways up from the listed leaves, and has the root at
its top.

OnBytes/Maker/ReadNodes.lean says of the record of one opening that the reader has handed out: where
both children of a vertex are in it, the vertex is in it with the hash of the two; the opened leaves
stand at the bottom; the root at the top. From that:

  `walked_leaf`, `walked_lt`
                   a listed leaf is in its opening's record, at the bottom level, and is a leaf of
                   the tree.
  `walked_sib`     so is, at each level, the sibling on the way up from a listed leaf.
  `two_children`   a number and its sibling are the two children of one parent.
  `walked_up`, `walked_step`
                   on the way up from a listed leaf each vertex is in the record; below the top the
                   two children of the next vertex are in it, and that vertex with their hash.
  `rec_meets`      **consistency of the table**: at a vertex on the way up from a leaf that an
                   opening of the tree j lists, the table's entry at the parent is g's node hash of
                   the entries at the parent's two children.
  `rec_root`       **the top**: the table's entry at the top is the digest of the root to which the
                   reader's walk in an opening of the tree led.

The premises. Each opening of the tree is what the reader of an opening has handed out (`Walked`,
OnBytes/Maker/ReadWalks.lean: a law of a chain that was read). Two openings of the tree hold one
value at each vertex (`OneTable`, OnBytes/Maker/WalksAt.lean). `NodeIs g h cfg`: g's node hash of
the digests of two strings of 32 bytes is the digest of the format's vertex hash of the two: a
matter of how typed queries are spelled as hash calls; it is shown nowhere here. Each value in the
row has 32 bytes (`h32`): shown nowhere here.

Not claimed. Nothing on soundness (index binding included), what a root fixes, opening-form binding,
no two openings of a commitment, correctness of extraction or whatever else names a committer or a prover.

-/
import OnBytes.Maker.WalksAt

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop (Dig)
open _root_.Run _root_.Run.WalkTie Octopus

section One
variable (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (cfg : ByteArray)

/-- A listed leaf is in its opening's record, at the bottom level. -/
theorem walked_leaf {y : OpenedY} (W : Walked h cfg y) (x : ℕ) (hx : x ∈ y.2.1) :
    ∃ v, seenAt y.2.2.seen y.1.a x = some v := by
  obtain ⟨f, salt, start, b, i, e⟩ := W
  obtain ⟨-, r1, r2, -, -, -⟩ := reader_seen h cfg f salt y.1 start y.2.1 b i y.2.2 e
  have hlen : (leafV h y.1 start y.2.1 (y.2.2.cols.zip y.2.2.salts)).length = y.2.1.length :=
    length_leafV h y.1 start y.2.1 _ (by rw [List.length_zip, r1, r2, Nat.min_self])
  obtain ⟨v, hv⟩ := mem_zip_left y.2.1 _ hlen.symm x hx
  exact ⟨v, (opening_nodes h cfg f salt y.1 start y.2.1 b i y.2.2 e).2.1 (x, v) hv⟩

/-- A listed leaf is a leaf of the tree. -/
theorem walked_lt {y : OpenedY} (W : Walked h cfg y) (x : ℕ) (hx : x ∈ y.2.1) : x < 2 ^ y.1.a := by
  obtain ⟨f, salt, start, b, i, e⟩ := W
  obtain ⟨hl, -, -, -, -, -⟩ := reader_seen h cfg f salt y.1 start y.2.1 b i y.2.2 e
  exact (listOK_spec y.1.a y.2.1 hl).2.2 x hx

/-- At each level the sibling on the way up from a listed leaf is in the record. -/
theorem walked_sib {y : OpenedY} (W : Walked h cfg y) (x : ℕ) (hx : x ∈ y.2.1) (m : ℕ)
    (hm : m < y.1.a) : ∃ v, seenAt y.2.2.seen (y.1.a - m) ((x / 2 ^ m) ^^^ 1) = some v := by
  obtain ⟨p, hp, -⟩ := walked_paths h cfg W x hx
  unfold pathFrom at hp
  obtain ⟨b, -, hb⟩ := mapM_mem _ _ _ hp m (List.mem_range.2 hm)
  obtain ⟨v, hv, -⟩ := Option.map_eq_some_iff.1 hb
  exact ⟨v, hv⟩

end One

/-- A number and its sibling are the two children of one parent. -/
theorem two_children (i : ℕ) :
    (i = 2 * (i / 2) ∧ i ^^^ 1 = 2 * (i / 2) + 1) ∨
      (i = 2 * (i / 2) + 1 ∧ i ^^^ 1 = 2 * (i / 2)) := by
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · left
    rw [Nat.xor_one_of_even (Nat.even_iff.2 h)]
    omega
  · right
    rw [Nat.xor_one_of_odd (Nat.odd_iff.2 h)]
    omega

section One'
variable (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (cfg : ByteArray)

/-- **On the way up from a listed leaf.** At each level m up to the top the vertex on the way is in
the record. -/
theorem walked_up {y : OpenedY} (W : Walked h cfg y) (x : ℕ) (hx : x ∈ y.2.1) :
    ∀ m, m ≤ y.1.a → ∃ v, seenAt y.2.2.seen (y.1.a - m) (x / 2 ^ m) = some v
  | 0, _ => by
    rw [Nat.sub_zero, Nat.pow_zero, Nat.div_one]
    exact walked_leaf h cfg W x hx
  | m + 1, hm => by
    obtain ⟨v, hv⟩ := walked_up W x hx m (Nat.le_of_succ_le hm)
    obtain ⟨s, hs⟩ := walked_sib h cfg W x hx m hm
    have ed : y.1.a - m = (y.1.a - (m + 1)) + 1 := by omega
    have ex : x / 2 ^ (m + 1) = x / 2 ^ m / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    rw [ed] at hv hs
    rw [ex]
    rcases two_children (x / 2 ^ m) with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨_, (walked_nodes h cfg W).1 _ (x / 2 ^ m / 2) v s (by rw [← e1]; exact hv)
        (by rw [← e2]; exact hs)⟩
    · exact ⟨_, (walked_nodes h cfg W).1 _ (x / 2 ^ m / 2) s v (by rw [← e2]; exact hs)
        (by rw [← e1]; exact hv)⟩

/-- Below the top: the two children of the next vertex on the way up, and that vertex with their
hash. -/
theorem walked_step {y : OpenedY} (W : Walked h cfg y) (x : ℕ) (hx : x ∈ y.2.1) (m : ℕ)
    (hm : m < y.1.a) :
    ∃ l r, seenAt y.2.2.seen (y.1.a - m) (2 * (x / 2 ^ m / 2)) = some l ∧
      seenAt y.2.2.seen (y.1.a - m) (2 * (x / 2 ^ m / 2) + 1) = some r ∧
      seenAt y.2.2.seen (y.1.a - (m + 1)) (x / 2 ^ m / 2) = some (h 166 0 0 cfg (l ++ r)) := by
  obtain ⟨v, hv⟩ := walked_up h cfg W x hx m (Nat.le_of_lt hm)
  obtain ⟨s, hs⟩ := walked_sib h cfg W x hx m hm
  have ed : y.1.a - m = (y.1.a - (m + 1)) + 1 := by omega
  rcases two_children (x / 2 ^ m) with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have a1 : seenAt y.2.2.seen (y.1.a - m) (2 * (x / 2 ^ m / 2)) = some v := by
      rw [← e1]; exact hv
    have a2 : seenAt y.2.2.seen (y.1.a - m) (2 * (x / 2 ^ m / 2) + 1) = some s := by
      rw [← e2]; exact hs
    exact ⟨v, s, a1, a2, (walked_nodes h cfg W).1 _ _ v s (ed ▸ a1) (ed ▸ a2)⟩
  · have a1 : seenAt y.2.2.seen (y.1.a - m) (2 * (x / 2 ^ m / 2)) = some s := by
      rw [← e2]; exact hs
    have a2 : seenAt y.2.2.seen (y.1.a - m) (2 * (x / 2 ^ m / 2) + 1) = some v := by
      rw [← e1]; exact hv
    exact ⟨s, v, a1, a2, (walked_nodes h cfg W).1 _ _ s v (ed ▸ a1) (ed ▸ a2)⟩

end One'

/-! ## The table of a tree of the file -/

/-- g's node hash of the digests of two strings of 32 bytes is the digest of the format's vertex
hash of the two. -/
def NodeIs {I X : Type} {K : ℕ} {L : TypedOracleCompiler.Iop.BatchProtocolWithLeafBody I X} (g : Fam (typedOracleFamily 256 K L))
    (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (cfg : ByteArray) : Prop :=
  ∀ l r : ByteArray, l.size = 32 → r.size = 32 →
    nodeAt g (bytesToDig l) (bytesToDig r) = bytesToDig (h 166 0 0 cfg (l ++ r))

section Table
variable {I X : Type} {K : ℕ} {L : TypedOracleCompiler.Iop.BatchProtocolWithLeafBody I X} (g : Fam (typedOracleFamily 256 K L))
  (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (cfg : ByteArray) {W : Three.Whole}
  {r : Proof.TailRead} {j : ℕ} {z : Opened}

theorem vertexOf_some {a : ℕ} {seen : List (ℕ × ℕ × ByteArray)} {m n : ℕ} {v : ByteArray}
    (e : seenAt seen (a - m) n = some v) : vertexOf a seen m n = bytesToDig v := by
  unfold vertexOf
  rw [e]
  rfl

/-- **The table is consistent on the way up from a listed leaf.** -/
theorem rec_meets (hone : OneTable W r j) (hz : (j, z) ∈ ownRowsW W r)
    (hW : Walked h cfg z) (hnode : NodeIs g h cfg) (h32 : ∀ u ∈ recOf W r j, u.2.2.size = 32)
    (x : ℕ) (hx : x ∈ z.2.1) (m : ℕ) (hm : m < z.1.a) :
    vertexOf z.1.a (recOf W r j) (m + 1) (x / 2 ^ m / 2) =
      nodeAt g (vertexOf z.1.a (recOf W r j) m (2 * (x / 2 ^ m / 2)))
        (vertexOf z.1.a (recOf W r j) m (2 * (x / 2 ^ m / 2) + 1)) := by
  obtain ⟨l, rr, a1, a2, a3⟩ := walked_step h cfg hW x hx m hm
  have hlow : z.1.a - m ≠ 0 := by omega
  have htop : z.1.a - (m + 1) ≠ 0 ∨ x / 2 ^ m / 2 = 0 := by
    by_cases e : m + 1 = z.1.a
    · right
      have hlt : x < 2 ^ (m + 1) := by rw [e]; exact walked_lt h cfg hW x hx
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
      exact Nat.div_eq_of_lt hlt
    · left
      omega
  rw [vertexOf_some (seenAt_rec hone hz (Or.inl hlow) a1),
    vertexOf_some (seenAt_rec hone hz (Or.inl hlow) a2),
    vertexOf_some (seenAt_rec hone hz htop a3),
    hnode l rr (h32 _ (mem_recOf hz (seenAt_mem a1))) (h32 _ (mem_recOf hz (seenAt_mem a2)))]

/-- **At its top the table has the root to which the reader's walk led.** -/
theorem rec_root (hone : OneTable W r j) (hz : (j, z) ∈ ownRowsW W r)
    (hW : Walked h cfg z) :
    vertexOf z.1.a (recOf W r j) z.1.a 0 = bytesToDig z.2.2.root :=
  vertexOf_some (by
    rw [Nat.sub_self]
    exact seenAt_rec hone hz (Or.inr rfl) (walked_nodes h cfg hW).2)

end Table

end OnBytes.Maker
