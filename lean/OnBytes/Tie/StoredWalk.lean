-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/StoredWalk.lean: two openings that walk to their roots, as one walk over two trees.

The strict reader walks each stored table's opening by itself, on bytes. The compiled verifier
walks both tables' openings at once: one forest of two trees of one depth, on digests, with the
sibling digests read off whole paths. This file shows that the second walk ends in the two roots
if the first two do. A table of which nothing is opened has no walk, and its root is compared with
nothing.

Main definition: `WalkOK`.
Main theorems: `part_ok`, `walk_two`.
It claims nothing on what a chain proves.
-/
import Run.Toy1TieTree
import Run.WalkTieProofs
import OnBytes.Tie.TwoTrees

set_option autoImplicit false

namespace OnBytes.Tie
open Octopus Run Run.TieTree

/-- A number after d levels is a number of the start, halved d times. -/
theorem mem_upN : ∀ (d : ℕ) (js : List ℕ) (x : ℕ), x ∈ upN d js → ∃ k ∈ js, x = k / 2 ^ d
  | 0, _, x, h => ⟨x, h, by simp⟩
  | d + 1, js, x, h => by
    obtain ⟨k', hk', e'⟩ := mem_upN d (up js) x h
    obtain ⟨k, hk, e⟩ := mem_up js k' hk'
    refine ⟨k, hk, ?_⟩
    rw [e', e, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

/-- Empty stays empty. -/
theorem upN_nil : ∀ d : ℕ, upN d [] = []
  | 0 => rfl
  | d + 1 => upN_nil d

/-- One tree's opening, on bytes: nothing of the tree is opened, or the walk from the opened
leaves v at the sorted places xs, with the given digests g, ends in the root. In the second case the
leaves, the digests and the root have 32 bytes, and g has exactly as many digests as the walk
takes. -/
def WalkOK (hP : ByteArray → ByteArray → ByteArray) (d : ℕ) (xs : List ℕ) (v g : List ByteArray)
    (root : ByteArray) : Prop :=
  (xs = [] ∧ v = []) ∨
  (xs ≠ [] ∧ xs.Pairwise (· < ·) ∧ (∀ x ∈ xs, x < 2 ^ d) ∧ v.length = xs.length ∧
    g.length = need d xs ∧ (∀ x ∈ v, x.size = 32) ∧ (∀ x ∈ g, x.size = 32) ∧ root.size = 32 ∧
    (octF hP d xs v g).headD default = root)

section
variable (hP : ByteArray → ByteArray → ByteArray) (h32 : ∀ l r, (hP l r).size = 32)

include h32 in
/-- If one tree's opening walks to its root on bytes, its share of the walk on digests ends in that
root. t is the tree's number in the forest, and R gives that root at t. The combining function must
give 32 bytes. -/
theorem part_ok (d : ℕ) (xs : List ℕ) (v g : List ByteArray) (root : ByteArray) (t : ℕ)
    (R : ℕ → Iop.Dig 256) (hR : R t = bytesToDig root) (hw : WalkOK hP d xs v g root) :
    (((upN d xs).map (t + ·)).zip (octF (digFn hP) d xs (v.map bytesToDig)
      (reads d (xs.zip (fill d xs (g.map bytesToDig)))))).all
        (fun m => decide (m.2 = R m.1)) = true := by
  rcases hw with ⟨rfl, rfl⟩ | ⟨hne, hp, hb, hl, hg, hv, hgs, hr, hwalk⟩
  · rw [upN_nil]
    rfl
  · have hu1 := WalkTie.upN_one d xs hne hp hb
    obtain ⟨u, hu⟩ := List.length_eq_one_iff.1 hu1
    have hu0 : u = 0 := by
      obtain ⟨k, hk, e⟩ := mem_upN d xs u (by rw [hu]; simp)
      rw [e]
      exact Nat.div_eq_of_lt (hb k hk)
    subst hu0
    have hrd : reads d (xs.zip (fill d xs (g.map bytesToDig))) = g.map bytesToDig := by
      rw [reads_fill (Iop.Dig 256) d xs (g.map bytesToDig) (by rw [List.length_map, hg]),
        List.take_of_length_le (by rw [List.length_map, hg])]
    rw [hrd, oct_dig hP h32 d xs v g hl (le_of_eq hg.symm) hv hgs, hu]
    have ho : (octF hP d xs v g).length = 1 := (WalkTie.length_octF hP d xs v g hl).trans hu1
    obtain ⟨r, hr'⟩ := List.length_eq_one_iff.1 ho
    rw [hr'] at hwalk ⊢
    have hrr : r = root := hwalk
    subst hrr
    simp [hR]

include h32 in
/-- Two trees' openings that walk to their roots on bytes (`WalkOK`): the one walk over both on
digests ends in the two roots, which R gives at 0 and 1. The combining function must give 32 bytes.
An empty opening has no walk, and its root is compared with nothing. -/
theorem walk_two (d : ℕ) (xs0 xs1 : List ℕ) (v0 v1 g0 g1 : List ByteArray)
    (root0 root1 : ByteArray) (R : ℕ → Iop.Dig 256) (hR0 : R 0 = bytesToDig root0)
    (hR1 : R 1 = bytesToDig root1) (hw0 : WalkOK hP d xs0 v0 g0 root0)
    (hw1 : WalkOK hP d xs1 v1 g1 root1) :
    ((upN d (xs0 ++ xs1.map (2 ^ d + ·))).zip (octF (digFn hP) d (xs0 ++ xs1.map (2 ^ d + ·))
      (v0.map bytesToDig ++ v1.map bytesToDig)
      (reads d (xs0.zip (fill d xs0 (g0.map bytesToDig)) ++
        (xs1.zip (fill d xs1 (g1.map bytesToDig))).map fun x => (2 ^ d + x.1, x.2))))).all
        (fun m => decide (m.2 = R m.1)) = true := by
  have hb0 : ∀ x ∈ xs0, x < 2 ^ d := by
    rcases hw0 with ⟨rfl, -⟩ | ⟨-, -, hb, -⟩
    · intro x hx
      cases hx
    · exact hb
  have hl0 : v0.length = xs0.length := by
    rcases hw0 with ⟨rfl, rfl⟩ | ⟨-, -, -, hl, -⟩
    · rfl
    · exact hl
  have f0 : (xs0.zip (fill d xs0 (g0.map bytesToDig))).map (·.1) = xs0 :=
    List.map_fst_zip (le_of_eq (length_fill d xs0 _).symm)
  have f1 : (xs1.zip (fill d xs1 (g1.map bytesToDig))).map (·.1) = xs1 :=
    List.map_fst_zip (le_of_eq (length_fill d xs1 _).symm)
  have f1' : (xs1.zip (fill d xs1 (g1.map bytesToDig))).map (2 ^ d + ·.1)
      = xs1.map (2 ^ d + ·) := by
    conv_rhs => rw [← f1]
    rw [List.map_map]
    rfl
  have hz0 : ∀ x ∈ xs0.zip (fill d xs0 (g0.map bytesToDig)), x.1 < 2 ^ d :=
    fun x hx => hb0 x.1 (List.of_mem_zip hx).1
  have e1 := octF_two (digFn hP) d (xs0.zip (fill d xs0 (g0.map bytesToDig)))
    (xs1.zip (fill d xs1 (g1.map bytesToDig))) (v0.map bytesToDig) (v1.map bytesToDig) hz0
    (by rw [List.length_map, List.length_zip, length_fill, Nat.min_self, hl0])
  have e2 := upN_two d (xs0.zip (fill d xs0 (g0.map bytesToDig)))
    (xs1.zip (fill d xs1 (g1.map bytesToDig))) hz0
  rw [f0, f1, f1'] at e1 e2
  rw [e1, e2, List.zip_append (by
    rw [WalkTie.length_octF (digFn hP) d xs0 _ _ (by rw [List.length_map, hl0])]),
    List.all_append, Bool.and_eq_true]
  refine ⟨?_, part_ok hP h32 d xs1 v1 g1 root1 1 R hR1 hw1⟩
  have := part_ok hP h32 d xs0 v0 g0 root0 0 R hR0 hw0
  simpa using this

end

end OnBytes.Tie

#print axioms OnBytes.Tie.walk_two
