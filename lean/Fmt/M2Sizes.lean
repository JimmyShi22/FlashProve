-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2Sizes.lean: the second toy (a test protocol, a chain of three links): how many entries the
forms have that the blocks of Fmt/M2Send.lean, Fmt/M2Psc.lean and Fmt/M2Loc.lean make.

Theorems and proofs. Core Lean, no Mathlib.
A block is the function of one step of the protocol. A form is the vector of coefficients of a
linear claim (a row) on an oracle message's table; l is the length of a main row and l_zk (in Lean:
lz) that of a mask row. A member (`Mem`, Fmt/M2Types.lean) is an oracle message of a group. The
verifier draws a point, and the prover answers with one field element for each sampled message; the
sample row is the linear claim that such an answer makes. Each sampled message reads the first
coordinates of the point, as many as its own cube has (`cubeOf`, Fmt/M2Types.lean). The head of
Fmt/M2Loc.lean says what the switch does, and what the carrying message, the kept row and its second
sending are.

Why: at the closing of a group the verifier draws one element theta and sums all open rows of the
group under its powers. Fmt/M2BatchEq.lean proves that a closing's fast form (`batch`) equals its
meaning (`batchLit`: every row written out), at the blocks of Fmt/M2All.lean and the draws' rows
`drawL` (Fmt/M2Loc.lean), under conditions on sizes. Among them are the lengths of the sums in front
of the draws' rows; a draw is a position that the verifier has drawn. With these lemmas,
Fmt/M2DecEq.lean proves that the conditions hold of the rows that the frame really makes (there:
where the frame's test on sizes has passed). The frame is the decision's pass through the rounds
(Fmt/M2Dec.lean).

Main names:
  `pow_split`, `size_onMask`: two small facts on numbers and on a form on a mask row.
  `length_eqFold`, `size_pv`: the weights of a point of n coordinates: 2^n entries.
  `size_sample_main`: the sample row's form on a member's own main table has 2^(bits of its rows) l
    entries, if l is a power of two and the point has at least the member's cube's coordinates.
  `size_sample_mask`: the sample row's form on the member's own mask table has this many
    entries: none without mask rows; else 2^(bits of its mask rows) l_zk, under the like
    conditions.
  `size_halfRow`, `size_psc_main`, `size_psc_mask`: the three rows of a link's sum-check: l entries
    on a row, if gamma has V coordinates and l = 2^(V + 1); l_zk on the mask row.
  `size_twoRows`, `size_overP`, `size_carried_g`, `size_carried_p`, `size_oldSample_g`,
    `size_oldSample_p`, `size_drawL_g`: a row that the switch makes has 2 l entries on the carrying
    message (its form g) and l, or none, on the second sending (its form p); at a draw the lemma
    (`size_drawL_g`) is on g alone.

Limits: this file says nothing on values.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M2Send
import Fmt.M2Psc
import Fmt.M2Loc

set_option autoImplicit false

namespace Fmt.M2.Sizes
open Fmt.M1

theorem length_eqFold (f : Fld) :
    ∀ (z T : List E), (z.foldl (eqStep f) T).length = T.length * 2 ^ z.length
  | [], T => by simp
  | a :: z, T => by
      rw [List.foldl_cons, length_eqFold f z]
      unfold eqStep
      rw [List.length_append, List.length_map, List.length_map, List.length_cons, Nat.pow_succ,
        ← Nat.two_mul, Nat.mul_comm 2, Nat.mul_assoc, Nat.mul_comm 2]

/-- the weights of a point of n coordinates: 2^n entries -/
theorem size_pv (f : Fld) (s : E) (z : List E) : (pv f s z).size = 2 ^ z.length := by
  unfold pv
  rw [List.size_toArray, length_eqFold]
  simp

theorem pow_split (a b l : Nat) (hl : l = 2 ^ b) : 2 ^ (a + b) = 2 ^ a * l := by
  rw [Nat.pow_add, hl]

/-- The sample row on a member's own main table. -/
theorem size_sample_main (f : Fld) (l lz : Nat) (m : Mem) (z : List E) (beta y : E)
    (hl : l = 2 ^ Nat.log2 l) (hz : cubeOf (Nat.log2 l) (Nat.log2 lz) m ≤ z.length) :
    (sampleOf f l lz m z beta y).1.size = 2 ^ clog m.rows * l := by
  have hA : clog m.rows + Nat.log2 l ≤ z.length := by
    unfold cubeOf at hz
    split at hz <;> omega
  have hT : (z.take (clog m.rows + Nat.log2 l)).length = clog m.rows + Nat.log2 l := by
    rw [List.length_take]
    omega
  unfold sampleOf
  dsimp only
  split
  · split
    · rw [Array.size_setIfInBounds, size_pv, hT]
      exact pow_split _ _ _ hl
    · rw [Array.size_setIfInBounds, Array.size_setIfInBounds, Array.size_setIfInBounds, size_pv, hT]
      exact pow_split _ _ _ hl
  · show (pv f _ (z.take (clog m.rows + Nat.log2 l))).size = _
    rw [size_pv, hT]
    exact pow_split _ _ _ hl

/-- The sample row on a member's own mask table. -/
theorem size_sample_mask (f : Fld) (l lz : Nat) (m : Mem) (z : List E) (beta y : E)
    (hl : lz = 2 ^ Nat.log2 lz) (hz : cubeOf (Nat.log2 l) (Nat.log2 lz) m ≤ z.length) :
    (sampleOf f l lz m z beta y).2.size = if m.masks == 0 then 0 else 2 ^ clog m.masks * lz := by
  unfold sampleOf
  dsimp only
  split
  · split <;> rfl
  · rename_i h0
    have hA : clog m.masks + Nat.log2 lz ≤ z.length := by
      unfold cubeOf at hz
      rw [if_neg h0] at hz
      omega
    show ((pv f _ (z.take (clog m.masks + Nat.log2 lz))).setIfInBounds _ beta).size = _
    rw [Array.size_setIfInBounds, size_pv, List.length_take, Nat.min_eq_left hA]
    exact pow_split _ _ _ hl

theorem size_halfRow (f : Fld) (s : E) (gamma : List E) :
    (halfRow f s gamma).size = 2 ^ (gamma.length + 1) := by
  unfold halfRow
  rw [size_pv, List.length_append]
  rfl

/-- The three rows of a link's sum-check, on a row. -/
theorem size_psc_main (f : Fld) (V l lz : Nat) (zeta : List E) (mu : E)
    (qs : List (E × E)) (p v : E × E) (eps : E) (gamma : List E) (beta : E)
    (hg : gamma.length = V) (hl : l = 2 ^ (V + 1)) :
    (pscOf f V l lz zeta mu qs p v eps gamma beta).1.1.size = l ∧
    (pscOf f V l lz zeta mu qs p v eps gamma beta).2.1.1.size = l ∧
    (pscOf f V l lz zeta mu qs p v eps gamma beta).2.2.1.size = l := by
  have h : ∀ s : E, (halfRow f s gamma).size = l := fun s => by rw [size_halfRow, hg, hl]
  exact ⟨h _, h _, h _⟩

theorem size_onMask (lz first : Nat) (g : Nat → E) : (onMask lz first g).size = lz := by
  unfold onMask
  simp

/-- The same three rows, on the mask row. -/
theorem size_psc_mask (f : Fld) (V l lz : Nat) (zeta : List E) (mu : E) (qs : List (E × E))
    (p v : E × E) (eps : E) (gamma : List E) (beta : E) :
    (pscOf f V l lz zeta mu qs p v eps gamma beta).1.2.1.size = lz ∧
    (pscOf f V l lz zeta mu qs p v eps gamma beta).2.1.2.1.size = lz ∧
    (pscOf f V l lz zeta mu qs p v eps gamma beta).2.2.2.1.size = lz :=
  ⟨size_onMask _ _ _, size_onMask _ _ _, size_onMask _ _ _⟩

theorem size_twoRows (l : Nat) (a b : Array E) : (twoRows l a b).size = 2 * l := by
  unfold twoRows
  simp

theorem size_overP (l : Nat) (Q : Array E) : (overP l Q).size = l := by
  unfold overP
  simp

theorem size_carried_g (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow) :
    (carried f C Z kept S).g.size = 2 * C.l :=
  size_twoRows _ _ _

theorem size_carried_p (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow) :
    (carried f C Z kept S).p.size = if kept then C.l else 0 := by
  cases kept
  · rfl
  · exact size_overP _ _

theorem size_oldSample_g (f : Fld) (C Z : Code) (Q : Array E) (y : E) :
    (oldSample f C Z Q y).g.size = 2 * C.l :=
  size_twoRows _ _ _

theorem size_oldSample_p (f : Fld) (C Z : Code) (Q : Array E) (y : E) :
    (oldSample f C Z Q y).p.size = C.l := size_overP _ _

/-- every row at a draw has 2 l entries on the carrying message -/
theorem size_drawL_g (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow) (x : Nat) (col : KCol) :
    ∀ R ∈ drawL f C Z kept S x col, R.g.size = 2 * C.l := by
  intro R hR
  cases kept
  · have e : ∃ a1 b1 p1 t1 a2 b2 p2 t2 a3 b3 p3 t3, drawL f C Z false S x col =
        [⟨twoRows C.l a1 b1, p1, t1⟩, ⟨twoRows C.l a2 b2, p2, t2⟩, ⟨twoRows C.l a3 b3, p3, t3⟩] :=
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
    obtain ⟨a1, b1, p1, t1, a2, b2, p2, t2, a3, b3, p3, t3, e⟩ := e
    rw [e] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl <;> exact size_twoRows _ _ _
  · have e : ∃ a1 b1 p1 t1 a2 b2 p2 t2 a3 b3 p3 t3 a4 b4 p4 t4, drawL f C Z true S x col =
        [⟨twoRows C.l a1 b1, p1, t1⟩, ⟨twoRows C.l a2 b2, p2, t2⟩,
          ⟨twoRows C.l a3 b3, p3, t3⟩, ⟨twoRows C.l a4 b4, p4, t4⟩] :=
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
    obtain ⟨a1, b1, p1, t1, a2, b2, p2, t2, a3, b3, p3, t3, a4, b4, p4, t4, e⟩ := e
    rw [e] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl <;> exact size_twoRows _ _ _

end Fmt.M2.Sizes
