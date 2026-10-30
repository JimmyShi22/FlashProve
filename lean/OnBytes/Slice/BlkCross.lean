-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkCross.lean: from coefficients by numbers to vectors on a stage's entries: the
general part.

The program names a coefficient of a row by three numbers: an oracle message, one of its two tables,
an index in that table (OnBytes/Slice/BlkRowRead.lean: RowF). The field's side names an entry of a
sent message by a pair of a row and a place, in the main or the mask part (OnBytes/Slice/
KeyGroup.lean: Mb.cd.J), and writes a row of a group as a vector on the entries of the stage's
tables, made of coefficients on entries of members (OnBytes/Slice/KeyLinRows.lean: Gp.push). It
compares two such vectors at the members' entries alone (OnBytes/Slice/KeyLinExit.lean: Gp.Has).
This file has what is common to all crossings from the one naming to the other.

 The index of a member's entry in the program's table (Mb.idx): row + 2 ^ (row bits) * place.
 A pushed vector at a member's entry (push_ent, sum_at): the coefficient of the one index that is
   sent there, or 0.
 A vector that lies in a main table in one of the program's two layouts (LaidOn; cross_laid): if the
   entries phi a of a member are where the program has the vector's entries number num a, then the
   pushed vector with the coefficients c a has, at each entry of that member, the program's
   coefficient "F at the number of the vector's entry that stands at the index" (laid,
   OnBytes/Slice/BlkLinRead.lean), for every F that is c on the numbers and 0 off them.
 The two layouts' maps between an entry's number and an index are inverse to each other
   (entryAt_index, index_entryAt).

Main definitions: `swapDigits`, `Mb.idx`, `LaidOn`.
Main theorems: `swapDigits_swap`, `entryAt_index`, `index_entryAt`, `Mb.idx_inj`, `sum_at`,
`push_ent`, `push_other`, `cross_laid`, `cross_one`.

Not claimed. Nothing on a row of the program: that is not said here.

-/
import OnBytes.Slice.KeyLinExit
import OnBytes.Slice.KeyExit
import OnBytes.Slice.BlkLinRead

set_option autoImplicit false

namespace OnBytes.Slice
open Prob Cb

/-! ## The two layouts -/

/-- The a lowest digits of a number of a + b digits moved above the others. -/
def swapDigits (a b n : ℕ) : ℕ := n / 2 ^ a + n % 2 ^ a * 2 ^ b

/-- The result has a + b digits. -/
theorem swapDigits_lt (a b n : ℕ) (h : n < 2 ^ (a + b)) : swapDigits a b n < 2 ^ (a + b) := by
  have hq : n / 2 ^ a < 2 ^ b := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.add_comm]
    exact h
  have hr := Nat.mod_lt n (Nat.two_pow_pos a)
  unfold swapDigits
  calc n / 2 ^ a + n % 2 ^ a * 2 ^ b < 2 ^ b + n % 2 ^ a * 2 ^ b := Nat.add_lt_add_right hq _
    _ = (n % 2 ^ a + 1) * 2 ^ b := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    _ ≤ 2 ^ a * 2 ^ b := Nat.mul_le_mul_right _ hr
    _ = 2 ^ (a + b) := (Nat.pow_add 2 _ _).symm

/-- Moved there and back. -/
theorem swapDigits_swap (a b n : ℕ) (h : n < 2 ^ (a + b)) :
    swapDigits b a (swapDigits a b n) = n := by
  have hq : n / 2 ^ a < 2 ^ b := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.add_comm]
    exact h
  unfold swapDigits
  rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos b), Nat.div_eq_of_lt hq, Nat.zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq, Nat.add_comm, Nat.mul_comm]
  exact Nat.div_add_mod n (2 ^ a)

/-- The number of the entry at an index, by digits. -/
theorem entryAt_swap (l : VectorLay) (t : ℕ) :
    l.entryAt t = if l.rowsHigh then swapDigits l.rowBits l.placeBits t else t := rfl

/-- The index of an entry, by digits. -/
theorem index_swap (l : VectorLay) (e : ℕ) :
    l.index e = if l.rowsHigh then swapDigits l.placeBits l.rowBits e else e := rfl

/-- The entry at an index of the table has a number below the table's size. -/
theorem entryAt_lt (l : VectorLay) (t : ℕ) (h : t < 2 ^ l.bits) : l.entryAt t < 2 ^ l.bits := by
  rw [entryAt_swap]
  split
  · exact swapDigits_lt _ _ _ h
  · exact h

/-- An entry with a number below the table's size has an index of the table. -/
theorem index_lt (l : VectorLay) (e : ℕ) (h : e < 2 ^ l.bits) : l.index e < 2 ^ l.bits := by
  rw [index_swap]
  split
  · have h' : e < 2 ^ (l.placeBits + l.rowBits) := by
      rw [Nat.add_comm]
      exact h
    have := swapDigits_lt _ _ _ h'
    rw [Nat.add_comm] at this
    exact this
  · exact h

/-- **The entry at the index of an entry is that entry.** -/
theorem entryAt_index (l : VectorLay) (e : ℕ) (h : e < 2 ^ l.bits) :
    l.entryAt (l.index e) = e := by
  rw [entryAt_swap, index_swap]
  split
  · exact swapDigits_swap _ _ _ (by rw [Nat.add_comm]; exact h)
  · rfl

/-- **The index of the entry at an index is that index.** -/
theorem index_entryAt (l : VectorLay) (t : ℕ) (h : t < 2 ^ l.bits) :
    l.index (l.entryAt t) = t := by
  rw [entryAt_swap, index_swap]
  split
  · exact swapDigits_swap _ _ _ h
  · rfl

/-! ## A member's entries by numbers -/

/-- **The table and the index at which the program has an entry of a sent message.** rbM, rbZ: the
row bits of the message's main and mask table. -/
def Mb.idx (M : Mb) (rbM rbZ : ℕ) : M.cd.J → Part × ℕ
  | .inl x => (.main, x.1.val + 2 ^ rbM * x.2.val)
  | .inr x => (.mask, x.1.val + 2 ^ rbZ * x.2.val)

/-- Different entries have different indices, if the rows fit the row bits. -/
theorem Mb.idx_inj (M : Mb) (rbM rbZ : ℕ) (hM : M.nM ≤ 2 ^ rbM) (hZ : M.nZ ≤ 2 ^ rbZ) :
    Function.Injective (M.idx rbM rbZ) := by
  have key : ∀ (rb n r r' p p' : ℕ), n ≤ 2 ^ rb → r < n → r' < n →
      r + 2 ^ rb * p = r' + 2 ^ rb * p' → r = r' ∧ p = p' := by
    intro rb n r r' p p' hn hr hr' h
    have h1 := congrArg (· % 2 ^ rb) h
    have h2 := congrArg (· / 2 ^ rb) h
    simp only [Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ (Nat.two_pow_pos rb)] at h1 h2
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hr hn), Nat.mod_eq_of_lt (lt_of_lt_of_le hr' hn)] at h1
    rw [Nat.div_eq_of_lt (lt_of_lt_of_le hr hn), Nat.div_eq_of_lt (lt_of_lt_of_le hr' hn),
      Nat.zero_add, Nat.zero_add] at h2
    exact ⟨h1, h2⟩
  rintro (⟨r, p⟩ | ⟨r, p⟩) (⟨r', p'⟩ | ⟨r', p'⟩) h
  · obtain ⟨h1, h2⟩ := key rbM M.nM r.val r'.val p.val p'.val hM r.isLt r'.isLt
      (congrArg Prod.snd h)
    rw [Fin.ext h1, Fin.ext h2]
  · cases congrArg Prod.fst h
  · cases congrArg Prod.fst h
  · obtain ⟨h1, h2⟩ := key rbZ M.nZ r.val r'.val p.val p'.val hZ r.isLt r'.isLt
      (congrArg Prod.snd h)
    rw [Fin.ext h1, Fin.ext h2]

/-! ## A pushed vector at a member's entry -/

/-- **Coefficients on different places, read at a place**: any function that is c a at the place of
a, and 0 at every place of no a. -/
theorem sum_at {I T : Type} [Fintype I] [DecidableEq T] (φ : I → T) (c : I → GE) (val : T → GE)
    (hφ : Function.Injective φ) (h1 : ∀ a, val (φ a) = c a)
    (h0 : ∀ j, (∀ a, φ a ≠ j) → val j = 0) (j : T) :
    (∑ a, if φ a = j then c a else 0) = val j := by
  by_cases h : ∃ a, φ a = j
  · obtain ⟨a, rfl⟩ := h
    rw [Finset.sum_eq_single a, if_pos rfl, h1]
    · intro b _ hb
      exact if_neg fun e => hb (hφ e)
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [h0 j fun a e => h ⟨a, e⟩]
    exact Finset.sum_eq_zero fun a _ => if_neg fun e => h ⟨a, e⟩

section
variable {s : Sg} {G : Gp s}

/-- A pushed vector at an entry of the same member. -/
theorem push_ent (hA : G.Apart) (i : G.ι) {I : Type} [Fintype I] (φ : I → (G.mb i).cd.J)
    (c : I → GE) (j : (G.mb i).cd.J) :
    G.push i φ c (G.ent ⟨i, j⟩) = ∑ a, if φ a = j then c a else 0 := by
  unfold Gp.push
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : φ a = j
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg fun e => h ?_]
    have := Gp.ent_inj hA e
    exact eq_of_heq (Sigma.mk.inj this).2

/-- A pushed vector at an entry of another member. -/
theorem push_other (hA : G.Apart) (i i' : G.ι) (hi : i ≠ i') {I : Type} [Fintype I]
    (φ : I → (G.mb i).cd.J) (c : I → GE) (j : (G.mb i').cd.J) :
    G.push i φ c (G.ent ⟨i', j⟩) = 0 := by
  unfold Gp.push
  refine Finset.sum_eq_zero fun a _ => if_neg fun e => hi ?_
  exact (Sigma.mk.inj (Gp.ent_inj hA e)).1

end

/-! ## A vector in a main table -/

/-- **The entries phi a of the message M are where the program has the entries number num a of a
vector** that lies in the message's main table in the layout lay. -/
def LaidOn (M : Mb) (rbZ : ℕ) (lay : VectorLay) {I : Type} (φ : I → M.cd.J) (num : I → ℕ) : Prop :=
  ∀ a, M.idx lay.rowBits rbZ (φ a) = (.main, lay.index (num a))

/-- **The crossing for a vector in a main table.** The sum is the pushed vector at the entry j of
its member (push_ent). -/
theorem cross_laid (M : Mb) (rbZ : ℕ) (lay : VectorLay) {I : Type} [Fintype I] (φ : I → M.cd.J)
    (num : I → ℕ) (c : I → GE) (F : ℕ → GE) (hL : LaidOn M rbZ lay φ num)
    (hnum : Function.Injective num) (hlt : ∀ a, num a < 2 ^ lay.bits)
    (hM : M.nM ≤ 2 ^ lay.rowBits) (hZ : M.nZ ≤ 2 ^ rbZ) (hl : M.C.l ≤ 2 ^ lay.placeBits)
    (h1 : ∀ a, F (num a) = c a) (h0 : ∀ e, (∀ a, num a ≠ e) → F e = 0) (j : M.cd.J) :
    (∑ a, if φ a = j then c a else 0) =
      if (M.idx lay.rowBits rbZ j).1 = .main then laid lay F (M.idx lay.rowBits rbZ j).2
      else 0 := by
  have hinj := M.idx_inj lay.rowBits rbZ hM hZ
  refine sum_at φ c (fun j => if (M.idx lay.rowBits rbZ j).1 = .main then
    laid lay F (M.idx lay.rowBits rbZ j).2 else 0) (fun a b e => hnum ?_) (fun a => ?_)
    (fun j hj => ?_) j
  · have e1 := congrArg (fun x => lay.entryAt (M.idx lay.rowBits rbZ x).2) e
    simp only [hL a, hL b] at e1
    rw [entryAt_index lay _ (hlt a), entryAt_index lay _ (hlt b)] at e1
    exact e1
  · show (if (M.idx lay.rowBits rbZ (φ a)).1 = .main then
      laid lay F (M.idx lay.rowBits rbZ (φ a)).2 else 0) = c a
    rw [hL a, if_pos rfl]
    unfold laid
    rw [Nat.mod_eq_of_lt (index_lt lay _ (hlt a)), entryAt_index lay _ (hlt a), h1]
  · rcases j with ⟨r, p⟩ | ⟨r, p⟩
    · have hidx : r.val + 2 ^ lay.rowBits * p.val < 2 ^ lay.bits := by
        have hr := lt_of_lt_of_le r.isLt hM
        have hp := lt_of_lt_of_le p.isLt hl
        calc r.val + 2 ^ lay.rowBits * p.val < 2 ^ lay.rowBits + 2 ^ lay.rowBits * p.val :=
              Nat.add_lt_add_right hr _
          _ = 2 ^ lay.rowBits * (p.val + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
          _ ≤ 2 ^ lay.rowBits * 2 ^ lay.placeBits := Nat.mul_le_mul_left _ hp
          _ = 2 ^ lay.bits := (Nat.pow_add 2 _ _).symm
      show laid lay F (r.val + 2 ^ lay.rowBits * p.val) = 0
      unfold laid
      rw [Nat.mod_eq_of_lt hidx]
      refine h0 _ fun a e => hj a (hinj ?_)
      rw [hL a, e, index_entryAt lay _ hidx]
      rfl
    · exact if_neg (by
        show ¬ (Part.mask = Part.main)
        exact fun e => by cases e)

/-- **The crossing for one entry**: the coefficient 1 on the entry j0. -/
theorem cross_one {T : Type} [DecidableEq T] (j0 j : T) :
    (∑ _a : Unit, if j0 = j then (1 : GE) else 0) = if j0 = j then 1 else 0 :=
  Fintype.sum_unique _

end OnBytes.Slice
