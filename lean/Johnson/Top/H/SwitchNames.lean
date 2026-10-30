-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchNames.lean: the dictionary between the names of a sending's entries in
the typed library and the program's numbers, and what coefficients that are carried along a map of
names give when they are read at a table's index.

An entry of the signature of a sending (`Johnson.Pack.sigOf cs l`) is a message of the list l and a
coordinate of its code's message: a main row and a place in it, or a mask row and a place. The
program names the same entry by three numbers: which message of the sending; which of its two
tables; the index row + 2^rowBits * place, rowBits the table's row bits (OnBytes/Iop/Cs.lean,
`cutIndex`; OnBytes/Iop/Send.lean). Definitions, statements and proofs.

Main names:
  `idxOf rows ell x`: the index of (row, place). `idxOf_inj`, `idxOf_mod`, `idxOf_div`.
  `entAt cs l n`: the three numbers of the entry n. `entAt_inj`: one to one.
  `pushTo_elim`: coefficients carried along a map on a sum of two types: the two halves' sum.
  `pushTo_at`: if every name of a map lies in the table (o, part), at the index f i, then the
    carried coefficients are, at an entry of that table, the sum of the c i with f i = its index,
    and 0 at every other entry.
  `pushTo_stretch`: for names on a stretch of the rest, f i = places.get (first + i): that sum is
    `stretchAt` (OnBytes/Slice/BlkCsStretch.lean).
  `pushTo_one`: where f is one to one: the one coefficient whose index is met, or 0.
Limits: which map of names a switch of the programs has is not said here. Nothing on soundness.

-/
import Johnson.Pack.PortF
import Cb.Req1.LdSegAfterRows
import OnBytes.Slice.BlkCsStretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb Johnson.Pack

/-- The index in its table of the entry at (row, place). -/
def idxOf (rows ell : ℕ) (x : Fin rows × Fin ell) : ℕ := x.1.val + 2 ^ ceilLog2 rows * x.2.val

theorem idxOf_mod (rows ell : ℕ) (x : Fin rows × Fin ell) :
    idxOf rows ell x % 2 ^ ceilLog2 rows = x.1.val := by
  unfold idxOf
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le x.1.isLt (le_two_pow_ceilLog2 rows))

theorem idxOf_div (rows ell : ℕ) (x : Fin rows × Fin ell) :
    idxOf rows ell x / 2 ^ ceilLog2 rows = x.2.val := by
  unfold idxOf
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (lt_of_lt_of_le x.1.isLt (le_two_pow_ceilLog2 rows)), Nat.zero_add]

theorem idxOf_inj (rows ell : ℕ) : Function.Injective (idxOf rows ell) := by
  intro x y h
  have h1 := idxOf_mod rows ell x
  have h2 := idxOf_div rows ell x
  rw [h, idxOf_mod] at h1
  rw [h, idxOf_div] at h2
  exact Prod.ext (Fin.ext h1.symm) (Fin.ext h2.symm)

/-- The table and the index of a coordinate of a shape's message. -/
def coordAt (cs : Codes) (s : OracleShape) (j : (portCode cs s).J) : Part × ℕ :=
  Sum.elim (fun x => (Part.main, idxOf s.mainRows (pMain cs s).ell x))
    (fun x => (Part.mask, idxOf s.maskRows (pMask cs s).ell x))
    (j : (Fin s.mainRows × Fin (pMain cs s).ell) ⊕ (Fin s.maskRows × Fin (pMask cs s).ell))

theorem coordAt_inj (cs : Codes) (s : OracleShape) : Function.Injective (coordAt cs s) := by
  intro a b h
  change (Fin s.mainRows × Fin (pMain cs s).ell) ⊕ (Fin s.maskRows × Fin (pMask cs s).ell) at a b
  rcases a with a | a <;> rcases b with b | b <;> simp only [coordAt, Sum.elim_inl, Sum.elim_inr,
    Prod.mk.injEq, reduceCtorEq, false_and, true_and] at h
  · exact congrArg Sum.inl (idxOf_inj _ _ h)
  · exact congrArg Sum.inr (idxOf_inj _ _ h)

variable (cs : Codes) (l : List (OracleShape × ℕ))

/-- **The dictionary**: which message of the sending; which table; the index. -/
def entAt (n : (sigOf cs l).Ent) : ℕ × Part × ℕ := (n.1.val, coordAt cs (l.get n.1).1 n.2)

theorem entAt_inj : Function.Injective (entAt cs l) := by
  rintro ⟨i, a⟩ ⟨i', b⟩ h
  have hi : i = i' := Fin.ext (congrArg Prod.fst h)
  subst hi
  have hj : coordAt cs (l.get i).1 a = coordAt cs (l.get i).1 b := congrArg Prod.snd h
  rw [coordAt_inj cs _ hj]

/-- Coefficients carried along a map on a sum of two types. -/
theorem pushTo_elim {I I' J : Type} [Fintype I] [Fintype I'] (p : I → J) (q : I' → J)
    (c : I ⊕ I' → GE) (n : J) :
    pushTo (Sum.elim p q) c n =
      pushTo p (fun i => c (.inl i)) n + pushTo q (fun i => c (.inr i)) n := by
  unfold pushTo
  rw [Fintype.sum_sum_type]
  rfl

/-- **Carried coefficients, read at a table's index.** -/
theorem pushTo_at {I : Type} [Fintype I] (p : I → (sigOf cs l).Ent) (c : I → GE) (o : ℕ)
    (part : Part) (f : I → ℕ) (hp : ∀ i, entAt cs l (p i) = (o, part, f i))
    (n : (sigOf cs l).Ent) :
    pushTo p c n =
      if (entAt cs l n).1 = o ∧ (entAt cs l n).2.1 = part then
        ∑ i, if f i = (entAt cs l n).2.2 then c i else 0
      else 0 := by
  classical
  unfold pushTo
  have key : ∀ i, p i = n ↔ (o, part, f i) = entAt cs l n := fun i =>
    ⟨fun h => by rw [← hp i, h], fun h => entAt_inj cs l (by rw [hp i, h])⟩
  split
  · rename_i h
    refine Finset.sum_congr rfl fun i _ => ?_
    have : p i = n ↔ f i = (entAt cs l n).2.2 := by
      rw [key i]
      constructor
      · intro e; rw [← e]
      · intro e
        rw [e, ← h.1, ← h.2]
    simp only [this]
  · rename_i h
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    intro e
    apply h
    rw [← (key i).1 e]
    exact ⟨rfl, rfl⟩

/-- **On a stretch of the rest.** -/
theorem pushTo_stretch (places : SwitchPlaces) (first count : ℕ) (c : Fin count → GE) (J : ℕ) :
    (∑ i : Fin count, if places.get (first + i.val) = J then c i else 0) =
      stretchAt places first count (fun i => if h : i < count then c ⟨i, h⟩ else 0) J := by
  unfold stretchAt
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [i.isLt]

/-- Where the indices are one to one at most one coefficient is met. -/
theorem pushTo_one {I : Type} [Fintype I] [DecidableEq I] (f : I → ℕ) (hf : Function.Injective f)
    (c : I → GE) (i₀ : I) : (∑ i, if f i = f i₀ then c i else 0) = c i₀ := by
  rw [Finset.sum_eq_single i₀]
  · simp
  · intro i _ hne
    rw [if_neg fun e => hne (hf e)]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Johnson.Top.H

#print axioms Johnson.Top.H.entAt_inj
#print axioms Johnson.Top.H.pushTo_at
#print axioms Johnson.Top.H.pushTo_stretch
