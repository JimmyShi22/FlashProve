-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/DrawsOf.lean: what the list of draws of a round of the format contains.

The format makes a round's list of draws from the plan's entry and the round's kind
(Fmt/Rules6Draws.lean: `Fmt.dsOf`): first the positions, then the elements, then one draw of matrix
entries, and a sealed value in a round of that kind. OnBytes/Slice/Draws.lean has five notions on a
list of draws: `PlainDraws`, `nE`, `nP`, `AllPos`, `IsNZ`. This file computes each of them at the
list of a round, in terms of the entry's numbers.

Main theorems.
 `mem_dsOf`         every draw of a round is one of five.
 `plain_dsOf`       elements and positions alone, if the entry asks for no matrix entries and the
                    round is not a sealing.
 `nP_dsOf`          the number of positions is the entry's.
 `allPos_dsOf`      every position is drawn below 2 to the entry's exponent.
 `nE_dsOf`          the number of elements is the entry's `drawE`, in a round that is not one of
                    seeds, if `drawNZ` is at most `drawE`.
 `nE_dsOf_seed`     the same in a round of one seed (`drawNZ` is 1).
 `isNZ_dsOf_seed`   in a round of one seed the element number `drawE - 1` is drawn other than 0.

Not claimed. Nothing on the values that are drawn or on their laws. Nothing on a round of several
seeds beyond the first four theorems.
-/
import Fmt.Rules6Draws
import OnBytes.Slice.Draws

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## Which draws occur in a round -/

/-- The draws of seeds are elements. -/
theorem mem_dsSeeds (s v : ℕ) (d : Fmt.Draw) (h : d ∈ Fmt.dsSeeds s v) :
    d = .elem ∨ d = .elemNZ := by
  unfold Fmt.dsSeeds at h
  obtain ⟨l, hl, hd⟩ := List.mem_flatten.1 h
  rw [List.eq_of_mem_replicate hl] at hd
  rcases List.mem_append.1 hd with h1 | h1
  · exact Or.inl (List.eq_of_mem_replicate h1)
  · exact Or.inr (List.mem_singleton.1 h1)

/-- The draws of a round's elements are elements. -/
theorem mem_dsElems (e : Fmt.Entry) (k : Fmt.Kind) (d : Fmt.Draw) (h : d ∈ Fmt.dsElems e k) :
    d = .elem ∨ d = .elemNZ := by
  unfold Fmt.dsElems at h
  by_cases hk : k = .seeds
  · rw [if_pos hk] at h
    rcases List.mem_append.1 h with h1 | h1
    · exact mem_dsSeeds _ _ d h1
    · exact Or.inl (List.eq_of_mem_replicate h1)
  · rw [if_neg hk] at h
    rcases List.mem_append.1 h with h1 | h1
    · exact Or.inl (List.eq_of_mem_replicate h1)
    · exact Or.inr (List.eq_of_mem_replicate h1)

/-- Every draw of a round is one of five. -/
theorem mem_dsOf (e : Fmt.Entry) (k : Fmt.Kind) (d : Fmt.Draw) (h : d ∈ Fmt.dsOf e k) :
    d = .pos e.logN ∨ d = .elem ∨ d = .elemNZ ∨ d = .trits e.trits ∨
      (d = .sealed ∧ k = .sealed) := by
  unfold Fmt.dsOf at h
  rcases List.mem_append.1 h with h1 | h1
  · exact Or.inl (List.eq_of_mem_replicate h1)
  rcases List.mem_append.1 h1 with h2 | h2
  · rcases mem_dsElems e k d h2 with h3 | h3
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (Or.inl h3))
  rcases List.mem_cons.1 h2 with h3 | h3
  · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
  by_cases hk : k = .sealed
  · rw [if_pos hk] at h3
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨List.mem_singleton.1 h3, hk⟩)))
  · rw [if_neg hk] at h3
    exact absurd h3 List.not_mem_nil

/-! ## The notions that ask something of every draw, from the draws that occur -/

/-- A list without a sealed value, in which every draw of matrix entries is empty, is plain. -/
theorem plain_of_mem (ds : List Fmt.Draw) (hs : Fmt.Draw.sealed ∉ ds)
    (ht : ∀ n, Fmt.Draw.trits n ∈ ds → n = 0) : PlainDraws ds := by
  induction ds with
  | nil => exact trivial
  | cons d ds ih =>
      have hr : PlainDraws ds :=
        ih (fun h => hs (List.mem_cons_of_mem d h)) (fun n h => ht n (List.mem_cons_of_mem d h))
      cases d with
      | elem => exact hr
      | elemNZ => exact hr
      | pos _ => exact hr
      | trits n => exact ⟨ht n List.mem_cons_self, hr⟩
      | sealed => exact (hs List.mem_cons_self).elim

/-- If every position that occurs is drawn below 2^k, then `AllPos k` holds. -/
theorem allPos_of_mem (k : ℕ) (ds : List Fmt.Draw) (hp : ∀ k', Fmt.Draw.pos k' ∈ ds → k' = k) :
    AllPos k ds := by
  induction ds with
  | nil => exact trivial
  | cons d ds ih =>
      have hr : AllPos k ds := ih fun k' h => hp k' (List.mem_cons_of_mem d h)
      cases d with
      | elem => exact hr
      | elemNZ => exact hr
      | pos k' => exact ⟨hp k' List.mem_cons_self, hr⟩
      | trits _ => exact hr
      | sealed => exact hr

/-- A round's draws are elements and positions alone, if the entry asks for no matrix entries and
the round is not a sealing. -/
theorem plain_dsOf (e : Fmt.Entry) (k : Fmt.Kind) (ht : e.trits = 0) (hk : k ≠ .sealed) :
    PlainDraws (Fmt.dsOf e k) := by
  refine plain_of_mem _ (fun h => ?_) (fun n h => ?_)
  · rcases mem_dsOf e k _ h with h | h | h | h | h
    · cases h
    · cases h
    · cases h
    · cases h
    · exact hk h.2
  · rcases mem_dsOf e k _ h with h | h | h | h | h
    · cases h
    · cases h
    · cases h
    · exact (Fmt.Draw.trits.inj h).trans ht
    · cases h.1

/-- Every position of a round is drawn below 2 to the entry's exponent. -/
theorem allPos_dsOf (e : Fmt.Entry) (k : Fmt.Kind) : AllPos e.logN (Fmt.dsOf e k) := by
  refine allPos_of_mem _ _ fun k' h => ?_
  rcases mem_dsOf e k _ h with h | h | h | h | h
  · exact Fmt.Draw.pos.inj h
  · cases h
  · cases h
  · cases h
  · cases h.1

/-! ## The number of positions -/

/-- The positions of two lists, joined, are counted list by list. -/
theorem nP_append : ∀ a b : List Fmt.Draw, nP (a ++ b) = nP a + nP b
  | [], b => (Nat.zero_add _).symm
  | .elem :: a, b => nP_append a b
  | .elemNZ :: a, b => nP_append a b
  | .pos _ :: a, b => by
      show nP (a ++ b) + 1 = nP a + 1 + nP b
      rw [nP_append a b, Nat.add_right_comm]
  | .trits _ :: a, b => nP_append a b
  | .sealed :: a, b => nP_append a b

/-- A list of n draws of a position has n positions. -/
theorem nP_replicate_pos (k : ℕ) : ∀ n, nP (List.replicate n (Fmt.Draw.pos k)) = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (nP_replicate_pos k n)

/-- A list in which no position occurs has none. -/
theorem nP_of_mem (ds : List Fmt.Draw) (hp : ∀ k, Fmt.Draw.pos k ∉ ds) : nP ds = 0 := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      have hr : nP ds = 0 := ih fun k h => hp k (List.mem_cons_of_mem d h)
      cases d with
      | elem => exact hr
      | elemNZ => exact hr
      | pos k => exact (hp k List.mem_cons_self).elim
      | trits _ => exact hr
      | sealed => exact hr

/-- The draws of a round's elements have no position. -/
theorem nP_dsElems (e : Fmt.Entry) (k : Fmt.Kind) : nP (Fmt.dsElems e k) = 0 := by
  refine nP_of_mem _ fun k' h => ?_
  rcases mem_dsElems e k _ h with h | h
  · cases h
  · cases h

/-- The end of a round's list has no position. -/
theorem nP_tail (n : ℕ) (k : Fmt.Kind) :
    nP (Fmt.Draw.trits n :: (if k = .sealed then [Fmt.Draw.sealed] else [])) = 0 := by
  by_cases hk : k = .sealed
  · rw [if_pos hk]
    rfl
  · rw [if_neg hk]
    rfl

/-- The number of positions of a round is the entry's. -/
theorem nP_dsOf (e : Fmt.Entry) (k : Fmt.Kind) : nP (Fmt.dsOf e k) = e.poss := by
  unfold Fmt.dsOf
  rw [nP_append, nP_append, nP_replicate_pos, nP_dsElems, nP_tail]
  rfl

/-! ## The number of elements -/

/-- The elements of two lists, joined, are counted list by list. -/
theorem nE_append : ∀ a b : List Fmt.Draw, nE (a ++ b) = nE a + nE b
  | [], b => (Nat.zero_add _).symm
  | .elem :: a, b => by
      show nE (a ++ b) + 1 = nE a + 1 + nE b
      rw [nE_append a b, Nat.add_right_comm]
  | .elemNZ :: a, b => by
      show nE (a ++ b) + 1 = nE a + 1 + nE b
      rw [nE_append a b, Nat.add_right_comm]
  | .pos _ :: a, b => nE_append a b
  | .trits _ :: a, b => nE_append a b
  | .sealed :: a, b => nE_append a b

/-- A list of draws of positions has no element. -/
theorem nE_replicate_pos (k : ℕ) : ∀ n, nE (List.replicate n (Fmt.Draw.pos k)) = 0
  | 0 => rfl
  | n + 1 => nE_replicate_pos k n

/-- A list of n draws of an element has n elements. -/
theorem nE_replicate_elem : ∀ n, nE (List.replicate n Fmt.Draw.elem) = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (nE_replicate_elem n)

/-- A list of n draws of an element other than 0 has n elements. -/
theorem nE_replicate_elemNZ : ∀ n, nE (List.replicate n Fmt.Draw.elemNZ) = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (nE_replicate_elemNZ n)

/-- The end of a round's list has no element. -/
theorem nE_tail (n : ℕ) (k : Fmt.Kind) :
    nE (Fmt.Draw.trits n :: (if k = .sealed then [Fmt.Draw.sealed] else [])) = 0 := by
  by_cases hk : k = .sealed
  · rw [if_pos hk]
    rfl
  · rw [if_neg hk]
    rfl

/-- The elements of a round are those of its middle part. -/
theorem nE_dsOf_eq (e : Fmt.Entry) (k : Fmt.Kind) : nE (Fmt.dsOf e k) = nE (Fmt.dsElems e k) := by
  unfold Fmt.dsOf
  rw [nE_append, nE_append, nE_replicate_pos, nE_tail, Nat.zero_add, Nat.add_zero]

/-- One seed of v coordinates, as the format lists it. -/
theorem dsSeeds_one (v : ℕ) :
    Fmt.dsSeeds 1 v = (List.replicate v Fmt.Draw.elem ++ [Fmt.Draw.elemNZ]) ++ [] := rfl

/-- The elements of a round of one seed, as the format lists them. -/
theorem dsElems_seed (e : Fmt.Entry) (h1 : e.drawNZ = 1) :
    Fmt.dsElems e .seeds =
      Fmt.dsSeeds 1 (e.drawE - 1) ++ List.replicate 0 Fmt.Draw.elem := by
  unfold Fmt.dsElems
  rw [if_pos rfl, h1, Nat.div_one, Nat.mod_one]

/-- The number of elements of a round is the entry's, in a round that is not one of seeds. -/
theorem nE_dsOf (e : Fmt.Entry) (k : Fmt.Kind) (h : e.drawNZ ≤ e.drawE) (hk : k ≠ .seeds) :
    nE (Fmt.dsOf e k) = e.drawE := by
  rw [nE_dsOf_eq]
  unfold Fmt.dsElems
  rw [if_neg hk, nE_append, nE_replicate_elem, nE_replicate_elemNZ]
  exact Nat.sub_add_cancel h

/-- The number of elements of a round of one seed is the entry's. -/
theorem nE_dsOf_seed (e : Fmt.Entry) (h1 : e.drawNZ = 1) (h : 1 ≤ e.drawE) :
    nE (Fmt.dsOf e .seeds) = e.drawE := by
  rw [nE_dsOf_eq, dsElems_seed e h1, dsSeeds_one, nE_append, nE_append, nE_append,
    nE_replicate_elem, nE_replicate_elem]
  show e.drawE - 1 + 1 + 0 + 0 = e.drawE
  exact Nat.sub_add_cancel h

/-! ## The element that is drawn other than 0 -/

/-- What holds of the element number i of a list holds of it in a longer list. -/
theorem isNZ_append : ∀ (a b : List Fmt.Draw) (i : ℕ), IsNZ a i → IsNZ (a ++ b) i
  | [], _, _, h => h.elim
  | .elem :: _, _, 0, h => h.elim
  | .elem :: a, b, i + 1, h => isNZ_append a b i h
  | .elemNZ :: _, _, 0, _ => trivial
  | .elemNZ :: a, b, i + 1, h => isNZ_append a b i h
  | .pos _ :: a, b, i, h => isNZ_append a b i h
  | .trits _ :: a, b, i, h => isNZ_append a b i h
  | .sealed :: a, b, i, h => isNZ_append a b i h

/-- Positions in front do not count. -/
theorem isNZ_replicate_pos (k : ℕ) (ds : List Fmt.Draw) (i : ℕ) (h : IsNZ ds i) :
    ∀ n, IsNZ (List.replicate n (Fmt.Draw.pos k) ++ ds) i
  | 0 => h
  | n + 1 => isNZ_replicate_pos k ds i h n

/-- In a seed of v coordinates the element number v is the factor, drawn other than 0. -/
theorem isNZ_seed : ∀ v, IsNZ (List.replicate v Fmt.Draw.elem ++ [Fmt.Draw.elemNZ]) v
  | 0 => trivial
  | v + 1 => isNZ_seed v

/-- In a round of one seed the element number `drawE - 1` is drawn other than 0. If `drawE` is at
least 1, that is the last element (`nE_dsOf_seed`). -/
theorem isNZ_dsOf_seed (e : Fmt.Entry) (h1 : e.drawNZ = 1) :
    IsNZ (Fmt.dsOf e .seeds) (e.drawE - 1) := by
  have hs : IsNZ (Fmt.dsSeeds 1 (e.drawE - 1)) (e.drawE - 1) := by
    rw [dsSeeds_one]
    exact isNZ_append _ _ _ (isNZ_seed _)
  have he : IsNZ (Fmt.dsElems e .seeds) (e.drawE - 1) := by
    rw [dsElems_seed e h1]
    exact isNZ_append _ _ _ hs
  unfold Fmt.dsOf
  exact isNZ_replicate_pos _ _ _ (isNZ_append _ _ _ he) _

end OnBytes.Slice

#print axioms OnBytes.Slice.plain_dsOf
#print axioms OnBytes.Slice.nP_dsOf
#print axioms OnBytes.Slice.allPos_dsOf
#print axioms OnBytes.Slice.nE_dsOf
#print axioms OnBytes.Slice.nE_dsOf_seed
#print axioms OnBytes.Slice.isNZ_dsOf_seed
