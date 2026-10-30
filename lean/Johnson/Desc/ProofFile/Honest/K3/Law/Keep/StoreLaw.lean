-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Keep/StoreLaw.lean: the fields of a lookup's store
(`Fast.storeOf`, Honest/K3/StoreMake.lean) are the tables that Honest/K3/JobsFast.lean makes
(`Fast.srcOf`), in range. Theorems; the only hypotheses are bounds on numbers.

Terms. Honest/K3/GLOSSARY.md. In this file S stands for `Fast.srcOf f row w theta alpha` and st for
`Fast.storeOf f row w theta alpha`.

What is shown.
  `Fast.lvlsFrom_eq`, `Fast.lvlsUp_size`, `Fast.lvlsUp_getD`, `Fast.lvlsUp_out`: `lvlsUp n L` has
    n + 1 entries; entry j, j ≤ n, is `upN (n - j) L`; beyond n a reader by `getD` finds `#[]`.
  `Fast.getD_mapRange`: entry i of a function laid over `Array.range n`, i < n.
  `Fast.srcOf_keyLvl`: the text of S's `keyLvl`: by `rfl`.
  `Fast.storeOf_part`: st's entry for a part that is there: the levels over S's leaves.
  `Fast.storeOf_key`: at a part i that is there and a level m up to the part's number of bits, st's
    level is `S.keyLvl i m`.
  `Fast.storeOf_tab`: at a level l up to d, st's level is `S.tabLvl l`.
  `Fast.storeOf_bit`, `Fast.storeOf_fac`: st's two tables are S's: by `rfl`.
  `Fast.storeOf_keys_size`, `Fast.storeOf_key_out`, `Fast.storeOf_part_out`, `Fast.storeOf_tab_out`:
    how many parts st holds, and what a reader by `getD` finds out of range: `#[]`.
  `Fast.srcOf_key_out`, `Fast.srcOf_tab_out`: what S makes from the leaves' number on: the leaves.
  `Fast.srcOf_key_leaves_size`, `Fast.srcOf_tab_leaves_size`: how many these are: a power of 2, so
    they are not `#[]`.
  `storeOk_iff`, `storeOk_none`, `storeOk_at`: `StoreOk` at a store says that it is `storeAt`; at
    none it holds; at `storeAt` it holds: so the hypothesis has an instance with a store.
  `storeAt_eq`: `storeAt` written out: by `rfl`.

Hypotheses that remain. Bounds on numbers alone.
  `h`: (in `Fast.lvlsUp_getD`, `Fast.lvlsUp_out`, `Fast.getD_mapRange`) j ≤ n; n < j; i < n.
  `hi`: part i is there (in `Fast.storeOf_part`, `Fast.storeOf_key`, `Fast.storeOf_key_out`), or is
    not (in `Fast.storeOf_part_out`).
  `hm`, `hl`: the level is in range (m up to the part's number of bits, in `Fast.storeOf_key`; l up
    to d, in `Fast.storeOf_tab`), or beyond it (in `Fast.storeOf_key_out`, `Fast.storeOf_tab_out`),
    or from the leaves' number on (in `Fast.srcOf_key_out`, `Fast.srcOf_tab_out`: ≤, not <).

Imported. Honest/K3/StoreMake.lean, and through it what that file's head names.

Users. Honest/K3/Law/Keep/StoreStays.lean, Honest/K3/Law/Keep/StoreGives.lean.

Limits. Out of range the store and S differ. At a level beyond a part's number of bits, or beyond d,
S makes the leaves (the difference of the two numbers is 0 among the natural numbers) and the store
has `#[]`; at a part that is not there S makes one leaf, alpha less the input's key at that part's
number, and the store has `#[]`. So the equations between the two are stated in range alone. On
arrays alone: nothing is said on what the tables hold.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.StoreMake

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E addE subE mulE oneE)

namespace Fast

/-! ## 1 The levels -/

/-- What `lvlsFrom` gathers: the level n above a, ..., a itself, in front of what it was given. -/
theorem lvlsFrom_eq : ∀ (n : Nat) (a : Array E) (acc : List (Array E)),
    lvlsFrom n a acc = ((List.range (n + 1)).map fun j => upN (n - j) a) ++ acc
  | 0, _, _ => rfl
  | n + 1, a, acc => by
    have hr : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := List.range_succ
    have hm : ((List.range (n + 1)).map fun j => upN (n + 1 - j) a) =
        (List.range (n + 1)).map fun j => upN (n - j) (up a) := by
      apply List.map_congr_left
      intro j hj
      have hj' : j < n + 1 := List.mem_range.1 hj
      have e : n + 1 - j = (n - j) + 1 := by omega
      rw [e]
      rfl
    have hz : upN (n + 1 - (n + 1)) a = a := by
      rw [Nat.sub_self]
      rfl
    show lvlsFrom n (up a) (a :: acc) = _
    rw [lvlsFrom_eq n (up a) (a :: acc), hr, List.map_append, hm, List.map_cons, List.map_nil, hz,
      List.append_assoc]
    rfl

/-- n + 1 entries. -/
theorem lvlsUp_size (n : Nat) (L : Array E) : (lvlsUp n L).size = n + 1 := by
  simp [lvlsUp, lvlsFrom_eq]

/-- **Entry j is the level n - j above the leaves.** -/
theorem lvlsUp_getD (n j : Nat) (L : Array E) (h : j ≤ n) :
    (lvlsUp n L).getD j #[] = upN (n - j) L := by
  have hj : j < n + 1 := by omega
  unfold lvlsUp
  rw [lvlsFrom_eq, List.append_nil, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map, List.getElem?_range hj]
  rfl

/-- Beyond the leaves there is no entry. -/
theorem lvlsUp_out (n j : Nat) (L : Array E) (h : n < j) : (lvlsUp n L).getD j #[] = #[] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [lvlsUp_size]; omega)]
  rfl

/-- Entry i of a function laid over the numbers below n. -/
theorem getD_mapRange {α : Type} (n i : Nat) (g : Nat → α) (d : α) (h : i < n) :
    ((Array.range n).map g).getD i d = g i := by
  have hs : i < ((Array.range n).map g).size := by
    rw [Array.size_map, Array.size_range]
    exact h
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs]
  simp only [Array.getElem_map, Array.getElem_range, Option.getD_some]

/-! ## 2 The store's fields, in range -/

/-- The text of `keyLvl`. -/
theorem srcOf_keyLvl (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E) (i m : Nat) :
    (srcOf f row w theta alpha).keyLvl i m =
      upN (f.parts.getD i 0 - m)
        ((Array.range (2 ^ f.parts.getD i 0)).map fun x => subE alpha (w.key theta i x)) := rfl

/-- The store's entry for a part that is there. -/
theorem storeOf_part (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E) (i : Nat)
    (hi : i < f.parts.length) :
    (storeOf f row w theta alpha).keyLvls.getD i #[] =
      lvlsUp (f.parts.getD i 0) ((srcOf f row w theta alpha).keyLvl i (f.parts.getD i 0)) :=
  getD_mapRange f.parts.length i
    (fun i => lvlsUp (f.parts.getD i 0) ((srcOf f row w theta alpha).keyLvl i (f.parts.getD i 0)))
    #[] hi

/-- **The key side**: at a part that is there, up to the part's number of bits. -/
theorem storeOf_key (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E) (i m : Nat)
    (hi : i < f.parts.length) (hm : m ≤ f.parts.getD i 0) :
    ((storeOf f row w theta alpha).keyLvls.getD i #[]).getD m #[] =
      (srcOf f row w theta alpha).keyLvl i m := by
  rw [storeOf_part f row w theta alpha i hi, lvlsUp_getD _ _ _ hm]
  simp only [srcOf_keyLvl, Nat.sub_self, upN]

/-- **The table side**: up to d. -/
theorem storeOf_tab (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E) (l : Nat)
    (hl : l ≤ f.d) :
    (storeOf f row w theta alpha).tabLvls.getD l #[] = (srcOf f row w theta alpha).tabLvl l :=
  lvlsUp_getD f.d l _ hl

/-- **The bits.** -/
theorem storeOf_bit (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E) :
    (storeOf f row w theta alpha).bitTab = (srcOf f row w theta alpha).bitTab () := rfl

/-- **The table side's factors.** -/
theorem storeOf_fac (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E) :
    (storeOf f row w theta alpha).facTab = (srcOf f row w theta alpha).facTab () := rfl

/-! ## 3 Out of range -/

/-- As many entries as parts. -/
theorem storeOf_keys_size (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E) :
    (storeOf f row w theta alpha).keyLvls.size = f.parts.length := by
  show ((Array.range f.parts.length).map _).size = _
  rw [Array.size_map, Array.size_range]

/-- At a part that is not there the store has nothing. -/
theorem storeOf_part_out (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E) (i m : Nat)
    (hi : f.parts.length ≤ i) :
    ((storeOf f row w theta alpha).keyLvls.getD i #[]).getD m #[] = #[] := by
  have e : (storeOf f row w theta alpha).keyLvls.getD i #[] = #[] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [storeOf_keys_size]; exact hi)]
    rfl
  rw [e]
  simp [Array.getD_eq_getD_getElem?]

/-- Beyond a part's leaves the store has nothing. -/
theorem storeOf_key_out (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E) (i m : Nat)
    (hi : i < f.parts.length) (hm : f.parts.getD i 0 < m) :
    ((storeOf f row w theta alpha).keyLvls.getD i #[]).getD m #[] = #[] := by
  rw [storeOf_part f row w theta alpha i hi, lvlsUp_out _ _ _ hm]

/-- Beyond the table side's leaves the store has nothing. -/
theorem storeOf_tab_out (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E) (l : Nat)
    (hl : f.d < l) : (storeOf f row w theta alpha).tabLvls.getD l #[] = #[] :=
  lvlsUp_out f.d l _ hl

/-- There `srcOf` makes the part's leaves. -/
theorem srcOf_key_out (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E) (i m : Nat)
    (hm : f.parts.getD i 0 ≤ m) :
    (srcOf f row w theta alpha).keyLvl i m =
      (srcOf f row w theta alpha).keyLvl i (f.parts.getD i 0) := by
  simp only [srcOf_keyLvl, Nat.sub_self, Nat.sub_eq_zero_of_le hm]

/-- And the table side's leaves. -/
theorem srcOf_tab_out (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E) (l : Nat)
    (hl : f.d ≤ l) :
    (srcOf f row w theta alpha).tabLvl l = (srcOf f row w theta alpha).tabLvl f.d := by
  show upN (f.d - l) _ = upN (f.d - f.d) _
  rw [Nat.sub_self, Nat.sub_eq_zero_of_le hl]

/-- A part's leaves are 2 ^ v, so they are not `#[]`. -/
theorem srcOf_key_leaves_size (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E)
    (i : Nat) :
    ((srcOf f row w theta alpha).keyLvl i (f.parts.getD i 0)).size = 2 ^ f.parts.getD i 0 := by
  simp only [srcOf_keyLvl, Nat.sub_self, upN, Array.size_map, Array.size_range]

/-- The table side's leaves are 2 ^ (mu + d). -/
theorem srcOf_tab_leaves_size (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E) :
    ((srcOf f row w theta alpha).tabLvl f.d).size = 2 ^ (f.mu + f.d) := by
  show (upN (f.d - f.d) (Array.zipWith _ ((Array.range _).map _) ((Array.range _).map _))).size = _
  simp only [Nat.sub_self, upN, Array.size_zipWith, Array.size_map, Array.size_range, Nat.min_self]

end Fast

/-! ## 4 `StoreOk` -/

/-- At a store, `StoreOk` says that it is `storeAt`. -/
theorem storeOk_iff (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn)
    (st : Store) : StoreOk R row a w h (some st) ↔ st = storeAt R row a w h :=
  ⟨fun hx => hx st rfl, fun e _ e' => (Option.some.inj e') ▸ e⟩

/-- Where no store is passed on it holds. -/
theorem storeOk_none (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn) :
    StoreOk R row a w h none := fun _ e => nomatch e

/-- **It holds of the store that `storeAt` makes of the same input and challenges.** -/
theorem storeOk_at (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn) :
    StoreOk R row a w h (some (storeAt R row a w h)) := (storeOk_iff R row a w h _).2 rfl

/-- `storeAt`, written out. -/
theorem storeAt_eq (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn) :
    storeAt R row a w h =
      Fast.storeOf a.face row (w (R.pts a.face a.base h).heard) (R.pts a.face a.base h).theta
        (R.pts a.face a.base h).alpha := rfl

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.Fast.lvlsFrom_eq
#print axioms ProofFile.Honest.K3.Fast.lvlsUp_size
#print axioms ProofFile.Honest.K3.Fast.lvlsUp_getD
#print axioms ProofFile.Honest.K3.Fast.lvlsUp_out
#print axioms ProofFile.Honest.K3.Fast.getD_mapRange
#print axioms ProofFile.Honest.K3.Fast.srcOf_keyLvl
#print axioms ProofFile.Honest.K3.Fast.storeOf_part
#print axioms ProofFile.Honest.K3.Fast.storeOf_key
#print axioms ProofFile.Honest.K3.Fast.storeOf_tab
#print axioms ProofFile.Honest.K3.Fast.storeOf_bit
#print axioms ProofFile.Honest.K3.Fast.storeOf_fac
#print axioms ProofFile.Honest.K3.Fast.storeOf_keys_size
#print axioms ProofFile.Honest.K3.Fast.storeOf_part_out
#print axioms ProofFile.Honest.K3.Fast.storeOf_key_out
#print axioms ProofFile.Honest.K3.Fast.storeOf_tab_out
#print axioms ProofFile.Honest.K3.Fast.srcOf_key_out
#print axioms ProofFile.Honest.K3.Fast.srcOf_tab_out
#print axioms ProofFile.Honest.K3.Fast.srcOf_key_leaves_size
#print axioms ProofFile.Honest.K3.Fast.srcOf_tab_leaves_size
#print axioms ProofFile.Honest.K3.storeOk_iff
#print axioms ProofFile.Honest.K3.storeOk_none
#print axioms ProofFile.Honest.K3.storeOk_at
#print axioms ProofFile.Honest.K3.storeAt_eq
