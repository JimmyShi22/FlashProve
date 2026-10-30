-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinTree.lean: the tree of the committer that runs is the library's pure tree over
lists.

The committer (Johnson/Bind/Twin.lean) builds its hash tree on arrays: all leaves, then depth by
depth (`leavesFromW`, `upFromW`, `climbW`, `rootW`). The library's trees over lists are
`Compile.levelsM` and `Compile.rootOf` (Compile/MerkleM.lean), with the pure forms `Compile.pairUpF`
and `Compile.levelsF` (Compile/MerkleList.lean). At the identity monad, at every hash h and every
shape:
   `rootW_id`: the committer's root is `Compile.rootOf` of `Compile.levelsF`, a steps, over the list
      of the 2^a leaves' values, with h's vertex as the node function.
Beside it, for trees whose values have two types (bytes and digests):
   `rootOf_levelsF_map`: a map f that commutes with the node functions commutes with the root, over
      a list that is not empty.
Limits. Bookkeeping between two texts of one tree. Nothing on collisions or on what a root fixes.

-/
import Johnson.Bind.Twin
import Compile.MerkleList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin

open Compile (pairUpF levelsF rootOf)

/-! ### Lists -/

section
variable {D : Type} [Inhabited D] (hN : D → D → D)

/-- n values of the next depth, read off a list two by two. -/
def ups : Nat → List D → List D
  | 0, _ => []
  | n + 1, l => hN (l.getD 0 default) (l.getD 1 default) :: ups n (l.drop 2)

theorem ups_eq_pairUpF : ∀ (n : Nat) (l : List D), l.length = 2 * n → ups hN n l = pairUpF hN l
  | 0, [], _ => rfl
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], h => by simp at h
  | n + 1, [_], h => by simp at h; omega
  | n + 1, a :: b :: t, h => by
    rw [Compile.pairUpF_cons₂, ← ups_eq_pairUpF n t (by simp only [List.length_cons] at h; omega)]
    rfl

theorem rootOf_levelsF_succ (d : Nat) (l : List D) :
    rootOf (levelsF hN (d + 1) l) = rootOf (levelsF hN d (pairUpF hN l)) := by
  obtain ⟨ls, hls⟩ := Compile.exists_levelsF_eq_cons hN d (pairUpF hN l)
  rw [Compile.levelsF_succ, hls, Compile.rootOf_cons₂]

omit [Inhabited D] in
theorem pairUpF_ne_nil : ∀ l : List D, l ≠ [] → pairUpF hN l ≠ []
  | [], h => absurd rfl h
  | [_], _ => List.cons_ne_nil _ _
  | _ :: _ :: _, _ => List.cons_ne_nil _ _

end

theorem getD_drop {D : Type} (l : List D) (i j : Nat) (d : D) :
    (l.drop i).getD j d = l.getD (i + j) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_toList {D : Type} (A : Array D) (i : Nat) (d : D) :
    A.getD i d = A.toList.getD i d := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-! ### The committer's loops at the identity monad -/

section
variable (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)

/-- The value of the leaf at x. -/
def leafId (S : Shape) (start : Nat → ByteArray) (col : Nat → List UInt64) (salt : Nat → ByteArray)
    (x : Nat) : ByteArray :=
  Id.run (leafAtW h S (start x) (col x) (salt x) x)

/-- The value of a vertex from its children's. -/
def vertexId (cfg l r : ByteArray) : ByteArray := Id.run (Fmt.vertexW h cfg l r)

theorem toList_leavesFromW (S : Shape) (start : Nat → ByteArray) (col : Nat → List UInt64)
    (salt : Nat → ByteArray) :
    ∀ (n x : Nat) (acc : Array ByteArray),
      (Id.run (leavesFromW h S start col salt n x acc)).toList =
        acc.toList ++ (List.range' x n).map (leafId h S start col salt)
  | 0, _, acc => by
    show acc.toList = acc.toList ++ []
    rw [List.append_nil]
  | n + 1, x, acc => by
    show (Id.run (leavesFromW h S start col salt n (x + 1)
      (acc.push (leafId h S start col salt x)))).toList = _
    rw [toList_leavesFromW S start col salt n (x + 1), Array.toList_push, List.range'_succ,
      List.map_cons, List.append_assoc]
    rfl

theorem toList_upFromW (cfg : ByteArray) (below : Array ByteArray) :
    ∀ (n i : Nat) (acc : Array ByteArray),
      (Id.run (upFromW h cfg below n i acc)).toList =
        acc.toList ++ ups (vertexId h cfg) n (below.toList.drop (2 * i))
  | 0, _, acc => by
    show acc.toList = acc.toList ++ []
    rw [List.append_nil]
  | n + 1, i, acc => by
    show (Id.run (upFromW h cfg below n (i + 1) (acc.push (vertexId h cfg
      (below.getD (2 * i) ByteArray.empty) (below.getD (2 * i + 1) ByteArray.empty))))).toList = _
    rw [toList_upFromW cfg below n (i + 1), Array.toList_push, List.append_assoc]
    refine congrArg _ ?_
    show _ :: _ = vertexId h cfg _ _ :: ups (vertexId h cfg) n ((below.toList.drop (2 * i)).drop 2)
    rw [getD_drop, getD_drop, List.drop_drop, getD_toList, getD_toList]
    rfl

theorem climbW_id (cfg : ByteArray) :
    ∀ (d : Nat) (now : Array ByteArray), now.size = 2 ^ d →
      Id.run (climbW h cfg d now) = rootOf (levelsF (vertexId h cfg) d now.toList)
  | 0, now, _ => by
    show now.getD 0 ByteArray.empty = rootOf [now.toList]
    rw [getD_toList]
    generalize now.toList = l
    cases l <;> rfl
  | d + 1, now, hs => by
    have hl : now.toList.length = 2 * 2 ^ d := by
      rw [Array.length_toList, hs, Nat.pow_succ, Nat.mul_comm]
    have hu : (Id.run (upFromW h cfg now (2 ^ d) 0 #[])).toList =
        pairUpF (vertexId h cfg) now.toList := by
      rw [toList_upFromW, ← ups_eq_pairUpF _ _ _ hl]
      rfl
    have hsz : (Id.run (upFromW h cfg now (2 ^ d) 0 #[])).size = 2 ^ d := by
      rw [← Array.length_toList, hu, Compile.length_pairUpF _ _ _ hl]
    show Id.run (climbW h cfg d (Id.run (upFromW h cfg now (2 ^ d) 0 #[]))) = _
    rw [climbW_id cfg d _ hsz, hu, rootOf_levelsF_succ]

/-- **The committer's root is the root of the library's pure tree over the list of its leaves.** -/
theorem rootW_id (S : Shape) (cfg : ByteArray) (start : Nat → ByteArray) (col : Nat → List UInt64)
    (salt : Nat → ByteArray) :
    Id.run (rootW h S cfg start col salt) =
      rootOf (levelsF (vertexId h cfg) S.a
        ((List.range (2 ^ S.a)).map (leafId h S start col salt))) := by
  have hl : (Id.run (leavesFromW h S start col salt (2 ^ S.a) 0 #[])).toList =
      (List.range (2 ^ S.a)).map (leafId h S start col salt) := by
    rw [toList_leavesFromW, List.range_eq_range']
    rfl
  have hs : (Id.run (leavesFromW h S start col salt (2 ^ S.a) 0 #[])).size = 2 ^ S.a := by
    rw [← Array.length_toList, hl, List.length_map, List.length_range]
  show Id.run (climbW h cfg S.a (Id.run (leavesFromW h S start col salt (2 ^ S.a) 0 #[]))) = _
  rw [climbW_id h cfg S.a _ hs, hl]

end

/-! ### Two types of values -/

section
variable {D D' : Type} [Inhabited D] [Inhabited D'] (hN : D → D → D) (hN' : D' → D' → D')
  (f : D → D') (hf : ∀ a b, f (hN a b) = hN' (f a) (f b))
include hf

omit [Inhabited D] [Inhabited D'] in
theorem pairUpF_map : ∀ l : List D, pairUpF hN' (l.map f) = (pairUpF hN l).map f
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
    rw [List.map_cons, List.map_cons, Compile.pairUpF_cons₂, Compile.pairUpF_cons₂, List.map_cons,
      hf, pairUpF_map t]

omit [Inhabited D] [Inhabited D'] in
theorem levelsF_map : ∀ (d : Nat) (l : List D),
    levelsF hN' d (l.map f) = (levelsF hN d l).map (List.map f)
  | 0, _ => rfl
  | d + 1, l => by
    rw [Compile.levelsF_succ, Compile.levelsF_succ, List.map_cons, pairUpF_map hN hN' f hf,
      levelsF_map d]

/-- **A map that commutes with the node functions commutes with the root**, over a list that is not
empty. The premise asks that f commutes at ALL values. From digests to byte strings that can be met;
from byte strings to digests it cannot, since a string need not have 32 bytes. -/
theorem rootOf_levelsF_map : ∀ (d : Nat) (l : List D), l ≠ [] →
    rootOf (levelsF hN' d (l.map f)) = f (rootOf (levelsF hN d l))
  | 0, [], h => absurd rfl h
  | 0, _ :: _, _ => rfl
  | d + 1, l, h => by
    rw [rootOf_levelsF_succ, rootOf_levelsF_succ, pairUpF_map hN hN' f hf,
      rootOf_levelsF_map d _ (pairUpF_ne_nil hN l h)]

end

end Bind.Twin

#print axioms Bind.Twin.ups_eq_pairUpF
#print axioms Bind.Twin.rootOf_levelsF_succ
#print axioms Bind.Twin.pairUpF_ne_nil
#print axioms Bind.Twin.getD_drop
#print axioms Bind.Twin.getD_toList
#print axioms Bind.Twin.toList_leavesFromW
#print axioms Bind.Twin.toList_upFromW
#print axioms Bind.Twin.climbW_id
#print axioms Bind.Twin.rootW_id
#print axioms Bind.Twin.pairUpF_map
#print axioms Bind.Twin.levelsF_map
#print axioms Bind.Twin.rootOf_levelsF_map
