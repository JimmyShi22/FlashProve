-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/MerkleList.lean: the list programs of Compile/MerkleM.lean and the trees of
Hash/MerklePure.lean.

Compile/MerkleM.lean writes Merkle trees over 2^d leaves as programs on lists: levels of digests,
leaves numbered by natural numbers, paths listed from the leaf upwards. Hash/MerklePure.lean has the
theory (extraction, its stability, that openings agree with it) for trees of any shape, with typed
positions and labellings from the root downwards. This file joins the two, without oracles and
without probability:
  Part 1  posOf d j: leaf number j of the perfect tree of depth d
  Part 2  ClimbsIn: a path from the leaf upwards whose node queries are entries of a trace; with a
          leaf query of the trace, and d siblings, it gives OpensIn
  Part 3  (a) honest openings pass: for pure functions, over 2^d leaf digests and for j < 2^d, the
              path that pathOf reads off the levels climbs to the root;
          (b) for a relation R with `Evaluates M R`: if the node action evaluates to a pure
              function, the list programs in any monad M evaluate to their pure versions
-/
import Compile.MerkleM
import Hash.MerklePure

namespace Compile
open Merkle

/-! ## Part 1. Numbered leaves -/

/-- Leaf number j of the perfect tree of depth d, counted from the left. Only j mod 2^d matters. The
step at the root is bit d - 1 of j, and the bit 0 means "left". -/
def posOf : (d : ℕ) → ℕ → (Shape.perfect d).Pos
  | 0, _ => Shape.Pos.here
  | d + 1, j =>
    if (j / 2 ^ d) % 2 = 0 then Shape.Pos.left (posOf d j) else Shape.Pos.right (posOf d j)

theorem posOf_succ_of_even {d j : ℕ} (h : (j / 2 ^ d) % 2 = 0) :
    posOf (d + 1) j = Shape.Pos.left (posOf d j) := by
  simp only [posOf, if_pos h]

theorem posOf_succ_of_odd {d j : ℕ} (h : ¬ (j / 2 ^ d) % 2 = 0) :
    posOf (d + 1) j = Shape.Pos.right (posOf d j) := by
  simp only [posOf, if_neg h]

/-- posOf d depends on j mod 2^d only. -/
theorem posOf_congr : ∀ (d : ℕ) {j j' : ℕ}, j % 2 ^ d = j' % 2 ^ d → posOf d j = posOf d j'
  | 0, _, _, _ => rfl
  | d + 1, j, j', h => by
      have h1 : j % 2 ^ d = j' % 2 ^ d := by
        have := congrArg (· % 2 ^ d) h
        simpa [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (Nat.le_succ d))] using this
      have h2 : (j / 2 ^ d) % 2 = (j' / 2 ^ d) % 2 := by
        have e : ∀ n : ℕ, (n / 2 ^ d) % 2 = (n % 2 ^ (d + 1)) / 2 ^ d := fun n => by
          rw [pow_succ, Nat.mod_mul_right_div_self]
        rw [e j, e j', h]
      simp only [posOf, h2, posOf_congr d h1]

/-! ## Part 2. Paths from the leaf upwards, within a trace -/

section Trace

variable {E D X : Type} {Ev : Events E D} (V : OraclePair Ev X)

/-- The path climbs from the digest c at index j of some level to the digest r, and all its node
queries are entries of the trace. The path lists siblings from below upwards; at each step the
lowest bit of j says on which side the digest computed so far is (0: left), and j is halved. This is
Compile.climbM with the answers taken from the trace. -/
def ClimbsIn (tr : List E) : List D → ℕ → D → D → Prop
  | [], _, c, r => c = r
  | s :: ss, j, c, r =>
      ∃ u,
        (∃ e ∈ tr, V.node e = some (if j % 2 = 0 then (c, s) else (s, c), u)) ∧
        ClimbsIn tr ss (j / 2) u r

/-- The last step of a path, split off. -/
theorem climbsIn_concat {tr : List E} (s : D) :
    ∀ (ss : List D) (j : ℕ) (c r : D),
      ClimbsIn V tr (ss ++ [s]) j c r ↔
      ∃ u,
        ClimbsIn V tr ss j c u ∧
        ∃ e ∈ tr, V.node e = some (if (j / 2 ^ ss.length) % 2 = 0 then (u, s) else (s, u), r)
  | [], j, c, r => by
      simp only [List.nil_append, ClimbsIn, List.length_nil, pow_zero, Nat.div_one]
      constructor
      · rintro ⟨u, h, rfl⟩; exact ⟨c, rfl, h⟩
      · rintro ⟨u, rfl, h⟩; exact ⟨r, h, rfl⟩
  | s0 :: ss, j, c, r => by
      simp only [List.cons_append, ClimbsIn, List.length_cons, climbsIn_concat s ss (j / 2)]
      have hdiv : j / 2 / 2 ^ ss.length = j / 2 ^ (ss.length + 1) := by
        rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
      rw [hdiv]
      constructor
      · rintro ⟨u, h, u', h', h''⟩; exact ⟨u', ⟨u, h, h'⟩, h''⟩
      · rintro ⟨u', ⟨u, h, h'⟩, h''⟩; exact ⟨u, h, u', h', h''⟩

/-- A leaf query of the trace and a path of d siblings that climbs within the trace open leaf number
j of the perfect tree of depth d. -/
theorem opensIn_of_climbsIn {tr : List E} {x : X} {c : D} {j : ℕ}
    (hx : ∃ e ∈ tr, V.leaf e = some (x, c)) :
    ∀ (d : ℕ) (path : List D) (r : D),
      path.length = d → ClimbsIn V tr path j c r → V.OpensIn tr (posOf d j) x r
  | 0, path, r, hl, h => by
      obtain rfl := List.length_eq_zero_iff.1 hl
      obtain rfl : c = r := h
      exact hx
  | d + 1, path, r, hl, h => by
      rcases List.eq_nil_or_concat' path with rfl | ⟨ss, s, rfl⟩
      · simp at hl
      · have hl' : ss.length = d := by simpa using hl
        obtain ⟨u, hu, hn⟩ := (climbsIn_concat V s ss j c r).1 h
        rw [hl'] at hn
        have ih := opensIn_of_climbsIn hx d ss u hl' hu
        by_cases hb : (j / 2 ^ d) % 2 = 0
        · rw [posOf_succ_of_even hb]
          rw [if_pos hb] at hn
          exact ⟨(u, s), hn, ih⟩
        · rw [posOf_succ_of_odd hb]
          rw [if_neg hb] at hn
          exact ⟨(s, u), hn, ih⟩

end Trace

/-! ## Part 3. Honest openings pass -/

section Pure

variable {D : Type} (hN : D → D → D)

/-- One level up, for a pure node function: Compile.pairUp in the identity monad. -/
def pairUpF (l : List D) : List D := pairUp (M := Id) hN l

/-- All levels, for a pure node function. -/
def levelsF (d : ℕ) (l : List D) : List (List D) := levelsM (M := Id) hN d l

/-- From a digest and a path to a root, for a pure node function. -/
def climbF (path : List D) (j : ℕ) (c : D) : D := climbM (M := Id) hN path j c

theorem pairUpF_cons₂ (a b : D) (t : List D) : pairUpF hN (a :: b :: t) = hN a b :: pairUpF hN t :=
  rfl

theorem levelsF_zero (l : List D) : levelsF hN 0 l = [l] := rfl

theorem levelsF_succ (d : ℕ) (l : List D) :
    levelsF hN (d + 1) l = l :: levelsF hN d (pairUpF hN l) := rfl

theorem climbF_nil (j : ℕ) (c : D) : climbF hN [] j c = c := rfl

theorem climbF_cons (s : D) (ss : List D) (j : ℕ) (c : D) :
    climbF hN (s :: ss) j c = climbF hN ss (j / 2) (if j % 2 = 0 then hN c s else hN s c) := by
  unfold climbF
  by_cases h : j % 2 = 0
  · simp only [climbM, if_pos h]; rfl
  · simp only [climbM, if_neg h]; rfl

theorem length_pairUpF : ∀ (n : ℕ) (l : List D), l.length = 2 * n → (pairUpF hN l).length = n
  | 0, [], _ => rfl
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], h => by simp at h
  | n + 1, [_], h => by simp at h; omega
  | n + 1, a :: b :: t, h => by
      rw [pairUpF_cons₂, List.length_cons,
        length_pairUpF n t (by simp only [List.length_cons] at h; omega)]

theorem exists_levelsF_eq_cons (d : ℕ) (l : List D) : ∃ ls, levelsF hN d l = l :: ls := by
  cases d with
  | zero => exact ⟨[], rfl⟩
  | succ d => exact ⟨_, rfl⟩

variable [Inhabited D]

/-- Entry i of the next level is the hash of the entries 2 i and 2 i + 1, if both exist. -/
theorem getD_pairUpF : ∀ (l : List D) (i : ℕ), 2 * i + 1 < l.length →
    (pairUpF hN l).getD i default = hN (l.getD (2 * i) default) (l.getD (2 * i + 1) default)
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | _ :: _ :: _, 0, _ => rfl
  | a :: b :: t, i + 1, h => by
      have ih := getD_pairUpF t i (by simp only [List.length_cons] at h; omega)
      have e1 : 2 * (i + 1) = 2 * i + 1 + 1 := by omega
      have e2 : 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 := by omega
      rw [pairUpF_cons₂, List.getD_cons_succ, ih, e2, e1, List.getD_cons_succ, List.getD_cons_succ,
        List.getD_cons_succ, List.getD_cons_succ]

theorem rootOf_cons₂ (l l' : List D) (ls : List (List D)) :
    rootOf (l :: l' :: ls) = rootOf (l' :: ls) := by
  simp only [rootOf, List.getLastD_cons]

theorem pathOf_cons₂ (l l' : List D) (ls : List (List D)) (j : ℕ) :
    pathOf (l :: l' :: ls) j =
      l.getD (if j % 2 = 0 then j + 1 else j - 1) default :: pathOf (l' :: ls) (j / 2) := rfl

/-- The path of a leaf in a tree of depth d has d entries. -/
theorem length_pathOf_levelsF :
    ∀ (d : ℕ) (l : List D) (j : ℕ), (pathOf (levelsF hN d l) j).length = d
  | 0, _, _ => rfl
  | d + 1, l, j => by
      obtain ⟨ls, hls⟩ := exists_levelsF_eq_cons hN d (pairUpF hN l)
      have ih := length_pathOf_levelsF d (pairUpF hN l) (j / 2)
      rw [levelsF_succ, hls, pathOf_cons₂, List.length_cons, ← hls, ih]

/-- Honest openings pass. Over 2^d leaf digests, the path that pathOf reads off the levels climbs
from leaf digest number j < 2^d to the root. -/
theorem climbF_pathOf : ∀ (d : ℕ) (l : List D) (j : ℕ), l.length = 2 ^ d → j < 2 ^ d →
    climbF hN (pathOf (levelsF hN d l) j) j (l.getD j default) = rootOf (levelsF hN d l)
  | 0, l, j, hl, hj => by
      have hj0 : j = 0 := by simpa using hj
      subst hj0
      match l, hl with
      | [a], _ => rfl
  | d + 1, l, j, hl, hj => by
      obtain ⟨ls, hls⟩ := exists_levelsF_eq_cons hN d (pairUpF hN l)
      have hl2 : l.length = 2 * 2 ^ d := by rw [hl, pow_succ, Nat.mul_comm]
      have hj2 : j / 2 < 2 ^ d :=
        Nat.div_lt_of_lt_mul (by rw [pow_succ, Nat.mul_comm] at hj; exact hj)
      have ih := climbF_pathOf d (pairUpF hN l) (j / 2) (length_pairUpF hN _ l hl2) hj2
      have hg := getD_pairUpF hN l (j / 2) (by omega)
      have hstep : (if j % 2 = 0 then
              hN (l.getD j default) (l.getD (if j % 2 = 0 then j + 1 else j - 1) default)
            else hN (l.getD (if j % 2 = 0 then j + 1 else j - 1) default) (l.getD j default)) =
          (pairUpF hN l).getD (j / 2) default := by
        rw [hg]
        by_cases hb : j % 2 = 0
        · have e : 2 * (j / 2) = j := by omega
          simp only [if_pos hb, e]
        · have e : 2 * (j / 2) + 1 = j := by omega
          have e' : 2 * (j / 2) = j - 1 := by omega
          rw [if_neg hb, if_neg hb, e, e']
      rw [levelsF_succ, hls, pathOf_cons₂, climbF_cons, hstep, rootOf_cons₂, ← hls, ih]

end Pure

/-- A notion of "the program x evaluates to a" for a monad, closed under pure and bind. Examples: an
oracle algorithm without coins under fixed oracle functions; an oracle algorithm whose queries and
answers are taken from a trace. -/
structure Evaluates (M : Type → Type) [Monad M] (R : {α : Type} → M α → α → Prop) : Prop where
  pure : ∀ {α : Type} (a : α), R (pure a : M α) a
  bind : ∀ {α β : Type} {x : M α} {f : α → M β} {a : α} {b : β}, R x a → R (f a) b → R (x >>= f) b

section Evaluates

variable {D : Type} {M : Type → Type} [Monad M] {R : {α : Type} → M α → α → Prop}
  (hR : Evaluates M R) {qN : D → D → M D} {hN : D → D → D} (hq : ∀ a b, R (qN a b) (hN a b))
include hR hq

/-- For a relation R with `Evaluates M R`: if the action qN evaluates to hN, the list programs
evaluate to their pure versions. -/
theorem Evaluates.pairUp : ∀ l : List D, R (pairUp qN l) (pairUpF hN l)
  | [] => hR.pure _
  | [_] => hR.pure _
  | a :: b :: t => hR.bind (hq a b) (hR.bind (Evaluates.pairUp t) (hR.pure _))

theorem Evaluates.levelsM : ∀ (d : ℕ) (l : List D), R (levelsM qN d l) (levelsF hN d l)
  | 0, _ => hR.pure _
  | d + 1, l => hR.bind (hR.pairUp hq l) (hR.bind (Evaluates.levelsM d _) (hR.pure _))

theorem Evaluates.climbM :
    ∀ (path : List D) (j : ℕ) (c : D), R (climbM qN path j c) (climbF hN path j c)
  | [], _, _ => hR.pure _
  | s :: ss, j, c => by
      rw [climbF_cons]
      by_cases hb : j % 2 = 0
      · simp only [Compile.climbM, if_pos hb]
        exact hR.bind (hq c s) (Evaluates.climbM ss _ _)
      · simp only [Compile.climbM, if_neg hb]
        exact hR.bind (hq s c) (Evaluates.climbM ss _ _)

end Evaluates

end Compile
