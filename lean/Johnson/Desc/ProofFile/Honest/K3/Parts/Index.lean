-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/Index.lean: the honest side of the kind "lookup" (K3). At any
number of parts of keys: which stage stands at which number of the row. For every face. Theorems;
the definitions are numbers and lists.

Terms. Honest/K3/GLOSSARY.md ("face", "row", "stage"). The parts of keys are the field parts of a
lookup's face (`Face`, Johnson/Desc/First/Look/K3LookupGeneral.lean).

What is shown.
  `jSplit`, `jJoin`, `jKey`, `jTab`: a stage's number in the row, as a sum.
  `pairsL`, `treesL`, `splitsL`: the row's stretches as lists.
  `stagesP`: the row, stretch by stretch.
  `pairs_get`, `trees_get`: the entry with a given number of one tree's stretch, and of the stretch
    of all trees.
  `atP_shift`, `atP_alpha`, `atP_tie`, `atP_split`, `atP_join`, `atP_key`, `atP_tab`, `atP_last`,
    `atP_leaves`, `atP_zero`, `atP_bits`: (stages f)[number]? = some stage.
  `stagesP_len`: the number of all stages.
Helpers: `pairs_succ`, `len_pairs`, `trees_cons`, `len_trees`, `len_splits`, `splits_get`,
`ties_get`, `get_behind`, `get_front`, `get_cons`.

Hypotheses that remain. Ranges alone.
  `hs`: (in `atP_shift`) the face has a shift. `hj`: (in `atP_tie`) j < planes - 1. `hi`: (in
    `atP_split`) i + 1 is below the number of parts; (in `atP_key`) part i is there, of v bits.
    `hm`: (in `atP_key`) m < v. `hl`: (in `atP_tab`) l < d.
  `h`: (in `atP_last`, `get_behind`, `get_front`, `get_cons`) the list has the stage at the number;
    (in `splits_get`, `ties_get`) the number is in range. `hn`: (in `get_behind`) the length of what
    stands in front.
  In `pairs_get` and `trees_get` the ranges stand without a name, in front of arrows.

Users. Honest/K3/Good/Step.lean, Honest/K3/Law/Keep/StoreStays.lean and Honest/K3/Parts/Walk.lean
import this file.

Limits. No number of rounds stands here: the rounds in front of a stage are counted by the stage's
number alone (`off`, Honest/K3/Law/Walk.lean).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Index

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts

/-! ## The numbers; the stretches -/

def jSplit (f : LFace) (i : Nat) : Nat := oAlpha f + 1 + (f.planes - 1) + i
def jJoin (f : LFace) : Nat := jSplit f (f.parts.length - 1)
def jKey (f : LFace) (i m : Nat) : Nat := jJoin f + 1 + 2 * (f.parts.take i).sum + 2 * m
def jTab (f : LFace) (l : Nat) : Nat := jJoin f + 1 + 2 * f.parts.sum + 2 * l

/-- Levels and the lines behind them, by letters. -/
def pairsL (A B : Nat → Stage) (n : Nat) : List Stage := (List.range n).flatMap fun m => [A m, B m]

/-- The key trees of parts that are numbered from k on. -/
def treesL (l : List Nat) (k : Nat) : List Stage :=
  (l.zipIdx k).flatMap fun x => pairsL (Stage.key x.2) (Stage.keyLine x.2) x.1

def splitsL (n : Nat) : List Stage := (List.range n).map Stage.split

theorem stagesP (f : LFace) :
    stages f = blkA f ++ (Stage.alpha :: (ties (f.planes - 1) ++ (splitsL (f.parts.length - 1) ++
      (Stage.join :: (treesL f.parts 0 ++ (pairsL Stage.tab Stage.tabLine f.d ++
        [Stage.leaves, Stage.zero, Stage.bits])))))) := by
  unfold stages
  simp [blkA, ties, splitsL, treesL, pairsL]

theorem pairs_succ (A B : Nat → Stage) (n : Nat) :
    pairsL A B (n + 1) = pairsL A B n ++ [A n, B n] := by
  simp [pairsL, List.range_succ, List.flatMap_append]

theorem len_pairs (A B : Nat → Stage) : ∀ n, (pairsL A B n).length = 2 * n
  | 0 => rfl
  | n + 1 => by
    rw [pairs_succ, List.length_append, len_pairs A B n]
    simp
    omega

theorem pairs_get (A B : Nat → Stage) : ∀ (n m : Nat), m < n →
    (pairsL A B n)[2 * m]? = some (A m) ∧ (pairsL A B n)[2 * m + 1]? = some (B m)
  | 0, m, h => by omega
  | n + 1, m, h => by
    rw [pairs_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h1 | h1
    · obtain ⟨a, b⟩ := pairs_get A B n m h1
      have hl := len_pairs A B n
      exact ⟨by rw [List.getElem?_append_left (by omega)]; exact a,
        by rw [List.getElem?_append_left (by omega)]; exact b⟩
    · subst h1
      have hl := len_pairs A B m
      constructor
      · rw [List.getElem?_append_right (by omega), hl, Nat.sub_self]
        rfl
      · rw [List.getElem?_append_right (by omega), hl,
          show 2 * m + 1 - 2 * m = 1 by omega]
        rfl

theorem trees_cons (v : Nat) (l : List Nat) (k : Nat) :
    treesL (v :: l) k = pairsL (Stage.key k) (Stage.keyLine k) v ++ treesL l (k + 1) := by
  simp [treesL, List.zipIdx_cons]

theorem len_trees : ∀ (l : List Nat) (k : Nat), (treesL l k).length = 2 * l.sum
  | [], _ => rfl
  | v :: l, k => by
    rw [trees_cons, List.length_append, len_pairs, len_trees l (k + 1), List.sum_cons]
    omega

theorem trees_get : ∀ (l : List Nat) (k i m v : Nat), l[i]? = some v → m < v →
    (treesL l k)[2 * (l.take i).sum + 2 * m]? = some (Stage.key (k + i) m) ∧
      (treesL l k)[2 * (l.take i).sum + 2 * m + 1]? = some (Stage.keyLine (k + i) m)
  | [], _, _, _, _, h, _ => by simp at h
  | w :: l, k, 0, m, v, h, hm => by
    obtain rfl : w = v := by simpa using h
    obtain ⟨a, b⟩ := pairs_get (Stage.key k) (Stage.keyLine k) w m hm
    have hl := len_pairs (Stage.key k) (Stage.keyLine k) w
    rw [trees_cons]
    simp only [List.take_zero, List.sum_nil, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact ⟨by rw [List.getElem?_append_left (by omega)]; exact a,
      by rw [List.getElem?_append_left (by omega)]; exact b⟩
  | w :: l, k, i + 1, m, v, h, hm => by
    have h' : l[i]? = some v := by simpa using h
    obtain ⟨a, b⟩ := trees_get l (k + 1) i m v h' hm
    have hl := len_pairs (Stage.key k) (Stage.keyLine k) w
    rw [trees_cons, List.take_succ_cons, List.sum_cons]
    have e : k + 1 + i = k + (i + 1) := by omega
    rw [e] at a b
    constructor
    · rw [List.getElem?_append_right (by omega), hl,
        show 2 * (w + (l.take i).sum) + 2 * m - 2 * w = 2 * (l.take i).sum + 2 * m by omega]
      exact a
    · rw [List.getElem?_append_right (by omega), hl,
        show 2 * (w + (l.take i).sum) + 2 * m + 1 - 2 * w = 2 * (l.take i).sum + 2 * m + 1 by omega]
      exact b

theorem len_splits (n : Nat) : (splitsL n).length = n := by simp [splitsL]

theorem splits_get {n i : Nat} (h : i < n) : (splitsL n)[i]? = some (Stage.split i) := by
  simp [splitsL, h]

theorem ties_get {n j : Nat} (h : j < n) : (ties n)[j]? = some (Stage.tie j) := by
  simp [ties, h]

/-! ## Which stage stands where -/

/-- An entry of a list behind a list in front. -/
theorem get_behind {pre l : List Stage} {n k : Nat} {s : Stage} (hn : pre.length = n)
    (h : l[k]? = some s) : (pre ++ l)[n + k]? = some s := by
  rw [List.getElem?_append_right (by omega), hn, Nat.add_sub_cancel_left]
  exact h

/-- An entry of a list in front of another. -/
theorem get_front {l post : List Stage} {k : Nat} {s : Stage} (h : l[k]? = some s) :
    (l ++ post)[k]? = some s := by
  have hk : k < l.length := (List.getElem?_eq_some_iff.1 h).1
  rw [List.getElem?_append_left hk]
  exact h

theorem get_cons {a s : Stage} {l : List Stage} {k : Nat} (h : l[k]? = some s) :
    (a :: l)[k + 1]? = some s := by
  simpa using h

variable (f : LFace)

theorem atP_shift (hs : f.shifted = true) : (stages f)[0]? = some Stage.shift := by
  rw [stagesP]
  simp [blkA, hs]

theorem atP_alpha : (stages f)[oAlpha f]? = some Stage.alpha := by
  rw [stagesP]
  exact get_behind (k := 0) (len_blkA f) rfl

theorem atP_tie {j : Nat} (hj : j < f.planes - 1) : (stages f)[iTie f j]? = some (Stage.tie j) := by
  rw [stagesP, show iTie f j = oAlpha f + (j + 1) by unfold iTie; omega]
  exact get_behind (len_blkA f) (get_cons (get_front (ties_get hj)))

theorem atP_split {i : Nat} (hi : i < f.parts.length - 1) :
    (stages f)[jSplit f i]? = some (Stage.split i) := by
  rw [stagesP, show jSplit f i = oAlpha f + ((f.planes - 1 + i) + 1) by unfold jSplit; omega]
  exact get_behind (len_blkA f) (get_cons (get_behind (len_ties _) (get_front (splits_get hi))))

theorem atP_join : (stages f)[jJoin f]? = some Stage.join := by
  rw [stagesP, show jJoin f = oAlpha f + ((f.planes - 1 + (f.parts.length - 1 + 0)) + 1) by
    unfold jJoin jSplit; omega]
  exact get_behind (len_blkA f) (get_cons (get_behind (len_ties _)
    (get_behind (len_splits _) rfl)))

theorem atP_key {i m v : Nat} (hi : f.parts[i]? = some v) (hm : m < v) :
    (stages f)[jKey f i m]? = some (Stage.key i m) ∧
      (stages f)[jKey f i m + 1]? = some (Stage.keyLine i m) := by
  obtain ⟨a, b⟩ := trees_get f.parts 0 i m v hi hm
  rw [Nat.zero_add] at a b
  rw [stagesP]
  constructor
  · rw [show jKey f i m = oAlpha f + ((f.planes - 1 + (f.parts.length - 1 +
      ((2 * (f.parts.take i).sum + 2 * m) + 1))) + 1) by unfold jKey jJoin jSplit; omega]
    exact get_behind (len_blkA f) (get_cons (get_behind (len_ties _)
      (get_behind (len_splits _) (get_cons (get_front a)))))
  · rw [show jKey f i m + 1 = oAlpha f + ((f.planes - 1 + (f.parts.length - 1 +
      ((2 * (f.parts.take i).sum + 2 * m + 1) + 1))) + 1) by unfold jKey jJoin jSplit; omega]
    exact get_behind (len_blkA f) (get_cons (get_behind (len_ties _)
      (get_behind (len_splits _) (get_cons (get_front b)))))

theorem atP_tab {l : Nat} (hl : l < f.d) :
    (stages f)[jTab f l]? = some (Stage.tab l) ∧
      (stages f)[jTab f l + 1]? = some (Stage.tabLine l) := by
  obtain ⟨a, b⟩ := pairs_get Stage.tab Stage.tabLine f.d l hl
  rw [stagesP]
  constructor
  · rw [show jTab f l = oAlpha f + ((f.planes - 1 + (f.parts.length - 1 +
      ((2 * f.parts.sum + 2 * l) + 1))) + 1) by unfold jTab jJoin jSplit; omega]
    exact get_behind (len_blkA f) (get_cons (get_behind (len_ties _)
      (get_behind (len_splits _) (get_cons (get_behind (len_trees _ _) (get_front a))))))
  · rw [show jTab f l + 1 = oAlpha f + ((f.planes - 1 + (f.parts.length - 1 +
      ((2 * f.parts.sum + (2 * l + 1)) + 1))) + 1) by unfold jTab jJoin jSplit; omega]
    exact get_behind (len_blkA f) (get_cons (get_behind (len_ties _)
      (get_behind (len_splits _) (get_cons (get_behind (len_trees _ _) (get_front b))))))

/-- The last three. -/
theorem atP_last {k : Nat} {s : Stage}
    (h : [Stage.leaves, Stage.zero, Stage.bits][k]? = some s) :
    (stages f)[jTab f f.d + k]? = some s := by
  rw [stagesP, show jTab f f.d + k = oAlpha f + ((f.planes - 1 + (f.parts.length - 1 +
    ((2 * f.parts.sum + (2 * f.d + k)) + 1))) + 1) by unfold jTab jJoin jSplit; omega]
  exact get_behind (len_blkA f) (get_cons (get_behind (len_ties _)
    (get_behind (len_splits _) (get_cons (get_behind (len_trees _ _)
      (get_behind (len_pairs _ _ _) h))))))

theorem atP_leaves : (stages f)[jTab f f.d]? = some Stage.leaves := atP_last f (k := 0) rfl
theorem atP_zero : (stages f)[jTab f f.d + 1]? = some Stage.zero := atP_last f (k := 1) rfl
theorem atP_bits : (stages f)[jTab f f.d + 2]? = some Stage.bits := atP_last f (k := 2) rfl

theorem stagesP_len : (stages f).length = jTab f f.d + 3 := by
  rw [stagesP]
  simp only [List.length_append, List.length_cons, List.length_nil, len_blkA, len_ties, len_splits,
    len_trees, len_pairs]
  unfold jTab jJoin jSplit
  omega

#print axioms ProofFile.Honest.K3.Parts.stagesP
#print axioms ProofFile.Honest.K3.Parts.pairs_succ
#print axioms ProofFile.Honest.K3.Parts.len_pairs
#print axioms ProofFile.Honest.K3.Parts.pairs_get
#print axioms ProofFile.Honest.K3.Parts.trees_cons
#print axioms ProofFile.Honest.K3.Parts.len_trees
#print axioms ProofFile.Honest.K3.Parts.trees_get
#print axioms ProofFile.Honest.K3.Parts.len_splits
#print axioms ProofFile.Honest.K3.Parts.splits_get
#print axioms ProofFile.Honest.K3.Parts.ties_get
#print axioms ProofFile.Honest.K3.Parts.get_behind
#print axioms ProofFile.Honest.K3.Parts.get_front
#print axioms ProofFile.Honest.K3.Parts.get_cons
#print axioms ProofFile.Honest.K3.Parts.atP_shift
#print axioms ProofFile.Honest.K3.Parts.atP_alpha
#print axioms ProofFile.Honest.K3.Parts.atP_tie
#print axioms ProofFile.Honest.K3.Parts.atP_split
#print axioms ProofFile.Honest.K3.Parts.atP_join
#print axioms ProofFile.Honest.K3.Parts.atP_key
#print axioms ProofFile.Honest.K3.Parts.atP_tab
#print axioms ProofFile.Honest.K3.Parts.atP_last
#print axioms ProofFile.Honest.K3.Parts.atP_leaves
#print axioms ProofFile.Honest.K3.Parts.atP_zero
#print axioms ProofFile.Honest.K3.Parts.atP_bits
#print axioms ProofFile.Honest.K3.Parts.stagesP_len

end ProofFile.Honest.K3.Parts
