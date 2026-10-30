-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/TreesFew.lean: a prover's message whose oracle messages lie in at most two
classes of leaves, the main rows of one class having one length, has at most two trees.

The rule that places the oracle messages of one prover's message in trees (layTrees,
OnBytes/Iop/Ground.lean) opens a new tree only where no tree fits: for a message with main rows a
tree fits if it has the message's class of leaves and the length of the message's main rows; for a
message without main rows a tree fits if it has the class. Where the planner sends oracle messages
by planSend at a number from treesOf (OnBytes/Params/DeriveLin.lean), it writes the number of these
trees into a round's entry as its number of roots.

Main names.
  LayInv: the trees' classes are a or b, and no two trees have one class.
  laidOf_two: so the passes open at most two trees, if each message's class is a or b and the main
    rows of one class have one length.
  layTrees_two, treesOf_two: the same for layTrees and for treesOf.

The two passes under names (layStep, layPass, laidOf) and layTrees_size: LayPasses.lean.

What this file does not claim. That layTrees returns. Nothing on what lies in a tree.

The program does not import this file.


-/
import OnBytes.Params.DeriveLin
import OnBytes.Params.Fit.LayPasses

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params
open OnBytes

/-- An entry of an array to which a member was added. -/
theorem getD_push {α : Type} (A : Array α) (x d : α) (t : Nat) :
    (A.push x).getD t d = if t = A.size then x else A.getD t d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split <;> rfl

/-- The trees' classes are a or b, and no two trees have one class. -/
structure LayInv (a b : Nat) (s : Array TreeShape × Array Nat × Array Nat) : Prop where
  sz : s.2.1.size = s.1.size
  cl : ∀ t, t < s.1.size → s.2.1.getD t noId = a ∨ s.2.1.getD t noId = b
  inj : ∀ t u, t < s.1.size → u < s.1.size → s.2.1.getD t noId = s.2.1.getD u noId → t = u

/-- Adding a tree of a class that no tree has. -/
theorem LayInv.push {a b : Nat} {s : Array TreeShape × Array Nat × Array Nat} (I : LayInv a b s)
    (x : TreeShape) (c : Nat) (w : Array Nat) (hc : c = a ∨ c = b)
    (hn : ∀ t, t < s.1.size → s.2.1.getD t noId ≠ c) :
    LayInv a b (s.1.push x, s.2.1.push c, w) := by
  refine ⟨?_, fun t ht => ?_, fun t u ht hu e => ?_⟩
  · show (s.2.1.push c).size = (s.1.push x).size
    rw [Array.size_push, Array.size_push, I.sz]
  · have ht' : t < s.1.size + 1 := by simpa [Array.size_push] using ht
    show (s.2.1.push c).getD t noId = a ∨ (s.2.1.push c).getD t noId = b
    rw [getD_push, I.sz]
    split
    · exact hc
    · exact I.cl t (by omega)
  · have ht' : t < s.1.size + 1 := by simpa [Array.size_push] using ht
    have hu' : u < s.1.size + 1 := by simpa [Array.size_push] using hu
    have e' : (s.2.1.push c).getD t noId = (s.2.1.push c).getD u noId := e
    rw [getD_push, getD_push, I.sz] at e'
    by_cases h1 : t = s.1.size
    · by_cases h2 : u = s.1.size
      · omega
      · rw [if_pos h1, if_neg h2] at e'
        exact absurd e'.symm (hn u (by omega))
    · by_cases h2 : u = s.1.size
      · rw [if_neg h1, if_pos h2] at e'
        exact absurd e' (hn t (by omega))
      · rw [if_neg h1, if_neg h2] at e'
        exact I.inj t u (by omega) (by omega) e'

/-- With the invariant there are at most two trees. -/
theorem LayInv.two {a b : Nat} {s : Array TreeShape × Array Nat × Array Nat}
    (I : LayInv a b s) : s.1.size ≤ 2 := by
  refine Nat.le_of_not_lt fun h3 => ?_
  have i01 := I.inj 0 1 (by omega) (by omega)
  have i02 := I.inj 0 2 (by omega) (by omega)
  have i12 := I.inj 1 2 (by omega) (by omega)
  rcases I.cl 0 (by omega) with e0 | e0 <;> rcases I.cl 1 (by omega) with e1 | e1 <;>
    rcases I.cl 2 (by omega) with e2 | e2
  · exact absurd (i01 (e0.trans e1.symm)) (by omega)
  · exact absurd (i01 (e0.trans e1.symm)) (by omega)
  · exact absurd (i02 (e0.trans e2.symm)) (by omega)
  · exact absurd (i12 (e1.trans e2.symm)) (by omega)
  · exact absurd (i12 (e1.trans e2.symm)) (by omega)
  · exact absurd (i02 (e0.trans e2.symm)) (by omega)
  · exact absurd (i01 (e0.trans e1.symm)) (by omega)
  · exact absurd (i01 (e0.trans e1.symm)) (by omega)

/-- A property that each step of List.foldl keeps at the list's members. -/
theorem foldl_keeps_mem {α β : Type} {Pr : β → Prop} (step : β → α → β) :
    ∀ (l : List α) (b : β), (∀ a ∈ l, ∀ b, Pr b → Pr (step b a)) → Pr b →
      Pr (l.foldl step b)
  | [], _, _, hb => hb
  | a :: l, b, h, hb =>
    foldl_keeps_mem step l (step b a) (fun x hx => h x (List.mem_cons_of_mem _ hx))
      (h a List.mem_cons_self b hb)

section Passes

variable {codes : Codes} {sent : Array OracleNotice} {a b : Nat} {Lof : Nat → Nat}

/-- In the first pass each tree has the length that belongs to its class. -/
def LayLen (Lof : Nat → Nat) (s : Array TreeShape × Array Nat × Array Nat) : Prop :=
  ∀ t, t < s.1.size → (s.1.getD t {}).logN = Lof (s.2.1.getD t noId)

/-- A step of the first pass. -/
theorem layStep_main {i : Nat}
    (hc : (sent.getD i default).leafClass = a ∨ (sent.getD i default).leafClass = b)
    (hL : (sent.getD i default).shape.mainRows ≠ 0 →
      (codes.base.getD (sent.getD i default).shape.code default).logN =
        Lof (sent.getD i default).leafClass)
    {s : Array TreeShape × Array Nat × Array Nat} (I : LayInv a b s ∧ LayLen Lof s) :
    LayInv a b (layStep codes sent false s i) ∧ LayLen Lof (layStep codes sent false s i) := by
  unfold layStep
  dsimp only
  split
  · exact I
  · rename_i hm
    have hm' : (sent.getD i default).shape.mainRows ≠ 0 := by
      intro e0
      rw [e0] at hm
      simp at hm
    split
    · exact ⟨⟨I.1.sz, I.1.cl, I.1.inj⟩, I.2⟩
    · rename_i hnone
      have hn : ∀ t, t < s.1.size → s.2.1.getD t noId ≠ (sent.getD i default).leafClass := by
        intro t ht e
        have q := List.find?_eq_none.1 hnone t (List.mem_range.2 ht)
        apply q
        simp only [Bool.false_or, Bool.and_eq_true, beq_iff_eq]
        exact ⟨e, by rw [I.2 t ht, e, hL hm']⟩
      refine ⟨I.1.push _ _ _ hc hn, fun t ht => ?_⟩
      have ht' : t < s.1.size + 1 := by simpa [Array.size_push] using ht
      show ((s.1.push _).getD t {}).logN = Lof ((s.2.1.push _).getD t noId)
      rw [getD_push, getD_push, I.1.sz]
      by_cases h1 : t = s.1.size
      · rw [if_pos h1, if_pos h1]
        simpa using hL hm'
      · rw [if_neg h1, if_neg h1]
        exact I.2 t (by omega)

/-- A step of the second pass. -/
theorem layStep_mask {i : Nat}
    (hc : (sent.getD i default).leafClass = a ∨ (sent.getD i default).leafClass = b)
    {s : Array TreeShape × Array Nat × Array Nat} (I : LayInv a b s) :
    LayInv a b (layStep codes sent true s i) := by
  unfold layStep
  dsimp only
  split
  · exact I
  · split
    · exact ⟨I.sz, I.cl, I.inj⟩
    · rename_i hnone
      refine I.push _ _ _ hc fun t ht e => ?_
      have q := List.find?_eq_none.1 hnone t (List.mem_range.2 ht)
      apply q
      simp only [Bool.true_or, Bool.and_true, beq_iff_eq]
      exact e

/-- The two passes open at most two trees. -/
theorem laidOf_two
    (hc : ∀ i, i < sent.size →
      (sent.getD i default).leafClass = a ∨ (sent.getD i default).leafClass = b)
    (hL : ∀ i, i < sent.size → (sent.getD i default).shape.mainRows ≠ 0 →
      (codes.base.getD (sent.getD i default).shape.code default).logN =
        Lof (sent.getD i default).leafClass) :
    (laidOf codes sent).1.size ≤ 2 := by
  have I0 : LayInv a b ((#[], #[], Array.replicate sent.size 0) :
      Array TreeShape × Array Nat × Array Nat) ∧
      LayLen Lof ((#[], #[], Array.replicate sent.size 0) :
        Array TreeShape × Array Nat × Array Nat) :=
    ⟨⟨rfl, fun t ht => absurd ht (Nat.not_lt_zero t),
        fun t _ ht => absurd ht (Nat.not_lt_zero t)⟩,
      fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  have I1 := foldl_keeps_mem
    (Pr := fun s : Array TreeShape × Array Nat × Array Nat => LayInv a b s ∧ LayLen Lof s)
    (layStep codes sent false) (List.range sent.size) _
    (fun i hi s hs =>
      layStep_main (hc i (List.mem_range.1 hi)) (hL i (List.mem_range.1 hi)) hs) I0
  have I2 := foldl_keeps_mem
    (Pr := fun s : Array TreeShape × Array Nat × Array Nat => LayInv a b s)
    (layStep codes sent true) (List.range sent.size) _
    (fun i hi s hs => layStep_mask (hc i (List.mem_range.1 hi)) hs) I1.1
  exact I2.two

/-- A prover's message whose oracle messages lie in at most two classes of leaves, the main rows of
one class having one length, has at most two trees. -/
theorem layTrees_two {T : TreeLay} (h : layTrees codes sent = some T)
    (hc : ∀ i, i < sent.size →
      (sent.getD i default).leafClass = a ∨ (sent.getD i default).leafClass = b)
    (hL : ∀ i, i < sent.size → (sent.getD i default).shape.mainRows ≠ 0 →
      (codes.base.getD (sent.getD i default).shape.code default).logN =
        Lof (sent.getD i default).leafClass) :
    T.shapes.size ≤ 2 := by
  rw [layTrees_size h]
  exact laidOf_two hc hL

/-- The same for the number that the planner writes into a round's entry. -/
theorem treesOf_two {r : Nat} (h : treesOf codes sent = some r)
    (hc : ∀ i, i < sent.size →
      (sent.getD i default).leafClass = a ∨ (sent.getD i default).leafClass = b)
    (hL : ∀ i, i < sent.size → (sent.getD i default).shape.mainRows ≠ 0 →
      (codes.base.getD (sent.getD i default).shape.code default).logN =
        Lof (sent.getD i default).leafClass) :
    r ≤ 2 := by
  unfold treesOf at h
  obtain ⟨T, hT, e⟩ := Option.map_eq_some_iff.mp h
  rw [← e]
  exact layTrees_two hT hc hL

end Passes

end OnBytes.Params
