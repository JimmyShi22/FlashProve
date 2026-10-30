-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/LaySymbols.lean: **WHAT THE VERIFIER's LAYOUT OF A PROVER's MESSAGE IN TREES
LISTS OF EACH TREE, AND WHICH PART EACH MESSAGE IS** (`layTrees`, OnBytes/Iop/Ground.lean).
Definitions, statements and proofs.

OnBytes/Iop/LayTreesLaws.lean proves two laws on the trees' lengths and says in its head: nothing on
L.part, nothing on the widths that a tree lists. Here are these, over that file's named steps.
Let layTrees cs sent = some L.
  `inTree tree τ k`: the numbers below k of the messages that `tree` lays in the tree τ, in order.
  `mainW sent i`, `maskW sent i`: message i's main rows times their degree; its mask rows times 3.
  `layTrees_symbols`: of each tree τ of L: its `mainSymbols` | `maskSymbols` are, in the order of
    sending, `mainW` | `maskW` of the messages that L.tree lays in τ.
  `layTrees_part`: L.part lists, for each message i, how many earlier messages L.tree lays in i's
    tree: so message i is the entry number L.part i of its tree's lists (`inTree_get`).
  `layTrees_treeSize`: L.tree has an entry for every message.
How. The placing passes open trees without symbols (`laid_bare`). The filling loop pushes message
k's two widths to its tree's lists and notes the list's length before (`fillStep_sym`). The last
touch (`settle`) turns no list.
Limits. Nothing on soundness. Not that layTrees gives a layout. Nothing on which messages share a
tree.

-/
import OnBytes.Iop.LayTreesLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.LayTreesLaws

/-- The numbers below k of the messages that `tree` lays in the tree τ, in order. -/
def inTree (tree : Array Nat) (τ k : Nat) : List Nat :=
  (List.range k).filter fun i => tree.getD i 0 == τ

/-- Message i's main rows times their degree. -/
def mainW (sent : Array OracleNotice) (i : Nat) : Nat :=
  (sent.getD i default).shape.mainRows * (sent.getD i default).shape.mainDeg

/-- Message i's mask rows times 3. -/
def maskW (sent : Array OracleNotice) (i : Nat) : Nat := (sent.getD i default).shape.maskRows * 3

theorem inTree_succ (tree : Array Nat) (τ k : Nat) :
    inTree tree τ (k + 1) = inTree tree τ k ++ if tree.getD k 0 == τ then [k] else [] := by
  unfold inTree
  rw [List.range_succ, List.filter_append]
  simp only [List.filter_cons, List.filter_nil]

/-- Message i stands in its tree's list at the place that counts the earlier ones. -/
theorem inTree_get (tree : Array Nat) (τ i : Nat) (hi : tree.getD i 0 = τ) :
    ∀ n, i < n → (inTree tree τ n)[(inTree tree τ i).length]? = some i
  | 0, h => absurd h (Nat.not_lt_zero i)
  | k + 1, h => by
    rw [inTree_succ]
    rcases Nat.lt_or_ge i k with hk | hk
    · have ih := inTree_get tree τ i hi k hk
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 ih).1]
      exact ih
    · have e : i = k := by omega
      subst e
      rw [if_pos (by rw [beq_iff_eq]; exact hi), List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self]
      rfl

/-! ### The placing passes open trees without symbols -/

/-- A tree lists nothing yet. -/
def Bare (T : TreeShape) : Prop := T.mainSymbols = #[] ∧ T.maskSymbols = #[]

theorem passStep_bare (codes : Codes) (sent : Array OracleNotice) (b : Bool) (s : State) (k : Nat)
    (h : ∀ T ∈ s.1, Bare T) : ∀ T ∈ (passStep codes sent b s k).1, Bare T := by
  simp only [passStep]
  split
  · exact h
  · split
    · exact h
    · intro T hT
      rcases Array.mem_push.1 hT with h1 | rfl
      · exact h T h1
      · split <;> exact ⟨rfl, rfl⟩

theorem laid_bare (codes : Codes) (sent : Array OracleNotice) :
    ∀ T ∈ (laid codes sent).1, Bare T := by
  unfold laid
  refine foldl_range_inv _ (fun _ s => ∀ T ∈ s.1, Bare T) _ _ ?_
    (fun k s _ h => passStep_bare codes sent true s k h)
  refine foldl_range_inv _ (fun _ s => ∀ T ∈ s.1, Bare T) _ _ ?_
    (fun k s _ h => passStep_bare codes sent false s k h)
  intro T hT
  simp at hT

theorem laid_treeSize (codes : Codes) (sent : Array OracleNotice) :
    (laid codes sent).2.2.size = sent.size := by
  unfold laid
  refine foldl_range_inv _ (fun _ (s : State) => s.2.2.size = sent.size) _ _ ?_
    (fun k s _ h => (passStep_size codes sent _ s k).trans h)
  refine foldl_range_inv _ (fun _ (s : State) => s.2.2.size = sent.size) _ _ ?_
    (fun k s _ h => (passStep_size codes sent _ s k).trans h)
  simp

/-! ### The filling loop -/

/-- What holds behind k steps of the filling loop. m: the number of trees. -/
structure SymInv (sent : Array OracleNotice) (tree : Array Nat) (m k : Nat) (s : State) : Prop where
  size : s.1.size = m
  sym : ∀ τ T, s.1[τ]? = some T →
    T.mainSymbols.toList = (inTree tree τ k).map (mainW sent) ∧
      T.maskSymbols.toList = (inTree tree τ k).map (maskW sent)
  part : s.2.1.toList = (List.range k).map fun i => (inTree tree (tree.getD i 0) i).length

theorem fillStep_sym (codes : Codes) (sent : Array OracleNotice) (tree : Array Nat) (m k : Nat)
    (s s' : State) (hk : tree.getD k 0 < m) (hI : SymInv sent tree m k s)
    (hs : fillStep codes sent tree s k = some s') : SymInv sent tree m (k + 1) s' := by
  simp only [fillStep] at hs
  split at hs
  · cases hs
  · cases hs
    refine ⟨by rw [Array.size_modify]; exact hI.size, ?_, ?_⟩
    · intro τ T hT
      rw [Array.getElem?_modify] at hT
      by_cases ht : tree.getD k 0 = τ
      · rw [if_pos ht] at hT
        obtain ⟨T0, hT0, rfl⟩ := Option.map_eq_some_iff.1 hT
        obtain ⟨a, b⟩ := hI.sym τ T0 hT0
        rw [inTree_succ, if_pos (by rw [beq_iff_eq]; exact ht)]
        simp [enter, a, b, mainW, maskW]
      · rw [if_neg ht] at hT
        rw [inTree_succ, if_neg (by rw [beq_iff_eq]; exact ht)]
        simpa using hI.sym τ T hT
    · obtain ⟨T0, hT0⟩ : ∃ T0, s.1[tree.getD k 0]? = some T0 :=
        ⟨_, Array.getElem?_eq_getElem (by rw [hI.size]; exact hk)⟩
      have e : s.1.getD (tree.getD k 0) {} = T0 := by
        rw [Array.getD_eq_getD_getElem?, hT0]
        rfl
      show (s.2.1.push (s.1.getD (tree.getD k 0) {}).mainSymbols.size).toList = _
      rw [e, Array.toList_push, hI.part, List.range_succ, List.map_append, List.map_singleton,
        ← Array.length_toList, (hI.sym _ _ hT0).1, List.length_map]

/-! ### The whole -/

/-- What layTrees, where it gives a layout, lists. -/
theorem layTrees_sym (cs : Codes) (sent : Array OracleNotice) (L : TreeLay)
    (h : layTrees cs sent = some L) :
    (∀ τ T, L.shapes[τ]? = some T →
      T.mainSymbols.toList = (inTree L.tree τ sent.size).map (mainW sent) ∧
        T.maskSymbols.toList = (inTree L.tree τ sent.size).map (maskW sent)) ∧
    L.part.toList =
      (List.range sent.size).map fun i => (inTree L.tree (L.tree.getD i 0) i).length := by
  rw [layTrees_eq] at h
  cases hf : (List.range sent.size).foldlM (fillStep cs sent (laid cs sent).2.2)
      ((laid cs sent).1, #[], Array.replicate (laid cs sent).1.size 0) with
  | none =>
    rw [hf] at h
    cases h
  | some filled =>
    rw [hf, Option.bind_some] at h
    split at h
    · cases h
      have hI : SymInv sent (laid cs sent).2.2 (laid cs sent).1.size sent.size filled :=
        foldlM_range_inv _ (SymInv sent (laid cs sent).2.2 (laid cs sent).1.size) sent.size _
          filled hf
          ⟨rfl, fun τ T hT => by
            obtain ⟨b1, b2⟩ := laid_bare cs sent T (Array.mem_of_getElem? hT)
            rw [b1, b2]
            exact ⟨rfl, rfl⟩, rfl⟩
          (fun k s s' hk hI hs => fillStep_sym cs sent _ _ k s s'
            (by
              obtain ⟨T0, hT0, _⟩ := laid_placed cs sent k hk
              exact (Array.getElem?_eq_some_iff.1 hT0).1) hI hs)
      refine ⟨fun τ T hT => ?_, hI.part⟩
      have hT' : (filled.1.map settle)[τ]? = some T := hT
      rw [Array.getElem?_map] at hT'
      obtain ⟨T0, hT0, rfl⟩ := Option.map_eq_some_iff.1 hT'
      have e1 : (settle T0).mainSymbols = T0.mainSymbols := by
        unfold settle
        split <;> rfl
      have e2 : (settle T0).maskSymbols = T0.maskSymbols := by
        unfold settle
        split <;> rfl
      rw [e1, e2]
      exact hI.sym τ T0 hT0
    · cases h

end OnBytes.LayTreesLaws

namespace OnBytes
open LayTreesLaws

/-- **Each tree lists, in the order of sending, the widths of the messages that are laid in it.** -/
theorem layTrees_symbols (cs : Codes) (sent : Array OracleNotice) (L : TreeLay)
    (h : layTrees cs sent = some L) (τ : Nat) (T : TreeShape) (hT : L.shapes[τ]? = some T) :
    T.mainSymbols.toList = (inTree L.tree τ sent.size).map (mainW sent) ∧
      T.maskSymbols.toList = (inTree L.tree τ sent.size).map (maskW sent) :=
  (layTrees_sym cs sent L h).1 τ T hT

/-- **A message's part is the number of earlier messages in its tree.** -/
theorem layTrees_part (cs : Codes) (sent : Array OracleNotice) (L : TreeLay)
    (h : layTrees cs sent = some L) (i : Nat) (hi : i < sent.size) :
    L.part[i]? = some (inTree L.tree (L.tree.getD i 0) i).length := by
  rw [← Array.getElem?_toList, (layTrees_sym cs sent L h).2, List.getElem?_map,
    List.getElem?_range hi]
  rfl

/-- Every message has an entry in L.tree. -/
theorem layTrees_treeSize (cs : Codes) (sent : Array OracleNotice) (L : TreeLay)
    (h : layTrees cs sent = some L) : L.tree.size = sent.size := by
  rw [layTrees_eq] at h
  obtain ⟨filled, _, h2⟩ := Option.bind_eq_some_iff.1 h
  split at h2
  · cases h2
    exact laid_treeSize cs sent
  · cases h2

end OnBytes

#print axioms OnBytes.layTrees_symbols
#print axioms OnBytes.layTrees_part
#print axioms OnBytes.layTrees_treeSize
#print axioms OnBytes.LayTreesLaws.inTree_get
