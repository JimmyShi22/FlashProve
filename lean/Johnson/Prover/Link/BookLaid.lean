-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BookLaid.lean: THE BOOK OF TREES BEHIND A PROVER's MESSAGE, LOOKED UP: five
general lemmas on the library's treesSent and partsLaid (OnBytes/Slice/BlkSendRun.lean) and on cnt
(Johnson/Desc/Book/BookFits.lean). Over the library alone: a shared file for whoever reads a new
tree.

Main names (namespace Johnson.Prover.Link).
  treesSent_at   a new tree, written out: its shape; number := first + (r + τ); src := .own (r + τ).
  partsLaid_keep   entering parts into trees turns no tree's shape, number and count of lists.
  partsFold_one, partsLaid_one   all of a prover's message's oracle messages entered into its first
      tree: the tree's parts and its mark "opened at one list only", written out.
  cnt_all   where the first k messages all lie in tree 0 there are k of them.

By calls: treesSent_old (OnBytes/Slice/BlkSentSeat.lean).

Limits. Look-ups alone. Nothing on a protocol. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkSentSeat
import Johnson.Desc.Book.BookFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc.Book (cnt)

/-- A new tree, written out. -/
theorem treesSent_at (first : Nat) : ∀ (l : List TreeShape) (r : Nat) (A : Array Tree) (τ : Nat),
    (treesSent first l r A)[A.size + τ]? =
      (l[τ]?).map fun s => { shape := s, number := first + (r + τ), src := .own (r + τ) }
  | [], _, A, τ => by
      show A[A.size + τ]? = _
      rw [Array.getElem?_eq_none (by omega)]
      rfl
  | s :: l, r, A, 0 => by
      show (treesSent first l (r + 1) (A.push _))[A.size + 0]? = _
      rw [treesSent_old first l _ _ _ (by rw [Array.size_push]; omega), Array.getElem?_push,
        if_pos (Nat.add_zero _)]
      rfl
  | s :: l, r, A, τ + 1 => by
      have h := treesSent_at first l (r + 1)
        (A.push { shape := s, number := first + r, src := .own r }) τ
      rw [Array.size_push, show A.size + 1 + τ = A.size + (τ + 1) by omega,
        show r + 1 + τ = r + (τ + 1) by omega] at h
      exact h

/-- Entering parts into trees changes no tree's shape, number and count of lists. -/
theorem partsLaid_keep (sent : Array OracleNotice) (lay : TreeLay) (n0 base : Nat)
    (trees : Array Tree) (t : Nat) :
    ((partsLaid sent lay n0 base trees)[t]?).map (fun x => (x.shape, x.number, x.lists)) =
      (trees[t]?).map fun x => (x.shape, x.number, x.lists) := by
  unfold partsLaid
  generalize List.range sent.size = l
  induction l generalizing trees with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons, ih, Array.getElem?_modify]
    split
    · rw [Option.map_map]
      rfl
    · rfl

/-- One list of messages entered into one tree. -/
theorem partsFold_one (sent : Array OracleNotice) (lay : TreeLay) (n0 base : Nat) :
    ∀ (l : List Nat) (trees : Array Tree) (x : Tree), (∀ i ∈ l, lay.tree.getD i 0 = 0) →
    trees[base]? = some x →
    (l.foldl (fun trees i =>
      trees.modify (base + lay.tree.getD i 0) fun x => { x with
        parts := x.parts.push (n0 + i)
        oneList := x.oneList || (sent.getD i default).shape.answers == 0 }) trees)[base]? =
      some { x with
        parts := x.parts ++ (l.map (n0 + ·)).toArray
        oneList := x.oneList || l.any fun i => (sent.getD i default).shape.answers == 0 }
  | [], trees, x, _, hx => by
      rw [List.foldl_nil, hx]
      simp
  | i :: l, trees, x, h0, hx => by
      rw [List.foldl_cons, h0 i List.mem_cons_self, Nat.add_zero]
      rw [partsFold_one sent lay n0 base l _
        { x with
          parts := x.parts.push (n0 + i)
          oneList := x.oneList || (sent.getD i default).shape.answers == 0 }
        (fun j hj => h0 j (List.mem_cons_of_mem _ hj))
        (by rw [Array.getElem?_modify, if_pos rfl, hx]; rfl)]
      simp [Bool.or_assoc]

/-- **All of a prover's message's oracle messages in its first tree.** -/
theorem partsLaid_one (sent : Array OracleNotice) (lay : TreeLay) (n0 base : Nat)
    (trees : Array Tree) (x : Tree) (h0 : ∀ i, i < sent.size → lay.tree.getD i 0 = 0)
    (hx : trees[base]? = some x) :
    (partsLaid sent lay n0 base trees)[base]? =
      some { x with
        parts := x.parts ++ ((List.range sent.size).map (n0 + ·)).toArray
        oneList := x.oneList ||
          (List.range sent.size).any fun i => (sent.getD i default).shape.answers == 0 } :=
  partsFold_one sent lay n0 base _ trees x (fun i hi => h0 i (List.mem_range.1 hi)) hx

/-- Where the first k messages all lie in tree 0 there are k of them. -/
theorem cnt_all (tree : Array Nat) : ∀ k, (∀ j, j < k → tree.getD j 0 = 0) → cnt tree 0 k = k
  | 0, _ => rfl
  | k + 1, h => by
      show cnt tree 0 k + (if tree.getD k 0 = 0 then 1 else 0) = k + 1
      rw [cnt_all tree k (fun j hj => h j (Nat.lt_succ_of_lt hj)),
        if_pos (h k (Nat.lt_succ_self k))]

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.treesSent_at
#print axioms Johnson.Prover.Link.partsLaid_keep
#print axioms Johnson.Prover.Link.partsFold_one
#print axioms Johnson.Prover.Link.partsLaid_one
#print axioms Johnson.Prover.Link.cnt_all
