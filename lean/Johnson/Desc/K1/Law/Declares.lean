-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Declares.lean: THE SAME TREE AND THE SAME TENANT: the trees and tenants that a
sending's block declares (the field "oracles" of Johnson/Desc/Block.lean's Block, as
Johnson/Desc/K1/Send.lean writes it) are the layout that layTrees lays (OnBytes/Iop/Ground.lean).
Definitions, statements and proofs, on plain data: no block is run here.

  inTree tree τ xs   of a list taken with its numbers: the entries whose tree is τ.
  inTree_spec        it has as many entries as messages lie in τ; entry number (the count of earlier
                     messages in τ) is message i; and every entry is such a one.
  Declares decl lay n ten   what is said of a declared list: see there.
  declares_of        every list of this make has it.
  lay_tree_size      layTrees gives each message a tree number: the array has the messages' length.
  tenantOf P i       the tenant that K1's text writes of message i.
  oracles_declares   **K1's own text has it**, where the trees can be laid.

What is called. The part number of a message is the count of earlier messages in its tree:
layTrees_fits, Johnson/Desc/Book/BookFits.lean. That the array of tree numbers has the messages'
length: from OnBytes/Iop/LayTreesLaws.lean (pass_inv).

What is not claimed. That the record's book seats a message there: that is the matter of the
receiving's laws. That the groups told are the groups joined. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.K1.Send
import Johnson.Desc.Own.TreesAgree
import Johnson.Desc.Book.BookFits
import OnBytes.Iop.LayTreesLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes
open VerifiableInference.Desc.Book (cnt LayFits layTrees_fits)

/-! ## A list with its numbers, cut by trees -/

theorem tree_beq (tree : Array Nat) (j τ : Nat) (h : j < tree.size) :
    (tree[j]? == some τ) = (tree.getD j 0 == τ) := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
  simp

/-- A property of lists that holds of none and goes along where an entry is laid behind. -/
theorem from_behind {α : Type} {motive : List α → Prop} (nil : motive [])
    (snoc : ∀ ys z, motive ys → motive (ys ++ [z])) (xs : List α) : motive xs := by
  have h : ∀ l : List α, motive l.reverse := by
    intro l
    induction l with
    | nil => exact nil
    | cons a l ih =>
      rw [List.reverse_cons]
      exact snoc _ _ ih
  have h' := h xs.reverse
  rwa [List.reverse_reverse] at h'

/-- Of a list taken with its numbers: the entries whose tree is τ. -/
def inTree {α : Type} (tree : Array Nat) (τ : Nat) (xs : List α) : List (α × Nat) :=
  xs.zipIdx.filter fun y => tree[y.2]? == some τ

theorem inTree_concat {α : Type} (tree : Array Nat) (τ : Nat) (ys : List α) (z : α)
    (hy : ys.length < tree.size) :
    inTree tree τ (ys ++ [z]) =
      inTree tree τ ys ++ (if tree.getD ys.length 0 = τ then [(z, ys.length)] else []) := by
  unfold inTree
  rw [List.zipIdx_append, List.filter_append]
  congr 1
  simp only [List.zipIdx_cons, List.zipIdx_nil, Nat.zero_add]
  by_cases c : tree.getD ys.length 0 = τ
  · rw [if_pos c, List.filter_cons_of_pos (by rw [tree_beq _ _ _ hy]; exact beq_iff_eq.2 c),
      List.filter_nil]
  · rw [if_neg c,
      List.filter_cons_of_neg (by rw [tree_beq _ _ _ hy]; exact fun h => c (beq_iff_eq.1 h)),
      List.filter_nil]

/-- **The cut by trees**: its length; where message i stands in it; and that nothing else does. -/
theorem inTree_spec {α : Type} (tree : Array Nat) (τ : Nat) (xs : List α)
    (hsz : xs.length ≤ tree.size) :
    (inTree tree τ xs).length = cnt tree τ xs.length ∧
      (∀ i x, xs[i]? = some x → tree.getD i 0 = τ →
        (inTree tree τ xs)[cnt tree τ i]? = some (x, i)) ∧
      ∀ t y, (inTree tree τ xs)[t]? = some y →
        xs[y.2]? = some y.1 ∧ tree.getD y.2 0 = τ ∧ cnt tree τ y.2 = t := by
  induction xs using from_behind with
  | nil =>
    exact ⟨rfl, fun i x h => by simp at h, fun t y h => by simp [inTree] at h⟩
  | snoc ys z ih =>
    have hy : ys.length < tree.size := by
      rw [List.length_append, List.length_singleton] at hsz
      omega
    obtain ⟨l, a, b⟩ := ih (Nat.le_of_lt hy)
    rw [inTree_concat tree τ ys z hy]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.length_append, l, List.length_append, List.length_singleton]
      show _ = cnt tree τ ys.length + (if tree.getD ys.length 0 = τ then 1 else 0)
      by_cases c : tree.getD ys.length 0 = τ
      · rw [if_pos c, if_pos c]
        rfl
      · rw [if_neg c, if_neg c]
        rfl
    · intro i x hx hτ
      by_cases hi : i < ys.length
      · rw [List.getElem?_append_left hi] at hx
        have q := a i x hx hτ
        have lt := (List.getElem?_eq_some_iff.1 q).1
        rw [List.getElem?_append_left lt]
        exact q
      · have hi' : i = ys.length := by
          have := (List.getElem?_eq_some_iff.1 hx).1
          rw [List.length_append, List.length_singleton] at this
          omega
        subst hi'
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hx
        obtain rfl : z = x := Option.some.inj hx
        rw [if_pos hτ, ← l, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
    · intro t y h
      by_cases ht : t < (inTree tree τ ys).length
      · rw [List.getElem?_append_left ht] at h
        obtain ⟨b1, b2, b3⟩ := b t y h
        have lt := (List.getElem?_eq_some_iff.1 b1).1
        exact ⟨by rw [List.getElem?_append_left lt]; exact b1, b2, b3⟩
      · rw [List.getElem?_append_right (Nat.le_of_not_lt ht)] at h
        by_cases c : tree.getD ys.length 0 = τ
        · rw [if_pos c] at h
          have h0 : t - (inTree tree τ ys).length = 0 := by
            have := (List.getElem?_eq_some_iff.1 h).1
            rw [List.length_singleton] at this
            omega
          rw [h0] at h
          obtain rfl : (z, ys.length) = y := Option.some.inj h
          refine ⟨?_, c, ?_⟩
          · show (ys ++ [z])[ys.length]? = some z
            rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
            rfl
          · show cnt tree τ ys.length = t
            omega
        · rw [if_neg c] at h
          exact absurd (List.getElem?_eq_some_iff.1 h).1 (Nat.not_lt_zero _)

/-! ## What is said of a declared list -/

/-- **The declared list is the layout.** decl: the oracle messages that a sending's block declares,
one a tree; lay: the layout; n: the number of messages sent; ten i: message i's tenant. -/
structure Declares (decl : List VerifiableInference.Desc.Oracle) (lay : TreeLay) (n : Nat)
    (ten : Nat → VerifiableInference.Desc.SymbolComponent) : Prop where
  /-- as many trees are declared as the layout has -/
  trees : decl.length = lay.shapes.size
  /-- the declared tree number τ has the layout's shape number τ's length and width, and as many
  tenants as messages lie in τ -/
  shape : ∀ τ O, decl[τ]? = some O → O.logLength = (lay.shapes.getD τ {}).logN ∧
    O.words = (lay.shapes.getD τ {}).mainWidth + (lay.shapes.getD τ {}).maskWidth ∧
    O.tenants.length = cnt lay.tree τ n
  /-- message i's tenant stands in the declared tree of the layout's number, at the layout's part -/
  tenant : ∀ i, i < n → ∃ O, decl[lay.tree.getD i 0]? = some O ∧
    O.tenants[lay.part.getD i 0]? = some (ten i)
  /-- every declared tenant is some message's -/
  back : ∀ τ O t, decl[τ]? = some O → t < O.tenants.length →
    ∃ i, i < n ∧ lay.tree.getD i 0 = τ ∧ lay.part.getD i 0 = t

/-- Every list of this make has it. xs: the messages, each with what else its tenant is written of;
g: what is declared of a shape and its number; f: the tenant written of an entry. -/
theorem declares_of {α : Type} (lay : TreeLay) (xs : List α)
    (g : TreeShape × Nat → VerifiableInference.Desc.Oracle)
    (f : α × Nat → VerifiableInference.Desc.SymbolComponent) (ten : Nat → VerifiableInference.Desc.SymbolComponent)
    (hg : ∀ t i, g (t, i) = { logLength := t.logN, words := t.mainWidth + t.maskWidth
                              tenants := (inTree lay.tree i xs).map f })
    (hfit : LayFits xs.length lay) (hsz : lay.tree.size = xs.length)
    (hten : ∀ i x, xs[i]? = some x → f (x, i) = ten i) :
    Declares (lay.shapes.toList.zipIdx.map g) lay xs.length ten := by
  have key : ∀ τ, (lay.shapes.toList.zipIdx.map g)[τ]? =
      (lay.shapes[τ]?).map fun t => g (t, τ) := by
    intro τ
    simp [List.getElem?_map, List.getElem?_zipIdx, Option.map_map, Function.comp_def]
  have spec := fun τ => inTree_spec lay.tree τ xs (Nat.le_of_eq hsz.symm)
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro τ O h
    rw [key] at h
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
    have e : lay.shapes.getD τ {} = t := by
      rw [Array.getD_eq_getD_getElem?, ht]
      rfl
    rw [hg, e]
    exact ⟨rfl, rfl, by rw [List.length_map]; exact (spec τ).1⟩
  · intro i hi
    obtain ⟨lt, hp⟩ := hfit i hi
    refine ⟨g (lay.shapes[lay.tree.getD i 0], lay.tree.getD i 0), ?_, ?_⟩
    · rw [key, Array.getElem?_eq_getElem lt]
      rfl
    · rw [hg]
      show ((inTree lay.tree (lay.tree.getD i 0) xs).map f)[lay.part.getD i 0]? = _
      rw [List.getElem?_map, hp, (spec _).2.1 i xs[i] (List.getElem?_eq_getElem hi) rfl]
      show some (f (xs[i], i)) = _
      rw [hten i _ (List.getElem?_eq_getElem hi)]
  · intro τ O t h ht
    rw [key] at h
    obtain ⟨s, _, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [hg] at ht
    have ht' : t < (inTree lay.tree τ xs).length := by
      have : t < ((inTree lay.tree τ xs).map f).length := ht
      rwa [List.length_map] at this
    obtain ⟨b1, b2, b3⟩ := (spec τ).2.2 t _ (List.getElem?_eq_getElem ht')
    have lt := (List.getElem?_eq_some_iff.1 b1).1
    exact ⟨_, lt, b2, by rw [(hfit _ lt).2, b2]; exact b3⟩

/-! ## K1's own text -/

/-- layTrees gives each message a tree number. -/
theorem lay_tree_size {codes : Codes} {sent : Array OracleNotice} {L : TreeLay}
    (h : layTrees codes sent = some L) : L.tree.size = sent.size := by
  rw [LayTreesLaws.layTrees_eq] at h
  obtain ⟨filled, _, h2⟩ := Option.bind_eq_some_iff.1 h
  split at h2
  · obtain rfl := Option.some.inj h2
    have h1 := LayTreesLaws.pass_inv codes sent false (fun _ => False)
      (#[], #[], Array.replicate sent.size 0) (by simp) (fun _ h => h.elim)
    exact (LayTreesLaws.pass_inv codes sent true (fun _ => False) _ h1.1 (fun _ h => h.elim)).1
  · cases h2

/-- The tenant that K1's text writes of message i. -/
def tenantOf (P : Par) (i : Nat) : VerifiableInference.Desc.SymbolComponent :=
  let s := (P.sent.getD i default).shape
  { main := s.mainRows * s.mainDeg, mask := s.maskRows * 3, degree := s.mainDeg
    sampled := s.answers != 0, groups := P.groups.getD i [] }

/-- **The trees and tenants that K1's block declares are the layout**, where the trees can be
laid. -/
theorem oracles_declares (P : Par) (lay : TreeLay) (h : layTrees P.codes P.sent = some lay) :
    ∃ decl, oracles P = [decl, []] ∧ Declares decl lay P.sent.size (tenantOf P) := by
  unfold oracles Par.trees
  rw [Own.treesMade_eq, h]
  refine ⟨_, rfl, ?_⟩
  refine declares_of lay P.sent.toList _ _ (tenantOf P) (fun _ _ => rfl) (layTrees_fits h)
    (lay_tree_size h) ?_
  intro i x hx
  have e : P.sent.getD i default = x := by
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hx]
    rfl
  unfold tenantOf
  rw [e]

end VerifiableInference.Desc.K1
