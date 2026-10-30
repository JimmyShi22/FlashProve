-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/BookInOrder.lean: **"THE BOOK IS IN ORDER"**: a test with code on a chain's own record, and who keeps it. Definitions, statements and proofs.

What for. The law of the proximity test in the plain form asks, of the record in front, that the trees which the first switch's declared openings name are
those at the book's places (FirstOpens, Johnson/Desc/K12/Coin/Sheet.lean). Johnson/Desc/K12/Coin/FirstBook.lean has that from the block's own guard at a yes, a test on the
plan, and this one promise on the record. So it must be handed from block to block along a chain that sends all the trees that its tests open.
  BookOrd first B        the tree at the place z of the book bears the number first + z. bookOrdB: the same as a test with code; bookOrd_iff.
  BookStep first B r     the book is in order AND the record counts as many roots as the book has trees. bookStepB; bookStep_iff.
  bookStep_empty         an empty book with no root has it.
  bookStep_recv          **a receiving keeps it**: the book behind a prover's message with oracle messages (recvBook, FenceRecv.lean: bookSent's
                         text), at the count of roots with the new trees added.
  bookStep_received      the same from Received (FenceSend.lean): what the ground's receiving writes (recvP_received, FenceSendGround.lean), so: AT K14's TWO
                         SENDINGS (sendAt_received, FenceK14Sends.lean).
  bookStep_same          a block that leaves the book and the count of roots keeps it.
  CONTROLS: not_step_skipped: a book whose one tree bears the number first + 1 has it not · not_step_roots: nor an empty book with one root counted.
Limits. first MUST BE THE NUMBER AT WHICH THE RECEIVING COUNTS (the chain's firstTree): one letter for both. A tree that is TAKEN OVER from another chain bears that
chain's number: a book with such a tree is not in order: the last chain's book has not this form. Nothing on what a tree holds. NO SOUNDNESS.
The four definitions (BookOrd · bookOrdB · BookStep · bookStepB) stand in
Johnson/Desc/Sound/BookOrder.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FenceSend
import Johnson.Desc.Sound.BookOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes
open OnBytes.Slice (treesSent partsLaid treesSent_old partsLaid_old)

theorem bookOrd_iff (first : ℕ) (B : TreeBook) : bookOrdB first B = true ↔ BookOrd first B := by
  constructor
  · intro h z T hT
    have hz : z < B.trees.size := (Array.getElem?_eq_some_iff.1 hT).1
    have h1 := List.all_eq_true.1 h z (List.mem_range.2 hz)
    rw [hT] at h1
    exact beq_iff_eq.1 h1
  · intro h
    refine List.all_eq_true.2 fun z _ => ?_
    cases hT : B.trees[z]? with
    | none => rfl
    | some T => exact beq_iff_eq.2 (h z T hT)

theorem bookStep_iff (first : ℕ) (B : TreeBook) (roots : ℕ) :
    bookStepB first B roots = true ↔ BookStep first B roots := by
  unfold bookStepB BookStep
  rw [Bool.and_eq_true, beq_iff_eq, bookOrd_iff]

theorem bookStep_empty (first : ℕ) : BookStep first { trees := #[], place := #[] } 0 :=
  ⟨rfl, fun z T h => by simp at h⟩

/-- Entering parts into trees changes no tree's number. -/
theorem partsLaid_number (sent : Array OracleNotice) (lay : TreeLay) (n0 base : ℕ)
    (trees : Array Tree) (t : ℕ) :
    ((partsLaid sent lay n0 base trees)[t]?).map (·.number) = (trees[t]?).map (·.number) := by
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

/-- Nor their count. -/
theorem partsLaid_count (sent : Array OracleNotice) (lay : TreeLay) (n0 base : ℕ)
    (trees : Array Tree) : (partsLaid sent lay n0 base trees).size = trees.size := by
  unfold partsLaid
  generalize List.range sent.size = l
  induction l generalizing trees with
  | nil => rfl
  | cons i l ih => rw [List.foldl_cons, ih, Array.size_modify]

theorem treesSent_count (first : ℕ) : ∀ (l : List TreeShape) (r : ℕ) (A : Array Tree),
    (treesSent first l r A).size = A.size + l.length
  | [], _, _ => rfl
  | s :: l, r, A => by
    show (treesSent first l (r + 1) (A.push _)).size = _
    rw [treesSent_count first l, Array.size_push, List.length_cons]
    omega

/-- The τ-th of the appended trees bears the number first + (r + τ). -/
theorem treesSent_new_number (first : ℕ) : ∀ (l : List TreeShape) (r : ℕ) (A : Array Tree) (τ : ℕ),
    τ < l.length → ((treesSent first l r A)[A.size + τ]?).map (·.number) = some (first + (r + τ))
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | s :: l, r, A, 0, _ => by
    show ((treesSent first l (r + 1) (A.push _))[A.size + 0]?).map (·.number) = _
    rw [treesSent_old first l _ _ _ (by rw [Array.size_push]; omega), Array.getElem?_push,
      if_pos (Nat.add_zero _)]
    rfl
  | s :: l, r, A, τ + 1, h => by
    have ih := treesSent_new_number first l (r + 1)
      (A.push { shape := s, number := first + r, src := .own r }) τ (Nat.lt_of_succ_lt_succ h)
    rw [Array.size_push] at ih
    have e1 : A.size + (τ + 1) = A.size + 1 + τ := by omega
    have e2 : r + (τ + 1) = r + 1 + τ := by omega
    show ((treesSent first l (r + 1) (A.push _))[A.size + (τ + 1)]?).map (·.number) = _
    rw [e1, e2]
    exact ih

/-- **A receiving keeps it.** -/
theorem bookStep_recv (first : ℕ) (bk : TreeBook) (sent : Array OracleNotice) (lay : TreeLay)
    (n0 roots : ℕ) (h : BookStep first bk roots) :
    BookStep first (recvBook first bk sent lay n0 roots) (roots + lay.shapes.size) := by
  obtain ⟨hr, ho⟩ := h
  have hsz : (recvBook first bk sent lay n0 roots).trees.size = bk.trees.size + lay.shapes.size := by
    show (partsLaid sent lay n0 bk.trees.size
      (treesSent first lay.shapes.toList roots bk.trees)).size = _
    rw [partsLaid_count, treesSent_count, Array.length_toList]
  refine ⟨by rw [hsz, hr], fun z T hT => ?_⟩
  have hz : z < bk.trees.size + lay.shapes.size := by
    rw [← hsz]
    exact (Array.getElem?_eq_some_iff.1 hT).1
  have hn : ((treesSent first lay.shapes.toList roots bk.trees)[z]?).map (·.number) =
      some T.number := by
    rw [← partsLaid_number sent lay n0 bk.trees.size]
    have hT' : (partsLaid sent lay n0 bk.trees.size
      (treesSent first lay.shapes.toList roots bk.trees))[z]? = some T := hT
    rw [hT']
    rfl
  by_cases hlt : z < bk.trees.size
  · rw [treesSent_old _ _ _ _ z hlt] at hn
    obtain ⟨T₀, hT₀, e⟩ := Option.map_eq_some_iff.1 hn
    rw [← e]
    exact ho z T₀ hT₀
  · obtain ⟨τ, rfl⟩ : ∃ τ, z = bk.trees.size + τ := ⟨z - bk.trees.size, by omega⟩
    rw [treesSent_new_number first _ roots bk.trees τ (by rw [Array.length_toList]; omega)] at hn
    have e := Option.some.inj hn
    rw [← e, hr]

/-- The same from what a receiving writes. -/
theorem bookStep_received (ft : ℕ) (sent : Array OracleNotice) (lay : TreeLay) (st st' : Statement)
    (bk bk' : TreeBook) (roots roots' : ℕ) (h : Received ft sent lay st bk roots st' bk' roots')
    (hb : BookStep ft bk roots) : BookStep ft bk' roots' := by
  obtain ⟨_, _, _, rfl, rfl⟩ := h
  exact bookStep_recv ft bk sent lay _ roots hb

/-- A block that leaves the book and the count of roots keeps it. -/
theorem bookStep_same (first : ℕ) (bk bk' : TreeBook) (roots roots' : ℕ) (e₁ : bk' = bk)
    (e₂ : roots' = roots) (h : BookStep first bk roots) : BookStep first bk' roots' := by
  rw [e₁, e₂]
  exact h

/-- A control: a skipped number. -/
theorem not_step_skipped (first : ℕ) (s : TreeShape) :
    ¬ BookStep first { trees := #[{ shape := s, number := first + 1 }], place := #[] } 1 := by
  intro h
  have := h.2 0 { shape := s, number := first + 1 } rfl
  have e : first + 1 = first + 0 := this
  omega

/-- A control: a root that the book does not hold. -/
theorem not_step_roots (first : ℕ) : ¬ BookStep first { trees := #[], place := #[] } 1 := by
  intro h
  have e : (1 : ℕ) = 0 := h.1
  omega

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.bookOrd_iff
#print axioms VerifiableInference.Desc.Sound.bookStep_recv
#print axioms VerifiableInference.Desc.Sound.bookStep_received
#print axioms VerifiableInference.Desc.Sound.not_step_skipped
