-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/RowBase.lean: THE n-TH PIECE's BASE AT A DESCRIPTION's OWN ROWS, AS A NUMBER THAT A PROGRAM CAN COMPUTE off the description's blocks and the data. Book-keeping, general in the description.
Main names. `cutBase_held`: a block as a piece holds it declares the block's own rounds: the bases are those of the bare blocks. `baseOf base ds bs n`: the n-th base of a list of blocks (the list may be empty: then `base`). `base_at₁` | `₂` | `₃`: under the head, the n-th piece of chain j has `p.base = baseOf ‹the chain's first tree› ‹its data› F.….blocksInOrder n`.
Nothing on soundness.

-/
import Johnson.Top.Fire.Code.RowCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

section
variable {P S Cl : Type}

theorem cutBase_held : ∀ (l : List (Block S Cl)) (n base : ℕ) (ds : List RDT) (b : Block S Cl),
    cutBase base ds (held b : Block (P × S) Cl) (l.map held) n = cutBase base ds b l n
  | [], 0, _, _, _ => rfl
  | [], _ + 1, _, _, _ => rfl
  | _ :: _, 0, _, _, _ => rfl
  | c :: l, n + 1, base, ds, b => cutBase_held l n (base + nTrees (ds.take b.rounds.length)) (ds.drop b.rounds.length) c

/-- The n-th base of a list of blocks. -/
def baseOf (base : ℕ) (ds : List RDT) : List (Block S Cl) → ℕ → ℕ
  | [], _ => base
  | b :: l, n => cutBase base ds b l n

end

section
variable {Xi W : Type} (C : CK) (F : FileDescription Xi) (D : WholeD)
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
    (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (dW wEnd : W)

theorem base_at₁ (q : F.first.blocksInOrder = c₁ :: k₁) (n : ℕ) (p) (h : ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[n]? = some p) :
    p.base = baseOf 0 D.ds₁ F.first.blocksInOrder n := by
  obtain ⟨b, _, rfl⟩ := rowAt₁ C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd n p h
  rw [q]
  exact cutBase_held k₁ n 0 D.ds₁ c₁

theorem base_at₂ (q : F.shared.blocksInOrder = c₂ :: k₂) (n : ℕ) (p) (h : ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[n]? = some p) :
    p.base = baseOf D.t₁ D.ds₂ F.shared.blocksInOrder n := by
  obtain ⟨b, _, rfl⟩ := rowAt₂ C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd n p h
  rw [q]
  exact cutBase_held k₂ n D.t₁ D.ds₂ c₂

theorem base_at₃ (q : F.second.blocksInOrder = c₃ :: k₃) (n : ℕ) (p) (h : ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)[n]? = some p) :
    p.base = baseOf (D.t₁ + D.t₂) D.ds₃ F.second.blocksInOrder n := by
  obtain ⟨b, _, rfl⟩ := rowAt₃ C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd n p h
  rw [q]
  exact cutBase_held k₃ n (D.t₁ + D.t₂) D.ds₃ c₃

end

end LPFD

#print axioms LPFD.cutBase_held
#print axioms LPFD.base_at₁
#print axioms LPFD.base_at₂
#print axioms LPFD.base_at₃
