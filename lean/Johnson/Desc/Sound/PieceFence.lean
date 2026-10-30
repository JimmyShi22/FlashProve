-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PieceFence.lean: FROM THE PIECE's BASE AS A NUMBER TO THE FORM IN WHICH THE LAWS ASK IT: "EVERY TENANT THAT THE LAW's PINS READ SITS IN A TREE BELOW q.base". One definition, seven theorems.

THE CHAIN OF EQUATIONS, for the piece q at a place k of a chain's row:
  q.base = base₀ + the roots that the blocks in front DECLARE                      (PieceMore.base, Johnson/Desc/Sound/PieceMore.lean)
         = base₀ + the number of oracles that the blocks in front TELL             (roots_told: told_len, Johnson/Desc/Sound/ToldCount.lean, at the PREFIX; asked: blocksOk of the chain: a clause of planOk)
         = base₀ + treesTold (toldOf bs) k                                         (told_is: the table's neighbour's own count, Johnson/Desc/First/BookFit.lean)
         = Numbers.treesAt at the k-th place, in the first chain (base₀ = 0)       (bookFit's yes: a test on the plan that runs)
  and every tenant of an open pin with a sample at border k sits in a tree below that number (fenceFit's yes, Johnson/Desc/First/FenceFit.lean: a test that runs).
  toldOf bs: for each block, in order, the oracles beneath the roots that it sends, all rounds together.
  base_told: q.base = base₀ + (oraclesOf (bs.take k)).length · base_treesTold · base_treesAt (the first chain) ·
  fenced_at: **AT THE FIRST CHAIN: under blocksOk, bookFit's and fenceFit's yes: ∀ x ∈ sampledIn N (the open set at border k), x.1 < q.base.**
The blocks here are the pieces' own (in a description's pieces: its blocks as a piece holds them): rounds and oracles are read through them.

Limits. The three premises are tests on the plan | clauses of planOk: that they say yes at a description is a run's word or that description's yes. Which tenants a given law's pins read is that law's. NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PieceMore
import Johnson.Desc.Sound.ToldCount
import Johnson.Desc.First.BookFit
import Johnson.Desc.First.FenceFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (Numbers ModelPart treesTold bookFit bookFit_at fenceFit fenceFit_at sampledIn openSets start)

variable {C : CK} {F : Frame} {S Cl W : Type}

/-- For each block, in order, the oracles beneath the roots that it sends, all rounds together. -/
def toldOf (bs : List (Block S Cl)) : List (List Oracle) := bs.map fun b => b.oracles.flatMap id

/-- A prefix of blocks that are in order is in order. -/
theorem blocksOk_take (bs : List (Block S Cl)) (h : blocksOk bs = true) (k : ℕ) :
    blocksOk (bs.take k) = true := by
  unfold blocksOk at h ⊢
  exact List.all_eq_true.2 fun b hb => List.all_eq_true.1 h b (List.mem_of_mem_take hb)

/-- **The roots that the blocks in front declare are the oracles that they tell.** -/
theorem roots_told (bs : List (Block S Cl)) (h : blocksOk bs = true) (k : ℕ) :
    ((bs.take k).map rootsOf).sum = (oraclesOf (bs.take k)).length := by
  rw [told_len (bs.take k) (blocksOk_take bs h k)]
  generalize bs.take k = l
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append, ih]
    rfl

/-- The table's neighbour's count is that number. -/
theorem told_is (bs : List (Block S Cl)) (k : ℕ) :
    treesTold (toldOf bs) k = (oraclesOf (bs.take k)).length := by
  unfold treesTold toldOf oraclesOf
  rw [← List.map_take, List.map_map]
  generalize bs.take k = l
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, ih]
    rfl

section At
variable {num : Fmt.TreeSource → ℕ} {base₀ : ℕ} {bs : List (Block S Cl)} {k : ℕ} {q : Piece C F S Cl W}

/-- **The base is the chain's first tree and the oracles that the blocks in front tell.** -/
theorem base_told (h : PieceMore num base₀ bs k q) (hb : blocksOk bs = true) :
    q.base = base₀ + (oraclesOf (bs.take k)).length := by
  rw [h.base, roots_told bs hb k]

theorem base_treesTold (h : PieceMore num base₀ bs k q) (hb : blocksOk bs = true) :
    q.base = base₀ + treesTold (toldOf bs) k := by
  rw [base_told h hb, told_is]

/-- **In the first chain the base is the table's own number at the place.** -/
theorem base_treesAt (h : PieceMore num 0 bs k q) (hb : blocksOk bs = true) (N : Numbers)
    (ps : List Place) (hf : bookFit N ps (toldOf bs) = true) (hk : k ≤ ps.length) :
    q.base = N.treesAt ps[k]? := by
  rw [base_treesTold h hb, (bookFit_at N ps (toldOf bs) hf k hk).1, Nat.zero_add]

/-- **THE LAWS' FORM, AT THE FIRST CHAIN: every tenant of an open pin with a sample at the border in front of the piece sits in a tree below the piece's base.** -/
theorem fenced_at (h : PieceMore num 0 bs k q) (hb : blocksOk bs = true) (N : Numbers)
    (links : List ModelPart) (ps : List Place) (hf : bookFit N ps (toldOf bs) = true)
    (hg : fenceFit N links ps = true) (hk : k ≤ ps.length) :
    ∀ x ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []), x.1 < q.base := by
  intro x hx
  rw [base_treesAt h hb N ps hf hk]
  exact fenceFit_at N links ps hg k hk x hx

end At

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.roots_told
#print axioms VerifiableInference.Desc.Sound.told_is
#print axioms VerifiableInference.Desc.Sound.base_told
#print axioms VerifiableInference.Desc.Sound.base_treesTold
#print axioms VerifiableInference.Desc.Sound.base_treesAt
#print axioms VerifiableInference.Desc.Sound.fenced_at
