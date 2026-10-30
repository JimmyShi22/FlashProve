-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6PieceFacts.lean: SIX FIELDS OF THE OUTPUT HEAD'S BILL
(Law/K6TiedAtObject.lean: K6DueAt; Law/K6ItemsCut.lean) FROM WHAT THE TILING'S FILES SAY OF A PIECE
THAT THE MAKER CUTS (Johnson/Desc/Sound/PieceMore.lean: PieceMore; PieceFence.lean: fenced_at) AND
THREE TESTS WITH CODE.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  along_of_forall2, len_of_more, along_of_more: the piece has as many rounds as its block declares,
      and they are the declared ones.
  fence0_of_fence: where the pin of segment 24's first sending is open in front of the block, the
      fence of every open pin holds that sending's.
  fenced_of_fence0: so the trees of what the head reads were sent in front of the piece (ms0's
      members sit at seats of that sending, by its make).
  pin_open_full: at the full chain that pin is open at border 341 (by the kernel, over the closed
      list).
  fences_full: ALL THREE FENCES AT BLOCK 341 OF THE FULL CHAIN from PieceMore at base 0, the blocks'
      test, and the two tests on the table's numbers (bookFit, fenceFit).

Every letter under "there is": none.
What it does not say. That PieceMore holds of the description's piece 341 (seated_more
hands it out for the maker's pieces); that the three tests say yes (they have run at the walk in
the tiling's files, small; the full size by report, not shown here). Law/NamedAtCut.lean's [not in
this library] road to the first fence (from the
description's own test on the order of sending) is another; this one needs no test of K6's files.
Nothing on soundness.
-/
import Johnson.Desc.Sound.PieceFence
import Johnson.Desc.Kinds.Law.K6KindTied

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open VerifiableInference.Desc.First (ModelPart Item Numbers sampledIn bookFit fenceFit)
open OnBytes.Maker (RDT)
open VerifiableInference.Desc.Sound (Piece Frame Mem Fenced openQ linksFull len_full Along RoundIs
  PieceMore fenced_at toldOf)

theorem along_of_forall2 (num : Fmt.TreeSource → ℕ) :
    ∀ (ds : List RDT) (rs : List Fmt.DeclaredRound),
      List.Forall₂ (fun d r => RoundIs num r d) ds rs → Along (RoundIs num) rs ds
  | _, _, .nil => trivial
  | _, _, .cons h t => ⟨h, along_of_forall2 num _ _ t⟩

section
variable {C : _root_.Run.PQ.CK} {Fr : Frame} {A Cl W : Type} {num : Fmt.TreeSource → ℕ} {base₀ k : ℕ}
  {bs : List (Block A Cl)} {q : Piece C Fr A Cl W}

theorem len_of_more (h : PieceMore num base₀ bs k q) :
    q.ds.length + q.back.length = q.b.rounds.length := by
  rw [h.back, List.length_nil, Nat.add_zero]
  exact h.rounds.length_eq

theorem along_of_more (h : PieceMore num base₀ bs k q) : Along (RoundIs num) q.b.rounds q.ds :=
  along_of_forall2 num _ _ h.rounds

end

theorem fence0_of_fence (N : Numbers) (links : List ModelPart) (ps : List Place) (k base : ℕ)
    (hpin : Item.pin 24 0 ∈ openQ links ps k)
    (h : ∀ x ∈ sampledIn N (openQ links ps k), x.1 < base) : ∀ y ∈ N.sent 24 0, y.1 < base :=
  fun y hy => h y (List.mem_flatMap.2 ⟨.pin 24 0, hpin, hy⟩)

theorem fenced_of_fence0 (msR : List Mem) (N : Numbers) (base : ℕ)
    (h : ∀ y ∈ N.sent 24 0, y.1 < base) : Fenced base (ms0 msR N) :=
  fun x hx => h _ (members_ms0 msR N x hx).2

set_option maxRecDepth 1000000 in
theorem pin_open_full :
    Item.pin 24 0 ∈ openQ linksFull (First.flatPlacesOf linksFull true) 341 := by decide +kernel

/-- **The three fences at block 341 of the full chain.** -/
theorem fences_full {C : _root_.Run.PQ.CK} {Fr : Frame} {A Cl W : Type} {num : Fmt.TreeSource → ℕ}
    {bs : List (Block A Cl)} {q : Piece C Fr A Cl W} (h : PieceMore num 0 bs 341 q)
    (hb : blocksOk bs = true) (msR : List Mem) (N : Numbers)
    (hf : bookFit N (First.flatPlacesOf linksFull true) (toldOf bs) = true)
    (hg : fenceFit N linksFull (First.flatPlacesOf linksFull true) = true) :
    (∀ x ∈ sampledIn N (openQ linksFull (First.flatPlacesOf linksFull true) 341), x.1 < q.base) ∧
      (∀ y ∈ N.sent 24 0, y.1 < q.base) ∧ Fenced q.base (ms0 msR N) := by
  have h1 : ∀ x ∈ sampledIn N (openQ linksFull (First.flatPlacesOf linksFull true) 341),
      x.1 < q.base := fenced_at h hb N linksFull _ hf hg len_full
  have h2 := fence0_of_fence N linksFull _ 341 q.base pin_open_full h1
  exact ⟨h1, h2, fenced_of_fence0 msR N q.base h2⟩

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.along_of_more
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.len_of_more
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.pin_open_full
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.fences_full
