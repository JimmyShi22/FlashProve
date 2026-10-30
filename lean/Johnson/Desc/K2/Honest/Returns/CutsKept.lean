-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/CutsKept.lean: THE BOOK OF TREES IS CUT WHERE A STATE STOOD: if a
state of the walk has N places and T trees in its book, then at every later state of the same fold,
up to the place behind the last segment, a message's number is below N just when its tree's number
is below T. SO TWO MESSAGES OF ONE TREE LIE BETWEEN THE SAME TWO CUTS OF THE WALK (a cut is a state
between two sub-protocols). Under the opening alone. A tool for `ReadFits.own` (Returns/Read.lean;
Returns/PartsPlaced.lean). A definition; statements with their proofs.

  `cutAt N T B r` the book B has at least N places and T trees, and a place's message is below N
                    just when its tree is below T; r, the number of roots, is not read: the
                    library's walk asks a sentence on both
  `cutAt_recv`, `cutAt_same` it goes along where a prover's message is received (off the library's
                    `Seated`), and where the places and the number of trees stay (`SameNumbers`)
  `cutAt_self` a book that has the library's `BookFits` is cut at its own two sizes
  `cut_mates` between two cuts: a message whose tree is that of a message between them lies between
                    them
  `cut_kept` from the fold's returns at two cuts k₀ ≤ k of one fold, k up to the front's length: the
                    later book is cut at the earlier book's sizes

By, all the library's: `recvP_seat` (Johnson/Desc/Book/BookFitsGround.lean), `Seated`
(Johnson/Desc/Book/Seated.lean), `placed_of_fits` (Johnson/Desc/Book/BookFits.lean) ·
`seatKeeps_front` (Johnson/IMR/FrontCut.lean): every sub-protocol in front keeps a sentence on the
book that receiving and `SameNumbers` keep · `open_between`, `open_fits`
(Johnson/IMR/WalkGivesAt.lean): of two cuts of one fold, one in front of the other; the book fits at
a cut.

Limits. Nothing behind the place behind the last segment. Nothing on adopting. That a given stretch
of messages is one sending's is not said here. This file's imports are heavy. Nothing on any
property.

-/
import Johnson.IMR.AtReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (SameNumbers)
open VerifiableInference.Desc.Book (BookFits placed_of_fits recvP_seat)
open Meaning.K2 (SeatKeeps PR seatKeeps_front open_between open_fits frontOf)
open ProofFile (Cl)

/-- **The book is cut at N places and T trees.** -/
def cutAt (N T : Nat) (B : TreeBook) (_r : Nat) : Prop :=
  N ≤ B.place.size ∧ T ≤ B.trees.size ∧
    ∀ (j τ k : Nat), B.place[j]? = some (τ, k) → (j < N ↔ τ < T)

theorem cutAt_recv (N T : Nat) {L : Type} (d d' : _root_.Desc.Plain.DState L)
    (sent : Array OracleNotice) (ids : Array Nat)
    (h : VerifiableInference.Desc.Ground.recvP 0 d sent = some (ids, d'))
    (hP : cutAt N T d.book d.roots) : cutAt N T d'.book d'.roots := by
  obtain ⟨-, lay, -, Se⟩ := recvP_seat 0 d d' sent ids h
  obtain ⟨c1, c2, c3⟩ := hP
  refine ⟨by rw [Se.count]; omega, by rw [Se.size]; omega, fun j τ k hj => ?_⟩
  by_cases lt : j < d.book.place.size
  · rw [Se.places j lt] at hj
    exact c3 j τ k hj
  · have lt' := (Array.getElem?_eq_some_iff.1 hj).1
    rw [Se.count] at lt'
    obtain ⟨i, rfl⟩ : ∃ i, j = d.st.oracles.size + i :=
      ⟨j - d.st.oracles.size, by rw [Se.step]; omega⟩
    have hi : i < sent.size := by
      rw [Se.step] at lt'
      omega
    rw [Se.new i hi] at hj
    have e : d.book.trees.size + lay.tree.getD i 0 = τ := congrArg Prod.fst (Option.some.inj hj)
    have s0 := Se.step
    constructor
    · intro a
      omega
    · intro a
      omega

theorem cutAt_same (N T : Nat) (A B : TreeBook) (r : Nat) (h : SameNumbers A B)
    (k : cutAt N T A r) : cutAt N T B r := by
  obtain ⟨c1, c2, c3⟩ := k
  refine ⟨by rw [h.2.1]; exact c1, by rw [h.1]; exact c2, fun j τ q hj => ?_⟩
  rw [h.2.1] at hj
  exact c3 j τ q hj

theorem cutAt_self {B : TreeBook} (h : BookFits B) (r : Nat) :
    cutAt B.place.size B.trees.size B r := by
  refine ⟨Nat.le_refl _, Nat.le_refl _, fun j τ k hj => ?_⟩
  exact ⟨fun _ => placed_of_fits h j (τ, k) hj, fun _ => (Array.getElem?_eq_some_iff.1 hj).1⟩

/-- **Between two cuts.** -/
theorem cut_mates {B : TreeBook} {r N T N' T' : Nat} (h : cutAt N T B r) (h' : cutAt N' T' B r)
    {o q τ k k' : Nat} (ho : B.place[o]? = some (τ, k)) (hq : B.place[q]? = some (τ, k'))
    (h1 : N ≤ o) (h2 : o < N') : N ≤ q ∧ q < N' := by
  have a1 := h.2.2 o τ k ho
  have a2 := h.2.2 q τ k' hq
  have b1 := h'.2.2 o τ k ho
  have b2 := h'.2.2 q τ k' hq
  refine ⟨?_, b2.2 (b1.1 h2)⟩
  by_cases c : q < N
  · have := a1.2 (a2.1 c)
    omega
  · omega

/-- **The later book is cut at the earlier book's sizes.** -/
theorem cut_kept {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B)
    {k₀ k : Nat} (h₀ : k₀ ≤ k) (hk : k ≤ (frontOf c).length) {p : ProofFile.InstPub}
    {R R₀ R₁ : List Fmt.RoundView} {C C₀ C₁ : List VerifiableInference.Desc.OpenedColumn} {t₀ t : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take k₀) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (t, R₁, C₁)) :
    cutAt t₀.book.place.size t₀.book.trees.size t.book t.roots := by
  have K3 : SeatKeeps (PR (cutAt t₀.book.place.size t₀.book.trees.size)) := seatKeeps_front
    (fun d d' sent ids e k => cutAt_recv _ _ d d' sent ids e k) (cutAt_same _ _)
  exact open_between K3 O trivial (fun _ _ _ => trivial) h₀ hk f₀ f
    (cutAt_self (open_fits O (Nat.le_trans h₀ hk) f₀) _)

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.cutAt_recv
#print axioms VerifiableInference.Desc.K2.Honest.Returns.cutAt_same
#print axioms VerifiableInference.Desc.K2.Honest.Returns.cutAt_self
#print axioms VerifiableInference.Desc.K2.Honest.Returns.cut_mates
#print axioms VerifiableInference.Desc.K2.Honest.Returns.cut_kept
