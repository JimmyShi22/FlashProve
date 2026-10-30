-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/PartsPlaced.lean: AN INVARIANT OF THE BOOK OF TREES THAT THE
LIBRARY's `BookFits` (Johnson/Desc/Book/BookFits.lean) LEAVES OPEN BY ITS OWN WORD ("nor that a
tree's parts hold nothing else"): EVERY PART OF EVERY TREE IS A MESSAGE WHOSE PLACE IN THE BOOK IS
THAT TREE AND THAT PART NUMBER. It holds at every state that is reached up to the place behind the
last segment, under the opening alone. WITH IT `ReadFits.own` (Returns/Read.lean: a tree that holds
an opened message holds opened messages alone) BECOMES A SENTENCE ON THE BOOK's LIST OF PLACES. A
definition; statements with their proofs.

  `cnt_surj` below the count of a tree's messages every number is the count at one of them
  `partsPlaced B r` THE INVARIANT; r, the number of roots, is not read: the library's walk asks a
                    sentence on both
  `partsPlaced_recv` it goes along where a prover's message is received: off the library's `Seated`
  `partsPlaced_same` it goes along where the trees' parts and the places stay (`SameNumbers`)
  `partsPlaced_reached` so at every state reached over the RAW flat list (this folder's "reached
                    over the wrapped list" comes to it by the library's `reach_raw`), number k up to
                    the front's length
  `own_of_places` where the invariant holds: if every message whose place's tree is among the opened
                    ones' trees is itself opened, `ReadFits.own` holds, in its own letters

By, all the library's: `recvP_seat` (Johnson/Desc/Book/BookFitsGround.lean), `Seated`
(Johnson/Desc/Book/Seated.lean), `cnt`, `LayFits` (Johnson/Desc/Book/BookFits.lean) ·
`seatKeeps_front` (Johnson/IMR/FrontCut.lean), `open_fold` (Johnson/IMR/OpenWalk.lean): the walk
over the seats, for any sentence on the book that receiving and `SameNumbers` keep · `start_empty`
(Johnson/IMR/BookSeat.lean) · `Reach.fold` (Johnson/Top/H0/Walk/Reach.lean). After
`bookInOrder_reached` (Johnson/IMR/AtReach.lean), whose lines on the walk stand here again. A near
relative in this direction, not called: the third clause of `FitAt`
(OnBytes/Tie/Pv/Keeps/FitBook.lean): what a tree holds are numbers of oracle messages: the bound,
not the place.

Limits. `own_of_places`' premise on the places is shown nowhere here. Nothing behind the place
behind the last segment. Nothing on adopting. This file's imports are heavy. Nothing on any
property.

-/
import Johnson.Desc.K2.Honest.Returns.Read
import Johnson.IMR.AtReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (SameNumbers)
open VerifiableInference.Desc.Book (cnt recvP_seat)
open Johnson.Desc.First.Walk.Tied (Reach)
open Meaning.K2 (SeatKeeps PR seatKeeps_front open_fold start_empty frontOf)
open _root_.Tw.K2 (SwIn)
open ProofFile (Cl)

/-- Below the count of a tree's messages every number is the count at one of them. -/
theorem cnt_surj (tree : Array Nat) (τ : Nat) : ∀ (n k : Nat), k < cnt tree τ n →
    ∃ j, j < n ∧ tree.getD j 0 = τ ∧ cnt tree τ j = k
  | 0, k, h => by cases h
  | n + 1, k, h => by
    have e : cnt tree τ (n + 1) = cnt tree τ n + (if tree.getD n 0 = τ then 1 else 0) := rfl
    by_cases hk : k < cnt tree τ n
    · obtain ⟨j, h1, h2, h3⟩ := cnt_surj tree τ n k hk
      exact ⟨j, by omega, h2, h3⟩
    · by_cases ht : tree.getD n 0 = τ
      · rw [e, if_pos ht] at h
        exact ⟨n, by omega, ht, by omega⟩
      · rw [e, if_neg ht] at h
        omega

/-- **Every part of every tree is a message whose place is that tree and that part number.** -/
def partsPlaced (B : TreeBook) (_r : Nat) : Prop :=
  ∀ (τ : Nat) (t : Tree) (k i : Nat), B.trees[τ]? = some t → t.parts[k]? = some i →
    B.place[i]? = some (τ, k)

theorem partsPlaced_recv {L : Type} (d d' : _root_.Desc.Plain.DState L)
    (sent : Array OracleNotice) (ids : Array Nat)
    (h : VerifiableInference.Desc.Ground.recvP 0 d sent = some (ids, d'))
    (hP : partsPlaced d.book d.roots) : partsPlaced d'.book d'.roots := by
  obtain ⟨-, lay, -, Se⟩ := recvP_seat 0 d d' sent ids h
  intro τ t k i ht hk
  by_cases lt : τ < d.book.trees.size
  · rw [Se.trees τ lt] at ht
    have hp := hP τ t k i ht hk
    have hi : i < d.book.place.size := (Array.getElem?_eq_some_iff.1 hp).1
    rw [Se.places i hi]
    exact hp
  · have lt' := (Array.getElem?_eq_some_iff.1 ht).1
    rw [Se.size] at lt'
    obtain ⟨τ', rfl⟩ : ∃ τ', τ = d.book.trees.size + τ' := ⟨τ - d.book.trees.size, by omega⟩
    obtain ⟨t', a, -, -, -, hsz, hparts⟩ := Se.made τ' (by omega)
    obtain rfl : t = t' := Option.some.inj (ht.symm.trans a)
    have hk' : k < cnt lay.tree τ' sent.size := by
      rw [← hsz]
      exact (Array.getElem?_eq_some_iff.1 hk).1
    obtain ⟨j, j1, j2, j3⟩ := cnt_surj lay.tree τ' sent.size k hk'
    have e := hparts j j1 j2
    rw [j3] at e
    obtain rfl : i = d.st.oracles.size + j := Option.some.inj (hk.symm.trans e)
    rw [Se.new j j1, j2, (Se.fits j j1).2, j2, j3]

theorem partsPlaced_same (A B : TreeBook) (r : Nat) (h : SameNumbers A B)
    (k : partsPlaced A r) : partsPlaced B r := by
  intro τ t q i ht hq
  obtain ⟨T₀, h₀, -, -, -, e⟩ := h.2.2 τ t ht
  rw [h.2.1]
  rw [e] at hq
  exact k τ T₀ q i h₀ hq

/-- **At every reached state up to the place behind the last segment.** -/
theorem partsPlaced_reached {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B)
    {k : Nat} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s))
    (hk : k ≤ (frontOf c).length) : partsPlaced s.book s.roots := by
  obtain ⟨-, rs, cols, f⟩ := h.fold
  have K3 : SeatKeeps (PR partsPlaced) := seatKeeps_front
    (fun d d' sent ids e k => partsPlaced_recv d d' sent ids e k) partsPlaced_same
  have hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z := O.pub
  refine open_fold K3 O trivial (fun _ _ _ => trivial) hk f ?_
  show partsPlaced (ProofFile.startS Z z).book (ProofFile.startS Z z).roots
  rw [(start_empty hZ z).1]
  intro τ t q i ht
  simp at ht

/-- **`ReadFits.own` from a sentence on the places.** -/
theorem own_of_places {i : SwIn} {r : Nat} (hP : partsPlaced i.book r)
    (h : ∀ (q τ k : Nat), i.book.place[q]? = some (τ, k) → τ ∈ treesOf i →
      q ∈ (idsOf i).toList) :
    ∀ t ∈ treesOf i, ∀ tree, i.book.trees[t]? = some tree →
      ∀ q ∈ tree.parts.toList, q ∈ (idsOf i).toList := by
  intro t ht tree htree q hq
  obtain ⟨k, hk, e⟩ := List.getElem_of_mem hq
  have hk' : tree.parts[k]? = some q := by
    rw [← Array.getElem?_toList, List.getElem?_eq_getElem hk, e]
  exact h q t k (hP t tree k q htree hk') ht

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.cnt_surj
#print axioms VerifiableInference.Desc.K2.Honest.Returns.partsPlaced_recv
#print axioms VerifiableInference.Desc.K2.Honest.Returns.partsPlaced_same
#print axioms VerifiableInference.Desc.K2.Honest.Returns.partsPlaced_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.own_of_places
