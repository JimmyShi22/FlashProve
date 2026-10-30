-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Book/LastSeats.lean: the book of commitment trees numbers the oracle messages as a list
of seats does, wherever the book's trees are numbered by their places, its two tables fit, and its
places are the list's first entries. Five theorems. Joinings and one induction on a list.

Why. The last table's reader of OOD samples finds a message of the first chain by its seat's first
place in a list of seats. It asks of the book that the first chain hands on: if the message number i
has the seat w, then w stands in the list, and first at place i.

What is said.
  `idxOf_of_first`: where a list holds a at place i and at no place in front, `idxOf a` is i.
  `prefix_of_carried`: an accept of `K12.Door.seatsCarriedB L B` gives that B's places are the first
    entries of `L.places`.
  `seatsNumber_of_prefix`: `NumberedBook 0 B`, `BookFits B` and "B's places are the first entries of
    seats" give: `seatBy noFirst B i = some w → w ∈ seats ∧ seats.idxOf w = i`. THE LIST NEED NOT BE
    FREE OF REPEATS: in a book that fits no two messages have one place (`places_inj`), and only the
    list's entries in front of i are asked.
  `seatsNumber_of_carried`: the same at seats := `L.places`, from the three tests' accepts.
  `hS_of_five`: at every `get` and Rc: where Rc gives a condition E on `get q`, and E with "no mark"
    gives the two tests on the book, the equal counts, a fact X and `atFirstSeats L`: for every f
    that `firstOfS (get q).2` hands on, f's book numbers the messages as `L.places` does.

Limits. That any state passes the tests is not shown here. That `L.places` is the list of seats at
which a reader stands is not shown here. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Book.LastBook
import Johnson.Desc.Third.Border

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Book
open OnBytes
open VerifiableInference.Desc.Sound (NumberedBook bookFitsB bookFitsB_iff seatBy noFirst)
open VerifiableInference.Desc.K12.Door (atFirstBook atFirstSeats seatsCarriedB Laid)
open VerifiableInference.Desc.Third (firstOfS)

/-- Where a list holds a at place i and at no place in front, i is a's first place. -/
theorem idxOf_of_first {α : Type} [BEq α] [LawfulBEq α] (a : α) :
    ∀ (l : List α) (i : Nat), l[i]? = some a → (∀ j, j < i → l[j]? ≠ some a) → l.idxOf a = i
  | [], i, h, _ => by simp at h
  | b :: l, 0, h, _ => by
    have e : b = a := by simpa using h
    rw [List.idxOf_cons]
    simp [e]
  | b :: l, i + 1, h, hm => by
    have e : b ≠ a := fun e => hm 0 (Nat.succ_pos i) (by simp [e])
    have e' : (b == a) = false := by simpa using e
    rw [List.idxOf_cons]
    simp only [e', cond_false]
    have := idxOf_of_first a l i (by simpa using h)
      (fun j hj hh => hm (j + 1) (by omega) (by simpa using hh))
    omega

/-- The test's accept: the book's places are the first entries of the list of places. -/
theorem prefix_of_carried (L : Laid) (B : TreeBook) (h : seatsCarriedB L B = true) :
    B.place.toList = L.places.take B.place.size := by
  unfold seatsCarriedB at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h.1.1.1

/-- **The book numbers the messages as the list of seats does.** -/
theorem seatsNumber_of_prefix (seats : List (Nat × Nat)) (B : TreeBook) (hN : NumberedBook 0 B)
    (hF : BookFits B) (hP : B.place.toList = seats.take B.place.size) :
    ∀ i w, seatBy noFirst B i = some w → w ∈ seats ∧ seats.idxOf w = i := by
  intro i w h
  have hp : B.place[i]? = some w := by
    unfold seatBy at h
    cases hq : B.place[i]? with
    | none =>
      rw [hq] at h
      cases h
    | some p =>
      rw [hq] at h
      have h' : (B.trees[p.1]?).map (fun T => (noFirst p.1 T, p.2)) = some w := h
      obtain ⟨T, hT, e⟩ := Option.map_eq_some_iff.1 h'
      have e' : (T.number, p.2) = w := e
      rw [hN p.1 T hT, Nat.zero_add] at e'
      rw [← e']
  have at_ : ∀ k, k < B.place.size → seats[k]? = B.place[k]? := fun k hk => by
    rw [← Array.getElem?_toList, hP, List.getElem?_take_of_lt hk]
  have hi : i < B.place.size := (Array.getElem?_eq_some_iff.1 hp).1
  have hs : seats[i]? = some w := by rw [at_ i hi, hp]
  refine ⟨List.mem_of_getElem? hs, idxOf_of_first w seats i hs fun j hj hh => ?_⟩
  have hj' : B.place[j]? = some w := by rw [← at_ j (by omega), hh]
  have := places_inj hF hj' hp
  omega

/-- The same at the list of places that the book carries, from the three tests' accepts. -/
theorem seatsNumber_of_carried (L : Laid) (s : First.S) (h1 : atFirstBook 0 s = true)
    (h2 : bookFitsB s.book = true) (h3 : s.book.place.size = s.st.oracles.size)
    (h5 : atFirstSeats L s = true) :
    ∀ i w, seatBy noFirst s.book i = some w → w ∈ L.places ∧ L.places.idxOf w = i :=
  seatsNumber_of_prefix L.places s.book (book_of_three s h1 h2 h3).1 (book_of_three s h1 h2 h3).2.1
    (prefix_of_carried L s.book h5)

/-- **At what the first chain hands on, from a walk's end.** -/
theorem hS_of_five {P S₁ P₀ : Type} (get : P × S₁ → P₀ × First.S) (Rc : P × S₁ → Prop)
    (E : P₀ × First.S → Prop) (hE : ∀ q, Rc q → E (get q)) {X : P₀ × First.S → Prop} (L : Laid)
    (H5 : ∀ p : P₀ × First.S, E p → p.2.failed = none →
      atFirstBook 0 p.2 = true ∧ bookFitsB p.2.book = true ∧
        p.2.book.place.size = p.2.st.oracles.size ∧ X p ∧ atFirstSeats L p.2 = true) :
    ∀ q, Rc q → (get q).2.failed = none → ∀ f, firstOfS (get q).2 = some f →
      ∀ i w, seatBy noFirst f.book i = some w → w ∈ L.places ∧ L.places.idxOf w = i := by
  intro q hq hm f hf
  have eb : f.book = (get q).2.book := by
    unfold firstOfS at hf
    obtain ⟨e, _, rfl⟩ := Option.map_eq_some_iff.1 hf
    rfl
  rw [eb]
  have H := H5 _ (hE q hq) hm
  exact seatsNumber_of_carried L _ H.1 H.2.1 H.2.2.1 H.2.2.2.2

end VerifiableInference.Desc.Book
