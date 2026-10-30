-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/FitsRide.lean: the kind «the code switch»: THE BOOK's INVARIANT BookFits
(Johnson/Desc/Book/BookFits.lean: every message stands in its tree's list of parts at its own part
number) IS HANDED ON BY WHATEVER SEATS ITS NEW MESSAGES AS SeatedBut SAYS, and so by a yes of the
switch. NO BLOCK IMPORTS THIS FILE.
  fits_ride     BookFits B and SeatedBut B B' n n0 lay num src give BookFits B': from the eight
                fields alone: nothing of the switch, and no routine of the ground, stands in it:
                an older message: its place stays and its tree keeps its parts;
                a new one: it is placed at (old trees + its tree in the layout,
                its part there), and that new tree
                lists it at just that part
  fits_same     BookFits reads no more of a book than
                SameNumbers keeps.
  yes_fits      a yes of the decision, at any of its three sorts of place, hands BookFits on: no
                premise
  yes_places    behind a yes the book has as many places more as the front announces messages, and
                in front the statement and the book were in step
The four quiet steps leave the book whole
(K2C/BookKept.lean).
A frame fact. No
soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.SeatedAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (switchNotices sendByL8)
open VerifiableInference.Desc.Book (BookFits)

theorem fits_ride {B B' : TreeBook} {n n0 : Nat} {lay : TreeLay} {num : Nat → Nat}
    {src : Nat → Fmt.Src} (h : BookFits B) (St : SeatedBut B B' n n0 lay num src) :
    BookFits B' := by
  intro o q ho
  by_cases lt : o < B.place.size
  · rw [St.places o lt] at ho
    obtain ⟨T, hj, hp⟩ := h o q ho
    have hlt : q.1 < B.trees.size := (Array.getElem?_eq_some_iff.1 hj).1
    obtain ⟨t₀, t', a, b, _, _, _, e⟩ := St.trees q.1 hlt
    obtain rfl : T = t₀ := Option.some.inj (hj.symm.trans a)
    exact ⟨t', b, by rw [e]; exact hp⟩
  · have hlt' : o < B'.place.size := (Array.getElem?_eq_some_iff.1 ho).1
    rw [St.count] at hlt'
    obtain ⟨i, rfl⟩ : ∃ i, o = n0 + i := ⟨o - n0, by rw [St.step]; omega⟩
    have hi : i < n := by rw [St.step] at hlt'; omega
    rw [St.new i hi] at ho
    obtain ⟨f1, f2⟩ := St.fits i hi
    obtain ⟨T, a, _, _, _, _, e⟩ := St.made (lay.tree.getD i 0) f1
    obtain rfl := Option.some.inj ho
    refine ⟨T, a, ?_⟩
    show T.parts[lay.part.getD i 0]? = some (n0 + i)
    rw [f2]
    exact e i hi rfl

theorem fits_same {A B : TreeBook} (h : SameNumbers A B) (hA : BookFits A) : BookFits B := by
  intro o q ho
  rw [h.2.1] at ho
  obtain ⟨T, hj, hp⟩ := hA o q ho
  have hlt : q.1 < B.trees.size := by
    rw [h.1]
    exact (Array.getElem?_eq_some_iff.1 hj).1
  obtain ⟨T₀, h₀, _, _, _, e⟩ := h.2.2 q.1 _ (Array.getElem?_eq_getElem hlt)
  obtain rfl : T₀ = T := Option.some.inj (h₀.symm.trans hj)
  exact ⟨_, Array.getElem?_eq_getElem hlt, by rw [e]; exact hp⟩

theorem yes_fits {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (h : decideWith sendByL8 p s rs gs = .ok s') (hs : BookFits s.book) :
    BookFits s'.book := by
  obtain ⟨x, lay, _, _, _, St⟩ := yes_seated h
  exact fits_ride hs St

theorem yes_places {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (h : decideWith sendByL8 p s rs gs = .ok s') :
    ∃ x : _root_.Tw.K2.Front, FrontOf p s x ∧ x.st.oracles.size = s.book.place.size ∧
      s'.book.place.size = s.book.place.size + (switchNotices x.T x.others).size := by
  obtain ⟨x, lay, hx, _, _, St⟩ := yes_seated h
  exact ⟨x, hx, St.step, St.count⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.fits_ride
#print axioms VerifiableInference.Desc.First.K2.fits_same
#print axioms VerifiableInference.Desc.First.K2.yes_fits
#print axioms VerifiableInference.Desc.First.K2.yes_places
