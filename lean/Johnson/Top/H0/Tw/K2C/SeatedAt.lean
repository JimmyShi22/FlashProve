-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/SeatedAt.lean: the kind «the code switch»: WHERE A YES OF THE SWITCH SEATS
ITS NEW MESSAGES IN THE BOOK, AT THE RECORD: the like, for the switch's block, of what the plain
ground's receiving says of its own yes (Johnson/Desc/Book/Seated.lean · BookFitsGround.lean:
recvP_seat). NO BLOCK IMPORTS THIS FILE.
WHY NOT «Seated» ITSELF: Seated asks that every older tree is as it was. The switch reads the old
rows behind its sending and counts, at each tree that it opens, one list more («lists»): so an
older tree can turn in that one field.
  SeatedBut B B' n n0 lay num src   Seated, but that of a tree, older or new, only the number, the
                                    source, the shape and the parts are spoken of
  seated_but    Seated A B … and SameNumbers B C give SeatedBut A C …
  yes_seated    a yes of the decision, at any of its three sorts of place: with the front x that
                the block takes off the record and lay := the program's layTrees at x's codes and
                announcements: SeatedBut from the book in front to the book behind, for as many
                messages as x announces, the first with the number x.st.oracles.size; the new tree
                τ has the number firstTree + (roots + τ) and the source own (roots + τ)
No fence is asked: the layout is the one at the front's own codes and announcements. A frame fact.
No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.SentTrees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (switchNotices sendByL8)
open VerifiableInference.Desc.Book (Seated LayFits cnt)

/-- Seated, but that of a tree only its number, source, shape and parts are spoken of. -/
structure SeatedBut (B B' : TreeBook) (n n0 : Nat) (lay : TreeLay) (num : Nat → Nat)
    (src : Nat → Fmt.Src) : Prop where
  fits : LayFits n lay
  step : n0 = B.place.size
  new : ∀ i, i < n → B'.place[n0 + i]? = some (B.trees.size + lay.tree.getD i 0, lay.part.getD i 0)
  places : ∀ j, j < B.place.size → B'.place[j]? = B.place[j]?
  trees : ∀ j, j < B.trees.size → ∃ t t' : Tree, B.trees[j]? = some t ∧ B'.trees[j]? = some t' ∧
    t'.number = t.number ∧ t'.src = t.src ∧ t'.shape = t.shape ∧ t'.parts = t.parts
  size : B'.trees.size = B.trees.size + lay.shapes.size
  count : B'.place.size = B.place.size + n
  made : ∀ τ, τ < lay.shapes.size → ∃ t : Tree, B'.trees[B.trees.size + τ]? = some t ∧
    t.shape = lay.shapes.getD τ {} ∧ t.number = num τ ∧ t.src = src τ ∧
    t.parts.size = cnt lay.tree τ n ∧
    ∀ j, j < n → lay.tree.getD j 0 = τ → t.parts[cnt lay.tree τ j]? = some (n0 + j)

theorem seated_but {A B C : TreeBook} {n n0 : Nat} {lay : TreeLay} {num : Nat → Nat}
    {src : Nat → Fmt.Src} (St : Seated A B n n0 lay num src) (h : SameNumbers B C) :
    SeatedBut A C n n0 lay num src := by
  have at' : ∀ z, z < B.trees.size → ∃ t t' : Tree, B.trees[z]? = some t ∧ C.trees[z]? = some t' ∧
      t'.number = t.number ∧ t'.src = t.src ∧ t'.shape = t.shape ∧ t'.parts = t.parts := by
    intro z hz
    have hz' : z < C.trees.size := by rw [h.1]; exact hz
    obtain ⟨T₀, h₀, e1, e2, e3, e4⟩ := h.2.2 z _ (Array.getElem?_eq_getElem hz')
    exact ⟨T₀, _, h₀, Array.getElem?_eq_getElem hz', e1, e2, e3, e4⟩
  refine ⟨St.fits, St.step, fun i hi => ?_, fun j hj => ?_, fun j hj => ?_, ?_, ?_, fun τ hτ => ?_⟩
  · rw [h.2.1]
    exact St.new i hi
  · rw [h.2.1]
    exact St.places j hj
  · obtain ⟨t, t', a, b, e⟩ := at' j (by rw [St.size]; omega)
    rw [St.trees j hj] at a
    exact ⟨t, t', a, b, e⟩
  · rw [h.1]
    exact St.size
  · rw [h.2.1]
    exact St.count
  · obtain ⟨t, a, e1, e2, e3, e4, e5⟩ := St.made τ hτ
    obtain ⟨t₀, t', a₀, b, f1, f2, f3, f4⟩ := at' (A.trees.size + τ) (by rw [St.size]; omega)
    obtain rfl : t₀ = t := Option.some.inj (a₀.symm.trans a)
    refine ⟨t', b, f3.trans e1, f1.trans e2, f2.trans e3, by rw [f4]; exact e4, fun j hj hl => ?_⟩
    rw [f4]
    exact e5 j hj hl

/-- **Where a yes of the switch seats its new messages, at the record.** -/
theorem yes_seated {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (h : decideWith sendByL8 p s rs gs = .ok s') :
    ∃ (x : _root_.Tw.K2.Front) (lay : TreeLay), FrontOf p s x ∧
      layTrees x.st.codes (switchNotices x.T x.others) = some lay ∧
      s'.roots = s.roots + lay.shapes.size ∧
      SeatedBut s.book s'.book (switchNotices x.T x.others).size x.st.oracles.size lay
        (fun τ => p.firstTree + (s.roots + τ)) (fun τ => .own (s.roots + τ)) := by
  obtain ⟨r₁, r₂, x, ids, sd, an, took, d', _, hx, hs, hb, hr⟩ := yes_front_book h
  obtain ⟨d₁, h1, b, r⟩ := sendP_book hs
  obtain ⟨_, lay, hl, St⟩ := Desc.Book.recvP_seat _ _ _ _ _ h1
  obtain ⟨lay', hl', hro⟩ := Desc.Book.recvP_roots _ _ _ _ _ h1
  obtain rfl : lay = lay' := Option.some.inj (hl.symm.trans hl')
  rw [b] at hb
  exact ⟨x, lay, hx, hl, by rw [hr, r]; exact hro, seated_but St hb⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.seated_but
#print axioms VerifiableInference.Desc.First.K2.yes_seated
