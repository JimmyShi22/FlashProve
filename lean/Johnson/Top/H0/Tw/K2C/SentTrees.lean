-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/SentTrees.lean: the kind «the code switch»: THE TREES THAT A YES OF THE
SWITCH LAYS INTO THE BOOK ARE THE ONES THAT THE BLOCK DECLARES, ROOT BY ROOT. NO BLOCK IMPORTS
THIS FILE.
WHY: the block declares to the fold, beneath the roots of its first round, a list of oracle
messages (k2_oracles: p.sent). No law tied that list to the roots that the chain receives in that
round.
  yes_front_book  a yes of the decision: the front x that the block takes off the record
                  (FrontOf), sendP's yes at x, and from what sendP returns to the record behind:
                  SameNumbers and the count of roots
  sent_trees      INSIDE THE FENCE (the front's announcements are «sent», its codes «codes»), with
                  lay := the program's layTrees at these: behind a yes the book has
                  lay.shapes.size trees more and the record as many roots more; the τ-th new tree
                  stands at place (old number of trees) + τ, has the layout's τ-th shape, the
                  number firstTree + (old roots + τ) and THE SOURCE «own (old roots + τ)»: the
                  chain's root number (old roots + τ), which is the τ-th root of this round
  Declares        what is asked of the declared list: as long as the layout, and member by member
                  the layout's length and width
  declared_trees  with Declares: the τ-th DECLARED message has the length and the width of the
                  tree whose source is the τ-th root received
  yes_numbered    «as many roots as trees; the tree at place j has the number firstTree + j and
                  the source own j» is handed on by a yes of the switch: NO PREMISE ON recvP IS
                  LEFT (Johnson/Desc/Book/BookNumbers.lean's recvP_numbered pays it)
LIMITS. The fence is a premise (K2C/SendsOn.lean). Declares is a premise here: that the lot's own
maker of p.sent (Johnson/Desc/ProofFile/Lot/K2OfPlan.lean: oraclesAt) meets it is not proved in
this file. Of a declared message's TENANTS nothing is said. That the view's τ-th
root of the round is what the fold absorbs and opens under «own (roots + τ)» is the fold's own
matter. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.BookKept
import Johnson.Top.H0.Tw.K2C.SendsOn
import Johnson.Desc.Book.BookNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (SwIn SwOut switchBehind switchNotices sendByL8)

theorem yes_front_book {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (h : decideWith sendByL8 p s rs gs = .ok s') :
    ∃ (r₁ r₂ : Fmt.RoundView) (x : _root_.Tw.K2.Front), ∃ ids sd an took d', rs = [r₁, r₂] ∧
      FrontOf p s x ∧
      Desc.Plain.sendP (Desc.Plain.groundG : Desc.Plain.Ground Unit) ⟨p.samples, p.firstTree⟩ false
        ⟨x.st, s.book, s.roots, [], ()⟩ (switchNotices x.T x.others) r₁ r₂ =
          some (ids, sd, an, took, d') ∧
      SameNumbers d'.book s'.book ∧ s'.roots = d'.roots := by
  have key : ∀ {f : ReqFrame} {x : _root_.Tw.K2.Front} {r₁ r₂ : Fmt.RoundView} {w : SwOut} {roots : Nat},
      _root_.Tw.K2.switchE switchBehind (par9 p) sendByL8 ⟨s.st, s.book, s.roots, f, [],
          s.noneWaits⟩
        x r₁ r₂ (flat p gs) = .ok (w, roots) →
      ∃ ids sd an took d', Desc.Plain.sendP (Desc.Plain.groundG : Desc.Plain.Ground Unit)
        ⟨p.samples, p.firstTree⟩ false ⟨x.st, s.book, s.roots, [], ()⟩ (switchNotices x.T x.others)
          r₁ r₂ = some (ids, sd, an, took, d') ∧
      SameNumbers d'.book w.book ∧ roots = d'.roots := by
    intro f x r₁ r₂ w roots hw
    obtain ⟨y, k⟩ := switchE_inv hw
    obtain ⟨ids, took, d', hs, rfl⟩ := (sendByL8_iff _ _ _ _ _ _ _ _ _).1 k.hSend
    obtain ⟨_, _, sd, an, hx⟩ := (sendOpen_iff _ _ _ _ _ _ _ _ _ _ _).1 hs
    exact ⟨ids, sd, an, took, d', hx, switchBehind_same k.hBehind, k.hRoots⟩
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨r₁, r₂, x, w, roots, S', f, mine, rfl, k⟩ := link_inv hp h
    obtain ⟨ids, sd, an, took, d', h1, h2⟩ := key k.hSwitch
    refine ⟨r₁, r₂, x, ids, sd, an, took, d', rfl, Or.inl ⟨hp, k.hFront⟩, h1, ?_⟩
    rw [k.hOut]
    exact h2
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := head_inv hp h
    obtain ⟨ids, sd, an, took, d', h1, h2⟩ := key k.hSwitch
    refine ⟨r₁, r₂, _, ids, sd, an, took, d', rfl,
      Or.inr (Or.inl ⟨hp, a, G, k.hHere, k.hGroup, rfl⟩), h1, ?_⟩
    rw [k.hOut]
    exact h2
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := finish_inv hp h
    obtain ⟨ids, sd, an, took, d', h1, h2⟩ := key k.hSwitch
    refine ⟨r₁, r₂, _, ids, sd, an, took, d', rfl,
      Or.inr (Or.inr ⟨hp, a, G, k.hHere, k.hLaid, rfl⟩), h1, ?_⟩
    rw [k.hOut]
    exact h2

/-- **The trees that a yes of the switch lays, root by root.** -/
theorem sent_trees {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} {sent : Array OracleNotice} {codes : Codes} {n₀ : Nat} {lay : TreeLay}
    (hF : Fence p sent codes n₀ s) (hL : layTrees codes sent = some lay)
    (h : decideWith sendByL8 p s rs gs = .ok s') :
    s'.book.trees.size = s.book.trees.size + lay.shapes.size ∧
    s'.roots = s.roots + lay.shapes.size ∧
    ∀ τ, τ < lay.shapes.size → ∃ T : Tree, s'.book.trees[s.book.trees.size + τ]? = some T ∧
      T.shape = lay.shapes.getD τ {} ∧ T.number = p.firstTree + (s.roots + τ) ∧
      T.src = .own (s.roots + τ) := by
  obtain ⟨r₁, r₂, x, ids, sd, an, took, d', _, hx, hs, hb, hr⟩ := yes_front_book h
  obtain ⟨e1, e2, _⟩ := hF x hx
  obtain ⟨d₁, h1, b, r⟩ := sendP_book hs
  rw [e1] at h1
  obtain ⟨_, lay', hl', St⟩ := Desc.Book.recvP_seat _ _ _ _ _ h1
  obtain ⟨lay'', hl'', hro⟩ := Desc.Book.recvP_roots _ _ _ _ _ h1
  have hl1 : layTrees codes sent = some lay' := by rw [← e2]; exact hl'
  have hl2 : layTrees codes sent = some lay'' := by rw [← e2]; exact hl''
  obtain rfl : lay = lay' := Option.some.inj (hL.symm.trans hl1)
  obtain rfl : lay = lay'' := Option.some.inj (hL.symm.trans hl2)
  have hsz : s'.book.trees.size = s.book.trees.size + lay.shapes.size := by
    rw [hb.1, b]
    exact St.size
  refine ⟨hsz, by rw [hr, r]; exact hro, fun τ hτ => ?_⟩
  obtain ⟨t, a, e3, e4, e5, _, _⟩ := St.made τ hτ
  have hlt : s.book.trees.size + τ < s'.book.trees.size := by omega
  obtain ⟨T₀, h₀, n, sr, sh, _⟩ := hb.2.2 _ _ (Array.getElem?_eq_getElem hlt)
  rw [b] at h₀
  obtain rfl : T₀ = t := Option.some.inj (h₀.symm.trans a)
  exact ⟨_, Array.getElem?_eq_getElem hlt, sh.trans e3, n.trans e4, sr.trans e5⟩

/-- What is asked of the list that the block declares beneath its first round's roots. -/
def Declares (p : P2) (lay : TreeLay) : Prop :=
  p.sent.length = lay.shapes.size ∧
    ∀ τ o, p.sent[τ]? = some o → o.logLength = (lay.shapes.getD τ {}).logN ∧
      o.words = (lay.shapes.getD τ {}).mainWidth + (lay.shapes.getD τ {}).maskWidth

theorem declared_trees {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} {sent : Array OracleNotice} {codes : Codes} {n₀ : Nat} {lay : TreeLay}
    (hF : Fence p sent codes n₀ s) (hL : layTrees codes sent = some lay) (hD : Declares p lay)
    (h : decideWith sendByL8 p s rs gs = .ok s') :
    ∀ τ o, p.sent[τ]? = some o → ∃ T : Tree, s'.book.trees[s.book.trees.size + τ]? = some T ∧
      T.src = .own (s.roots + τ) ∧ T.number = p.firstTree + (s.roots + τ) ∧
      o.logLength = T.shape.logN ∧ o.words = T.shape.mainWidth + T.shape.maskWidth := by
  intro τ o ho
  have hτ : τ < lay.shapes.size := by
    rw [← hD.1]
    exact (List.getElem?_eq_some_iff.1 ho).1
  obtain ⟨T, hT, e1, e2, e3⟩ := (sent_trees hF hL h).2.2 τ hτ
  obtain ⟨d1, d2⟩ := hD.2 τ o ho
  exact ⟨T, hT, e3, e2, by rw [e1]; exact d1, by rw [e1]; exact d2⟩

/-- **The book's order is handed on by a yes of the switch**, with no premise on the receiving. -/
theorem yes_numbered {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (h : decideWith sendByL8 p s rs gs = .ok s')
    (hs : s.roots = s.book.trees.size ∧
      ∀ (j : Nat) (t : Tree),
          s.book.trees[j]? = some t → t.number = p.firstTree + j ∧ t.src = .own j) :
    s'.roots = s'.book.trees.size ∧
      ∀ (j : Nat) (t : Tree), s'.book.trees[j]? = some t →
        t.number = p.firstTree + j ∧ t.src = .own j :=
  yes_hands (P := fun B r => r = B.trees.size ∧
      ∀ (j : Nat) (t : Tree), B.trees[j]? = some t → t.number = p.firstTree + j ∧ t.src = .own j)
    (fun d d₁ sent ids hr hP => Desc.Book.recvP_numbered p.firstTree d d₁ sent ids hr hP)
    (fun A B r hAB hA => ⟨hA.1.trans hAB.1.symm, fun j t ht => by
      obtain ⟨T₀, h₀, n, sr, _⟩ := hAB.2.2 j t ht
      rw [n, sr]
      exact hA.2 j T₀ h₀⟩)
    h hs

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.sent_trees
#print axioms VerifiableInference.Desc.First.K2.declared_trees
#print axioms VerifiableInference.Desc.First.K2.yes_numbered
