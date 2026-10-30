-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/LinkNumbers.lean: the kind «the code switch»: WHICH NUMBERS THE FRAME's
LISTS HOLD BEHIND THE SWITCH AT A LINK, AND IN WHICH TREES THESE MESSAGES LIE. NO BLOCK IMPORTS
THIS FILE. The sending of the switch brings in n messages, numbered n0, n0 + 1, …, n0 + n − 1 (n0:
the front's statement's number of messages): g first, then the copies of the kept messages, then
the others: the link's own messages of moment 0, then the fresh mask. AT WHICH RECORD: the record
s' behind the switch's own block at a link's first place: there the frame stands in s'.check.frame
and NO LINK IS OPEN (s'.here = .between: the switch leaves «here»): the frames' step «opened»,
which is joined behind, carries the state of the calls into the link's own record.
  sentIds n0 n         the numbers n0, …, n0 + n − 1
  switch_numbers     a yes of the switch itself: what it returns: kept := the numbers 1 … K of the
                     sending, others := the rest; with SeatedBut from the book in front to the
                     book behind
  yes_link_frame     a yes of the decision at a link: s'.check.frame.keptBefore, .own, .mask and
                     s'.check.sent, each as a cut of sentIds; x.own = the frame's messages of moment
                     0; s'.here = .between
  yes_link_kept · yes_link_own   the memberships: every o among keptBefore, and every own[j], is
                                 n0 + i with i < n
  yes_link_trees     with «as many roots as trees» in front: every such o is placed by the book
                     behind in a tree jt.1 with s.roots ≤ jt.1 < s'.roots: a tree of this very
                     sending
A frame fact. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.SeatedAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (SwIn SwOut switchBehind switchNotices sendByL8 firstFront firstBehind)
open Johnson.Desc.First.Walk (firstKept)

/-- The numbers of a sending of n messages behind n0 messages. -/
def sentIds (n0 n : Nat) : Array Nat := (Array.range n).map (· + n0)

theorem mem_sentIds {n0 n o : Nat} (h : o ∈ sentIds n0 n) : ∃ i, i < n ∧ o = n0 + i := by
  unfold sentIds at h
  simp only [Array.mem_map, Array.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨i, hi, Nat.add_comm _ _⟩

theorem mem_of_extract {α : Type} {xs : Array α} {a b : Nat} {o : α} (h : o ∈ xs.extract a b) :
    o ∈ xs := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 h
  rw [Array.getElem_extract]
  exact Array.getElem_mem _

/-- A yes of the switch itself. -/
theorem switch_numbers {p : P2} {s : S} {f : ReqFrame} {x : _root_.Tw.K2.Front} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {w : SwOut} {roots : Nat}
    (hw : _root_.Tw.K2.switchE switchBehind (par9 p) sendByL8
      ⟨s.st, s.book, s.roots, f, [], s.noneWaits⟩ x r₁ r₂ (flat p gs) = .ok (w, roots)) :
    ∃ lay : TreeLay, roots = s.roots + lay.shapes.size ∧
      SeatedBut s.book w.book (switchNotices x.T x.others).size x.st.oracles.size lay
        (fun τ => p.firstTree + (s.roots + τ)) (fun τ => .own (s.roots + τ)) ∧
      w.out.kept = (sentIds x.st.oracles.size (switchNotices x.T x.others).size).extract 1
        (1 + x.T.kept.size) ∧
      w.out.others = (sentIds x.st.oracles.size (switchNotices x.T x.others).size).extract
        (1 + x.T.kept.size) (switchNotices x.T x.others).size := by
  obtain ⟨y, k⟩ := switchE_inv hw
  obtain ⟨ids, took, d', hs, rfl⟩ := (sendByL8_iff _ _ _ _ _ _ _ _ _).1 k.hSend
  obtain ⟨_, _, sd, an, hx⟩ := (sendOpen_iff _ _ _ _ _ _ _ _ _ _ _).1 hs
  obtain ⟨d₁, h1, b, r⟩ := sendP_book hx
  obtain ⟨hid, lay, hl, St⟩ := Desc.Book.recvP_seat _ _ _ _ _ h1
  obtain ⟨lay', hl', hro⟩ := Desc.Book.recvP_roots _ _ _ _ _ h1
  obtain rfl : lay = lay' := Option.some.inj (hl.symm.trans hl')
  obtain ⟨c, Y, S1, S2, S3, rows, bh⟩ := switchBehind_inv k.hBehind
  have sb := switchBehind_same k.hBehind
  have sb' : SameNumbers d₁.book w.book := by
    rw [← b]
    exact sb
  have hsz : ids.size = (switchNotices x.T x.others).size := by
    rw [hid]
    simp
  refine ⟨lay, ?_, seated_but St sb', ?_, ?_⟩
  · rw [k.hRoots]
    show d'.roots = _
    rw [r]
    exact hro
  · rw [bh.hOut]
    show ids.extract 1 (1 + x.T.kept.size) = _
    rw [hid]
    rfl
  · rw [bh.hOut]
    show ids.extract (1 + x.T.kept.size) ids.size = _
    rw [hsz, hid]
    rfl

/-- **The frame behind the switch at a link.** -/
theorem yes_link_frame {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (hp : p.stands = .link) (h : decideWith sendByL8 p s rs gs = .ok s') :
    ∃ (x : _root_.Tw.K2.Front) (lay : TreeLay), firstFront s.st s.check.frame = .ok x ∧
      x.own = s.check.frame.atMoment 0 ∧ s'.here = .between ∧
      s'.roots = s.roots + lay.shapes.size ∧
      SeatedBut s.book s'.book (switchNotices x.T x.others).size x.st.oracles.size lay
        (fun τ => p.firstTree + (s.roots + τ)) (fun τ => .own (s.roots + τ)) ∧
      s'.check.frame.keptBefore = (sentIds x.st.oracles.size (switchNotices x.T
          x.others).size).extract
        1 (1 + x.T.kept.size) ∧
      s'.check.frame.own = ((sentIds x.st.oracles.size (switchNotices x.T x.others).size).extract
        (1 + x.T.kept.size) (switchNotices x.T x.others).size).extract 0 x.own.length ∧
      s'.check.sent = s'.check.frame.own ∧ s'.check.frame.own.size = x.own.length := by
  obtain ⟨r₁, r₂, x, w, roots, S', f, mine, rfl, k⟩ := link_inv hp h
  obtain ⟨lay, e1, St, e2, e3⟩ := switch_numbers k.hSwitch
  obtain ⟨L, G, S0, g, a⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 k.hFront
  obtain ⟨mask, bA⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 k.hBehind
  have hxo : x.f.own = #[] := by rw [a.out]
  have hf1 : f.keptBefore = w.out.kept := by rw [bA.frame]
  have hf2 : f.own = mine := by
    rw [bA.frame]
    show x.f.own ++ mine = mine
    rw [hxo]
    simp
  refine ⟨x, lay, k.hFront, by rw [a.out], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k.hOut]
    exact k.hHere
  · rw [k.hOut]
    exact e1
  · rw [k.hOut]
    exact St
  · rw [k.hOut]
    show f.keptBefore = _
    rw [hf1, e2]
  · rw [k.hOut]
    show f.own = _
    rw [hf2, bA.theOwn, e3]
  · rw [k.hOut]
    rfl
  · rw [k.hOut]
    show f.own.size = _
    rw [hf2]
    exact bA.own.symm

theorem yes_link_kept {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (hp : p.stands = .link) (h : decideWith sendByL8 p s rs gs = .ok s') :
    ∃ x : _root_.Tw.K2.Front, firstFront s.st s.check.frame = .ok x ∧
      (∀ o ∈ s'.check.frame.keptBefore.toList, ∃ i, i < (switchNotices x.T x.others).size ∧
        o = x.st.oracles.size + i) ∧
      ∀ (j o : Nat), s'.check.frame.own[j]? = some o → ∃ i, i < (switchNotices x.T x.others).size ∧
        o = x.st.oracles.size + i := by
  obtain ⟨x, lay, hx, _, _, _, _, e1, e2, _, _⟩ := yes_link_frame hp h
  refine ⟨x, hx, fun o ho => ?_, fun j o ho => ?_⟩
  · rw [e1] at ho
    exact mem_sentIds (mem_of_extract (Array.mem_toList_iff.1 ho))
  · have hm : o ∈ s'.check.frame.own := by
      obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.1 ho
      exact Array.getElem_mem _
    rw [e2] at hm
    exact mem_sentIds (mem_of_extract (mem_of_extract hm))

/-- **In which trees they lie.** -/
theorem yes_link_trees {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (hp : p.stands = .link) (h : decideWith sendByL8 p s rs gs = .ok s')
    (hR : s.roots = s.book.trees.size) :
    (∀ o ∈ s'.check.frame.keptBefore.toList, ∃ jt : Nat × Nat, s'.book.place[o]? = some jt ∧
      s.roots ≤ jt.1 ∧ jt.1 < s'.roots) ∧
    ∀ (j o : Nat), s'.check.frame.own[j]? = some o → ∃ jt : Nat × Nat,
      s'.book.place[o]? = some jt ∧ s.roots ≤ jt.1 ∧ jt.1 < s'.roots := by
  obtain ⟨x, lay, hx, _, _, er, St, e1, e2, _, _⟩ := yes_link_frame hp h
  have key : ∀ i, i < (switchNotices x.T x.others).size → ∃ jt : Nat × Nat,
      s'.book.place[x.st.oracles.size + i]? = some jt ∧ s.roots ≤ jt.1 ∧ jt.1 < s'.roots := by
    intro i hi
    refine ⟨_, St.new i hi, ?_, ?_⟩
    · show s.roots ≤ s.book.trees.size + _
      omega
    · show s.book.trees.size + lay.tree.getD i 0 < s'.roots
      have := (St.fits i hi).1
      omega
  refine ⟨fun o ho => ?_, fun j o ho => ?_⟩
  · rw [e1] at ho
    obtain ⟨i, hi, rfl⟩ := mem_sentIds (mem_of_extract (Array.mem_toList_iff.1 ho))
    exact key i hi
  · have hm : o ∈ s'.check.frame.own := by
      obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.1 ho
      exact Array.getElem_mem _
    rw [e2] at hm
    obtain ⟨i, hi, rfl⟩ := mem_sentIds (mem_of_extract (mem_of_extract hm))
    exact key i hi

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.switch_numbers
#print axioms VerifiableInference.Desc.First.K2.yes_link_frame
#print axioms VerifiableInference.Desc.First.K2.yes_link_kept
#print axioms VerifiableInference.Desc.First.K2.yes_link_trees
