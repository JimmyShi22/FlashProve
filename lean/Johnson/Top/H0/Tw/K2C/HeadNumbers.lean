-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/HeadNumbers.lean: the kind «the code switch»: WHICH NUMBERS THE OPEN LINK's
FRAME HOLDS BEHIND THE WHOLE PLACE «H:2», AND IN WHICH TREES THESE MESSAGES LIE:
K2C/LinkNumbers.lean's sentences at the head's link. NO BLOCK IMPORTS THIS FILE. At the head's
link the switch lays the numbers that its sending returned into the head's own part of the record
(kept · ids); "H.1.quiet", joined behind it in the same block, makes the frame of them, lays it
into the state of the calls and opens the link with that state: so BEHIND THE PLACE THE LINK IS
OPEN and its own record's frame is spoken of: s'.link? = some L, L.check.frame.
  placeH2_stands    a yes of the whole place: the numbers stand at «head»
  placeH2_frame     a yes of the whole place: s.here = .head a; s'.link? = some L; L.link = P.l;
                    L.check = s'.check; the roots and the book as behind the switch (SeatedBut);
                    L.check.frame.keptBefore and .own as cuts of sentIds; own begins with a.fr.own
  headFrontQ_own    behind "H.0.front" the head's part's frame has no own message yet
  placeH2_kept      the memberships, with a.fr.own = #[]: every o among keptBefore, and every
                    own[j], is n0 + i with i < n
  placeH2_trees     with «as many roots as trees» in front and a.fr.own = #[]: every such o is
                    placed by the book behind in a tree jt.1 with s.roots ≤ jt.1 < s'.roots
A frame fact. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.LinkNumbers
import Johnson.Top.H0.Walk.FrameLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)
open _root_.Tw.K2 (SwIn SwOut switchBehind switchNotices sendByL8 firstFront firstBehind)
open Johnson.Desc.First.Walk (firstKept)

theorem placeH2_stands {p : P2} {n : String} {P : HeadPar} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : ((codeSwitchKind p : Block S Unit).andThen n (headOpened n p.place P)).decide s rs gs = .ok s') :
    p.stands = .head := by
  simp only [Block.andThen] at h
  obtain ⟨m, h₁, h₂⟩ := bindOk h
  have h₁' : decideWith sendByL8 p s _ _ = .ok m := h₁
  obtain ⟨⟨a, ha, _⟩, _, _⟩ := headOpenOpens P m s' h₂
  rcases (stands _ _ _ _ _ _ h₁') with ⟨hp, hb⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨r₁, r₂, x, w, roots, S', f, mine, _, k⟩ := link_inv hp h₁'
    rw [k.hOut] at ha
    have : s.here = .head a := ha
    rw [hb] at this
    cases this
  · exact hp
  · obtain ⟨r₁, r₂, a', G, w, roots, _, k⟩ := finish_inv hp h₁'
    rw [k.hOut] at ha
    cases ha

/-- **The open link's frame behind the whole place «H:2».** -/
theorem placeH2_frame {p : P2} {n : String} {P : HeadPar} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : ((codeSwitchKind p : Block S Unit).andThen n (headOpened n p.place P)).decide s rs gs = .ok s') :
    ∃ (a : HeadOwn) (G : ReqGroup) (lay : TreeLay) (L : LinkCtx), s.here = .head a ∧
      s'.link? = some L ∧ L.link = P.l ∧ L.check = s'.check ∧
      s'.roots = s.roots + lay.shapes.size ∧
      SeatedBut s.book s'.book
        (switchNotices G.target (headFrontOf s a G.target).others).size s.st.oracles.size lay
        (fun τ => p.firstTree + (s.roots + τ)) (fun τ => .own (s.roots + τ)) ∧
      L.check.frame.keptBefore = (sentIds s.st.oracles.size
        (switchNotices G.target (headFrontOf s a G.target).others).size).extract 1
          (1 + G.target.kept.size) ∧
      L.check.frame.own = a.fr.own ++ ((sentIds s.st.oracles.size
        (switchNotices G.target (headFrontOf s a G.target).others).size).extract
          (1 + G.target.kept.size)
          (switchNotices G.target (headFrontOf s a G.target).others).size).extract 0
            (s.check.frame.atMoment 0).length := by
  have hp := placeH2_stands h
  simp only [Block.andThen] at h
  obtain ⟨m, h₁, h₂⟩ := bindOk h
  have h₁' : decideWith sendByL8 p s _ _ = .ok m := h₁
  obtain ⟨r₁, r₂, a, G, w, roots, _, k⟩ := head_inv hp h₁'
  obtain ⟨lay, e1, St, e2, e3⟩ := switch_numbers k.hSwitch
  obtain ⟨a2, st, f, mine, L, out, y, cov, s₁, b, q⟩ := (headOpenQ_iff P m s').1 h₂
  obtain ⟨_, ⟨b', hb', ho⟩, _⟩ := headOpenOpens P m s' h₂
  have ha2 : a2 = { a with kept := w.out.kept, ids := w.out.others } := by
    have e := q.here
    rw [k.hOut] at e
    injection e with e
    exact e.symm
  have hmc : m.check = s.check := by rw [k.hOut]
  obtain ⟨mask, bA⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 q.behind
  obtain ⟨_, _, hL, _⟩ := Johnson.Desc.First.Walk.Law.front_ok q.front
  have hb2 : b' = { b with
      L := L
      F := Johnson.Desc.First.Walk.emptySlots
        (Johnson.Desc.First.Walk.weightsAtZero { trees := P.X.Fp.trees }) P.hp.ns } := by
    have e := hb'
    rw [q.out'] at e
    injection e with e
    exact e.symm
  have hbk := headOpenQ_book h₂
  refine ⟨a, G, lay, L, k.hHere, ?_, by rw [hL], ?_, ?_, ?_, ?_, ?_⟩
  · unfold S.link?
    rw [hb']
    simp only [ho, if_true]
    rw [hb2]
  · rw [hL, q.out']
  · rw [hbk.2, k.hOut]
    exact e1
  · rw [hbk.1, k.hOut]
    exact St
  · rw [hL]
    show f.keptBefore = _
    rw [bA.frame]
    show a2.kept = _
    rw [ha2]
    exact e2
  · rw [hL]
    show f.own = _
    rw [bA.frame]
    show a2.fr.own ++ mine = _
    rw [bA.theOwn, ha2]
    show a.fr.own ++ w.out.others.extract 0 (m.check.frame.atMoment 0).length = _
    rw [hmc, e3]
    rfl

theorem headFrontQ_own {tl : HTailF2} {s s' : S} (h : headFrontQ tl s = .ok s') :
    ∃ a, s'.here = .head a ∧ a.fr.own = #[] := by
  obtain ⟨x, s₁, a, k⟩ := (headFrontQ_iff tl s s').1 h
  obtain ⟨L, G, S0, g, fa⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 k.front
  exact ⟨{ a with fr := x.f }, by rw [k.out], by rw [fa.out]⟩

theorem placeH2_kept {p : P2} {n : String} {P : HeadPar} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : ((codeSwitchKind p : Block S Unit).andThen n (headOpened n p.place P)).decide s rs gs = .ok s')
    (hO : ∀ a, s.here = .head a → a.fr.own = #[]) :
    ∃ (L : LinkCtx) (N : Nat), s'.link? = some L ∧
      (∀ o ∈ L.check.frame.keptBefore.toList, ∃ i, i < N ∧ o = s.st.oracles.size + i) ∧
      ∀ (j o : Nat), L.check.frame.own[j]? = some o → ∃ i, i < N ∧ o = s.st.oracles.size + i := by
  obtain ⟨a, G, lay, L, ha, hL, _, _, _, _, e1, e2⟩ := placeH2_frame h
  refine ⟨L, (switchNotices G.target (headFrontOf s a G.target).others).size, hL, fun o ho => ?_,
    fun j o ho => ?_⟩
  · rw [e1] at ho
    exact mem_sentIds (mem_of_extract (Array.mem_toList_iff.1 ho))
  · have hm : o ∈ L.check.frame.own := by
      obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.1 ho
      exact Array.getElem_mem _
    rw [e2, hO a ha] at hm
    simp only [Array.empty_append] at hm
    exact mem_sentIds (mem_of_extract (mem_of_extract hm))

/-- **In which trees they lie.** -/
theorem placeH2_trees {p : P2} {n : String} {P : HeadPar} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : ((codeSwitchKind p : Block S Unit).andThen n (headOpened n p.place P)).decide s rs gs = .ok s')
    (hO : ∀ a, s.here = .head a → a.fr.own = #[]) (hR : s.roots = s.book.trees.size) :
    ∃ L : LinkCtx, s'.link? = some L ∧
      (∀ o ∈ L.check.frame.keptBefore.toList, ∃ jt : Nat × Nat, s'.book.place[o]? = some jt ∧
        s.roots ≤ jt.1 ∧ jt.1 < s'.roots) ∧
      ∀ (j o : Nat), L.check.frame.own[j]? = some o → ∃ jt : Nat × Nat,
        s'.book.place[o]? = some jt ∧ s.roots ≤ jt.1 ∧ jt.1 < s'.roots := by
  obtain ⟨a, G, lay, L, ha, hL, _, _, er, St, e1, e2⟩ := placeH2_frame h
  have key : ∀ i, i < (switchNotices G.target (headFrontOf s a G.target).others).size →
      ∃ jt : Nat × Nat, s'.book.place[s.st.oracles.size + i]? = some jt ∧ s.roots ≤ jt.1 ∧
        jt.1 < s'.roots := by
    intro i hi
    refine ⟨_, St.new i hi, ?_, ?_⟩
    · show s.roots ≤ s.book.trees.size + _
      omega
    · show s.book.trees.size + lay.tree.getD i 0 < s'.roots
      have := (St.fits i hi).1
      omega
  refine ⟨L, hL, fun o ho => ?_, fun j o ho => ?_⟩
  · rw [e1] at ho
    obtain ⟨i, hi, rfl⟩ := mem_sentIds (mem_of_extract (Array.mem_toList_iff.1 ho))
    exact key i hi
  · have hm : o ∈ L.check.frame.own := by
      obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.1 ho
      exact Array.getElem_mem _
    rw [e2, hO a ha] at hm
    simp only [Array.empty_append] at hm
    obtain ⟨i, hi, rfl⟩ := mem_sentIds (mem_of_extract (mem_of_extract hm))
    exact key i hi

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.placeH2_stands
#print axioms VerifiableInference.Desc.First.K2.placeH2_frame
#print axioms VerifiableInference.Desc.First.K2.headFrontQ_own
#print axioms VerifiableInference.Desc.First.K2.placeH2_kept
#print axioms VerifiableInference.Desc.First.K2.placeH2_trees
