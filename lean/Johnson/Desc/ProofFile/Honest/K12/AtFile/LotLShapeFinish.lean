-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLShapeFinish.lean

It states no goal. No property of the protocol is claimed.

«finish_lays»: WHAT THE PLACE OF THE FIRST CHAIN's LAST CODE
SWITCH (`finishPlace`, Johnson/Top/H0/Tw/K2C/Finish.lean) LAYS, BEHIND AN ACCEPT OF ITS DECISION, AS THE LOCAL SHAPE
`ClosingGroupLaid` (LotLShapeLaidForm.lean): the closing group, the message that carries the claim, the fresh mask, their
one tree and two places, each as a whole record's shape, in terms of the state IN FRONT of the place: its counts, its
codes, its frame. General in the state and in the switch's numbers: no size is read, no shape is closed.

  `between_in_front`, `link_in_front`, `mark_kept`   in front of an accept the chain stands between two links and every
                  link of the frame's shape is behind; the place lays and lifts no mark
  `finish_lays`   THE LAW. It also says where the state stands behind the accept: at the finish, with the mask's number
                  and the group's number that `enterFinish` (Johnson/Desc/K12/AtFinish.lean) hands to the test

By what. `finishPlace_cut` (Johnson/Loose/H2K12/GroupAt354.lean); `finishFrontQ_iff`, `finishFront_iff`,
`finishBehindQ_iff` (Johnson/Top/H0/Tw/K2C/Asks.lean), `newGroupG_is` (…/FrontGroup.lean), `finishFrontQ_rest`
(…/FinFront.lean), `finish_inv` (…/Closed.lean); the update on shapes from a yes alone: `switchE_sh`
(Johnson/Desc/First/Shape/Switch.lean); `switchEU_lays` (LotLShapeSwitch.lean).

IMPORTS OF Johnson.Top.H0.*, BY NAME: Johnson.Top.H0.Tw.K2C.FinFront. (Johnson.Loose.H2K12.GroupAt354 imports
Johnson.Top.H0.Tw.K2C.Closed, .Asks, .Finish and Johnson.Top.H0.Walk.Reach.)

Hypotheses, by name, ALL ON THE STATE IN FRONT AND PUBLIC THERE. group: the frame's list of groups has Gr at the frame's
link. noKept, noMaskRows, sampled: Gr's target has no kept member, its shape no mask row and an answer. layout, oneTree,
tree₀ … part₁: the carrier and the fold's mask sit in one new tree at parts 0 and 1. oldBelow: the carried rows' messages
have places in the book in front. placesBelow: each place in front names a tree in front.

Can it be empty. It is idle where the place never accepts. The premises can say no: at a target with kept members the
group gains more than one member.

Limits. How many generator rows are laid stands under ∃. Nothing on what a row holds of. Nothing on completeness,
soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLShapeLaidForm
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLShapeSwitch
import Johnson.Loose.H2K12.GroupAt354
import Johnson.Top.H0.Tw.K2C.FinFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.LotL
open OnBytes (OracleNotice TreeShape TreeLay ReqGroup foldMaskNotice singleRowsOracles)
open VerifiableInference.Desc (Block Own.treesMade Own.padMade)
open VerifiableInference.Desc.Ground.Sh (CoreSh stSh bookSh freshOrc orc_size grp_size tree_size grp_get)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 finishPlace withFresh freshGroup)
open VerifiableInference.Desc.First.Shape (switchEU switchE_sh singleSh formsOf oldOraclesS)

/-- In front of an accept of the place the chain stands between two links. -/
theorem between_in_front (p : P2) {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (accept : (finishPlace p : Block S Unit).decide s rs gs = .ok s') : s.here = .between := by
  obtain ⟨t, _, _, _, h1, -, -, -⟩ := H2K12.finishPlace_cut p accept
  obtain ⟨_, _, _, _, k⟩ := (VerifiableInference.Desc.First.K2.finishFrontQ_iff s t).1 h1
  have hb := k.between
  unfold VerifiableInference.Desc.First.S.atBetween at hb
  cases hh : s.here <;> simp [hh] at hb
  rfl

/-- In front of an accept of the place every link of the frame's shape is behind. -/
theorem link_in_front (p : P2) {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (accept : (finishPlace p : Block S Unit).decide s rs gs = .ok s') :
    s.check.frame.link = s.check.frame.shape.link.length := by
  obtain ⟨t, _, _, _, h1, -, -, -⟩ := H2K12.finishPlace_cut p accept
  obtain ⟨_, _, _, _, k⟩ := (VerifiableInference.Desc.First.K2.finishFrontQ_iff s t).1 h1
  obtain ⟨_, _, _, fa⟩ := (_root_.Tw.K2.finishFront_iff _ _ _).1 k.front
  exact fa.last

/-- The place lays and lifts no mark. -/
theorem mark_kept (p : P2) (hp : p.stands = .finish) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (accept : (finishPlace p : Block S Unit).decide s rs gs = .ok s') : s'.failed = s.failed := by
  obtain ⟨t, t', _, _, h1, h2, h3, -⟩ := H2K12.finishPlace_cut p accept
  obtain ⟨_, _, _, _, _, _, -, F⟩ := VerifiableInference.Desc.First.K2.finish_inv hp h2
  obtain ⟨-, -, -, hfailed, -, -, -⟩ := VerifiableInference.Desc.First.K2.finishFrontQ_rest h1
  obtain ⟨_, _, -, -, rfl⟩ := (VerifiableInference.Desc.First.K2.finishBehindQ_iff t' s').1 h3
  have hout := F.hOut
  subst hout
  exact hfailed

/-- **«finish_lays».** -/
theorem finish_lays (p : P2) (hp : p.stands = .finish) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (accept : (finishPlace p : Block S Unit).decide s rs gs = .ok s') {Gr : ReqGroup}
    (group : s.check.frame.groups[s.check.frame.link]? = some Gr) (noKept : Gr.target.kept = #[])
    (noMaskRows : Gr.target.shape.maskRows = 0) (sampled : Gr.target.shape.answers ≠ 0)
    {lay : TreeLay} {τ : TreeShape}
    (layout : Own.treesMade s.st.codes #[⟨Gr.target.shape, Gr.target.leafClass⟩,
      foldMaskNotice (s.check.frame.foldShape s.check.frame.link {})] = some lay)
    (oneTree : lay.shapes = #[τ]) (tree₀ : lay.tree.getD 0 0 = 0) (tree₁ : lay.tree.getD 1 0 = 0)
    (part₀ : lay.part.getD 0 0 = 0) (part₁ : lay.part.getD 1 0 = 1)
    (oldBelow : ∀ o ∈ (singleRowsOracles s.check.frame.rows).toList, o < s.book.place.size)
    (placesBelow : ∀ (i : ℕ) (q : ℕ × ℕ), s.book.place[i]? = some q → q.1 < s.book.trees.size) :
    ∃ places n o, Own.padMade s.st.codes Gr.target.shape = some places ∧ s'.here = .fin o ∧
      o.mask = some (s.st.oracles.size + 1) ∧ o.fr.group = s.st.groups.size ∧
      s'.st.codes = s.st.codes ∧ s'.roots = s.roots + 1 ∧ s'.failed = s.failed ∧
      ClosingGroupLaid ⟨stSh s'.st, bookSh s'.book, s'.roots⟩ s.st.groups.size s.st.oracles.size
        (s.st.oracles.size + 1) s.book.trees.size
        ⟨s.check.frame.shape.code, s.check.frame.shape.maskCode, [s.st.oracles.size], [false],
          .plain :: List.replicate n .generator, false⟩
        ⟨Gr.target.shape, true, Gr.target.shape.answers, places.map fun x => (x.part, x.index),
          [s.st.groups.size], OnBytes.Slice.freshLedger s.st.codes Gr.target.shape, false⟩
        (freshOrc (foldMaskNotice (s.check.frame.foldShape s.check.frame.link {})))
        ⟨τ, p.firstTree + s.roots, .own s.roots, [s.st.oracles.size, s.st.oracles.size + 1], true,
          0⟩ := by
  obtain ⟨t, t', rs', gs', h1, h2, h3, -⟩ := H2K12.finishPlace_cut p accept
  obtain ⟨r₁, r₂, a, G, w, roots, -, F⟩ := VerifiableInference.Desc.First.K2.finish_inv hp h2
  obtain ⟨ids, e1, -, -, e4⟩ := switchE_sh F.hSwitch
  -- the quiet step in front
  obtain ⟨G₀, x, s₁, a₀, k⟩ := (VerifiableInference.Desc.First.K2.finishFrontQ_iff s t).1 h1
  obtain ⟨G', S', g, fa⟩ := (_root_.Tw.K2.finishFront_iff _ _ _).1 k.front
  obtain ⟨eS, eg⟩ := VerifiableInference.Desc.First.K2.newGroupG_is fa.opened
  obtain ⟨hbook, hroots, -, hfailed, -, -, -⟩ :=
    VerifiableInference.Desc.First.K2.finishFrontQ_rest h1
  have hst : t.st = withFresh s.st s.check.frame.shape.code s.check.frame.shape.maskCode :=
    VerifiableInference.Desc.First.K2.finishFrontQ_st h1
  have ha : a = { a₀ with G := some G₀, fr := x.f } := by
    have e := F.hHere
    rw [k.out] at e
    injection e with e
    exact e.symm
  have hfr : a.fr = { s.check.frame with group := s.st.groups.size, moment := 1, own := #[] } := by
    rw [ha, fa.out, eg]
  obtain rfl : G₀ = Gr := Option.some.inj (k.group.symm.trans group)
  obtain rfl : G₀ = G := by
    have e := F.hLaid
    rw [ha] at e
    exact Option.some.inj e
  -- the update on shapes, at the state in front
  have e1' : switchEU p a.fr.group (singleSh a.fr.rows) G₀.target
      #[foldMaskNotice (a.fr.foldShape a.fr.link {})] ⟨stSh t.st, bookSh t.book, t.roots⟩
      (formsOf t.st) = some (ids, ⟨stSh w.st, bookSh w.book, roots⟩, formsOf w.st) := e1
  rw [hfr, hst, hbook, hroots] at e1'
  have hn : (stSh (withFresh s.st s.check.frame.shape.code
      s.check.frame.shape.maskCode)).oracles.length = s.st.oracles.size := orc_size s.st
  have hfresh : (stSh (withFresh s.st s.check.frame.shape.code
      s.check.frame.shape.maskCode)).groups[s.st.groups.size]? =
      some ⟨s.check.frame.shape.code, s.check.frame.shape.maskCode, [], [], [], false⟩ := by
    rw [grp_get]
    show ((s.st.groups.push (freshGroup _ _))[s.st.groups.size]?).map _ = _
    rw [Array.getElem?_push, if_pos rfl]
    rfl
  have hgl : (stSh (withFresh s.st s.check.frame.shape.code
      s.check.frame.shape.maskCode)).groups.length = s.st.groups.size + 1 := by
    rw [grp_size]
    exact Array.size_push _
  obtain ⟨places, n, hpl, hi, hc, r₁', r₂', r₃, r₄, r₅, r₆, r₇, r₈, r₉, r₁₀⟩ :=
    switchEU_lays (code := s.check.frame.shape.code) (maskCode := s.check.frame.shape.maskCode) e1'
      noKept noMaskRows layout oneTree tree₀ tree₁ part₀ part₁ sampled rfl hfresh (by
        intro o ho q hq
        have ho' : o < s.book.place.size := oldBelow o ho
        have hq' : (s.book.place.toList ++ [((bookSh s.book).trees.length, 0),
            ((bookSh s.book).trees.length, 1)])[o]? = some q := hq
        rw [List.getElem?_append_left (by rw [Array.length_toList]; exact ho'),
          Array.getElem?_toList] at hq'
        have := placesBelow o q hq'
        show q.1 ≠ (bookSh s.book).trees.length
        rw [tree_size]
        omega)
  -- the quiet step behind
  obtain ⟨a', m, ha', hm, rfl⟩ := (VerifiableInference.Desc.First.K2.finishBehindQ_iff t' s').1 h3
  have hout := F.hOut
  subst hout
  obtain rfl : { a with sw := w.out } = a' := by
    have e : VerifiableInference.Desc.First.Here.fin { a with sw := w.out } = .fin a' := ha'
    injection e
  have hm' : w.out.others[0]? = some m := hm
  have hmask : m = s.st.oracles.size + 1 := by
    rw [e4, hi, hn] at hm'
    have e : (VerifiableInference.Desc.First.K2.finFrontOf t a G₀).T.kept = #[] := noKept
    rw [e] at hm'
    simpa using hm'.symm
  have htb : (bookSh s.book).trees.length = s.book.trees.size := tree_size s.book
  simp only [hn, htb] at r₁' r₃ r₄ r₅ r₆ r₇ r₈
  refine ⟨places, n, _, hpl, rfl, by rw [hmask], by
    show a.fr.group = _
    rw [hfr], hc, r₉, hfailed, r₁', r₃, r₄, r₆, ?_, ?_, rfl, r₂'.trans hgl, r₅, ?_, r₇⟩
  · show (bookSh w.book).place[s.st.oracles.size]? = _
    rw [r₈]
    have e : s.st.oracles.size = (bookSh s.book).place.length := hn.symm.trans r₁₀
    rw [e]
    simp
  · show (bookSh w.book).place[s.st.oracles.size + 1]? = _
    rw [r₈]
    have e : s.st.oracles.size = (bookSh s.book).place.length := hn.symm.trans r₁₀
    rw [e]
    simp
  · show (bookSh w.book).place.length = _
    rw [r₈]
    have e : s.st.oracles.size = (bookSh s.book).place.length := hn.symm.trans r₁₀
    rw [e]
    simp

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.between_in_front
#print axioms ProofFile.Honest.K12.LotL.link_in_front
#print axioms ProofFile.Honest.K12.LotL.mark_kept
#print axioms ProofFile.Honest.K12.LotL.finish_lays
