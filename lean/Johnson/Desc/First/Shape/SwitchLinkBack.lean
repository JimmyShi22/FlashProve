-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/SwitchLinkBack.lean: THE CODE SWITCH AT A SEGMENT's FIRST PLACE (kind K2):
THE WAY BACK: THE CLAUSES OF THE LAW's PREMISE THAT READ NO ROUND AND NO COLUMN (LinkPlain,
Johnson/Desc/K2/Honest/Returns/LinkSent.lean) GIVE THE TEST ON THE PLAN's NUMBERS AND THE CHAIN's
SHAPE (linkB, SwitchLinkB.lean) AND THE TEST ON THE ONES (onesV, SwitchFrontFits.lean).
SwitchLinkB.lean has the way there (linkPlain_of_B). General laws; nothing is evaluated.

  `ownB_of`: the clause "own" gives its Bool: the converse of own_of_B.
  `readFitsB_of`: ReadFits' twelve clauses that read no column give readFitsB (SwitchReadFits.lean).
  **`linkB_of_state`**: at a state s, the frame's own segment L and group Q, and the three codes: 21
    premises, each a field of LinkPlain in its own letters, but for two: in the stead of "reads"
    readFitsB at the front's statement, the book and the carried rows; in the stead of "front"
    FrontCore at no position drawn. Then linkB p (chainF s) and onesV s.st s.check.frame.rows
    accept.
  `linkP_of_state`: the further test on the plan and the shape (linkP, SwitchLinkFits.lean) from its
    two look-ups (the frame's group; the carried rows' code) and its six clauses: two in the letters
    of the front's term (seeds, answers), one at the code looked up (logN), one on the plan's number
    of positions alone, two on the book's shape as linkP has them.

Limits. Implications. No state is shown at which the premises hold. Nothing on the rounds or the
columns. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Shape.SwitchLinkFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground.Sh (StSh stSh place_size orc_size tree_get)
open VerifiableInference.Desc.First.K2 (P2 par9)
open VerifiableInference.Desc.First.Send (planOk1)
open VerifiableInference.Desc.K2.Honest.Returns (FrontCore frontAt sendingAt idsOf treesOf shapeAt)
open VerifiableInference.Desc.LinkJoin (ColFits keptCount)
open OnBytes.Params (ReqMessage)
open Johnson.Desc.First.Walk (firstDue)
open _root_.Tw.K2 (Front SwIn switchNotices)

/-- The clause "own" gives its Bool. -/
theorem ownB_of {own : List ReqMessage} {others : Array OracleNotice} {code maskCode : Nat}
    (h : ∀ (j : Nat) (m : ReqMessage), own[j]? = some m →
      ∃ n, others[j]? = some n ∧ n.shape.answers ≠ 0 ∧
        (n.shape.mainRows = 0 ∨ n.shape.code = code) ∧
        (n.shape.maskRows = 0 ∨ n.shape.maskCode = maskCode) ∧
        (0 < m.life → 0 < n.shape.mainRows)) : ownB own others code maskCode = true := by
  unfold ownB
  rw [List.all_eq_true]
  rintro ⟨m, j⟩ hq
  obtain ⟨n, e, a1, a2, a3, a4⟩ := h j m (List.mem_zipIdx_iff_getElem?.1 hq)
  dsimp only
  rw [e]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩

/-- ReadFits' twelve clauses that read no column give the Bool on the three shapes. -/
theorem readFitsB_of (i : SwIn) (masks : i.old.masks = 2)
    (challenges : i.old.gamma.length = i.old.layout.k) (maskVars : i.old.layout.h ≤ i.old.layout.k)
    (keptSize : i.old.layout.kept.size = i.old.layout.members.size)
    (mainSize : i.old.layout.mainFirst.size = i.old.layout.members.size)
    (maskSize : i.old.layout.maskFirst.size = i.old.layout.members.size)
    (placed : ∀ o ∈ (idsOf i).toList, o < i.book.place.size)
    (stated : ∀ o ∈ (idsOf i).toList, o < i.st.oracles.size)
    (own : ∀ t ∈ treesOf i, ∀ tree, i.book.trees[t]? = some tree →
      ∀ q ∈ tree.parts.toList, q ∈ (idsOf i).toList)
    (fits : ∀ w (hw : w < i.old.layout.members.size), ColFits i.old.layout w
      (shapeAt i i.old.layout.members[w]).mainRows (shapeAt i i.old.layout.members[w]).maskRows
      (2 ^ i.old.layout.k) (2 ^ i.old.layout.h))
    (keptRows : keptCount i.old.layout
      (fun w => (shapeAt i (i.old.layout.members.getD w 0)).mainRows)
      (List.range i.old.layout.members.size) = i.old.keptRows)
    (fresh : (shapeAt i i.old.fresh).maskRows = 2 ^ i.old.layout.h) :
    readFitsB (stSh i.st) (Ground.Sh.bookSh i.book) (singleSh i.old) = true := by
  have eS : ∀ o, shapeAtS (stSh i.st) o = shapeAt i o := fun o => (shapeAt_sh i.st o).symm
  have eM : ∀ w (hw : w < i.old.layout.members.size),
      i.old.layout.members.getD w 0 = i.old.layout.members[w] := fun w hw => by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hw]
    rfl
  unfold readFitsB
  rw [trees_sh, ids_sh]
  simp only [eS, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, colFitsB_iff, place_size, orc_size]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨masks, challenges⟩, maskVars⟩, keptSize⟩, mainSize⟩, maskSize⟩, placed⟩,
    stated⟩, fun t ht => ?_⟩, fun w hw => ?_⟩, keptRows⟩, fresh⟩
  · rw [tree_get]
    cases e : i.book.trees[t]? with
    | none => rfl
    | some tree =>
      show (tree.parts.toList.all fun q => (idsOf i).toList.contains q) = true
      rw [List.all_eq_true]
      intro q hq
      exact List.contains_iff_mem.2 (own t ht tree e q hq)
  · have hw' : w < i.old.layout.members.size := hw
    have := fits w hw'
    rw [← eM w hw'] at this
    exact this

/-- **THE CLAUSES THAT READ NO ROUND AND NO COLUMN GIVE THE TEST ON THE PLAN AND THE SHAPE, AND THE
TEST ON THE ONES.** -/
theorem linkB_of_state {p : P2} {s : S} {L : Params.ReqLink} {Q : ReqGroup} {c₀ z₀ c : Code}
    (stands : p.stands = .link) (here : s.here = .between) (due : firstDue s.check = true)
    (waits : s.noneWaits = true) (first : s.check.frame.next = .first)
    (later : s.check.frame.link ≠ 0)
    (link : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q)
    (code : s.st.codes.base[s.check.frame.shape.code]? = some c₀)
    (maskCode : s.st.codes.mask[s.check.frame.shape.maskCode]? = some z₀)
    (shorter : z₀.logN ≤ c₀.logN) (plain : L.plain = 0) (number : s.st.groups.size = p.grp)
    (entry : planOk1 none (switchNotices (frontAt s L Q).T (frontAt s L Q).others)
      (par9 p).eSeed = true)
    (plan : K1.planOkOwn (sendingAt p (frontAt s L Q)) = true)
    (step : (frontAt s L Q).st.oracles.size = s.book.place.size)
    (trees : ((layTrees (sendingAt p (frontAt s L Q)).codes
      (sendingAt p (frontAt s L Q)).sent).getD {}).shapes.size = (par9 p).eSeed.roots)
    (oldCode : (frontAt s L Q).st.codes.base[(frontAt s L Q).f.rows.code]? = some c)
    (reads : readFitsB (stSh (frontAt s L Q).st) (Ground.Sh.bookSh s.book)
      (singleSh s.check.frame.rows) = true)
    (front : FrontCore (frontAt s L Q) c s.check.frame.shape.code [])
    (own : ∀ (j : Nat) (m : Params.ReqMessage), (frontAt s L Q).own[j]? = some m →
      ∃ n, (frontAt s L Q).others[j]? = some n ∧ n.shape.answers ≠ 0 ∧
        (n.shape.mainRows = 0 ∨ n.shape.code = s.check.frame.shape.code) ∧
        (n.shape.maskRows = 0 ∨ n.shape.maskCode = s.check.frame.shape.maskCode) ∧
        (0 < m.life → 0 < n.shape.mainRows)) :
    linkB p (chainF s) = true ∧ onesV s.st s.check.frame.rows = true := by
  have hst : stSh (frontAt s L Q).st = withGroupS (stSh s.st) s.check.frame.shape.code
      s.check.frame.shape.maskCode := withGroup_sh _ _ _
  have hfo : formsOf (frontAt s L Q).st =
      { formsOf s.st with groups := (formsOf s.st).groups ++ [[]] } := withGroup_forms _ _ _
  have hg : (stSh s.st).groups.length = s.st.groups.size := Ground.Sh.grp_size _
  have hF := (frontCore_iffB _ _ _ _).1 front
  rw [Bool.and_eq_true, hst, hfo] at hF
  rw [hst] at reads
  refine ⟨?_, hF.2⟩
  have b2 : ((chainF s).1.here == 0) = true := by
    show (hereNo s.here == 0) = true
    rw [here]
    rfl
  have b9 : (stSh s.st).groups.length = p.grp := hg.trans number
  have b13 : (stSh s.st).oracles.length = (Ground.Sh.bookSh s.book).place.length := by
    rw [orc_size, place_size]
    exact step
  unfold linkB
  split
  · rename_i L' Q' c₀' z₀' c' f1 f2 f3 f4 f5
    obtain rfl : L = L' := Option.some.inj (link.symm.trans f1)
    obtain rfl : Q = Q' := Option.some.inj (group.symm.trans f2)
    obtain rfl : c₀ = c₀' := Option.some.inj (code.symm.trans f3)
    obtain rfl : z₀ = z₀' := Option.some.inj (maskCode.symm.trans f4)
    obtain rfl : c = c' := Option.some.inj (oldCode.symm.trans f5)
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨stands, b2⟩, due⟩, waits⟩, first⟩, later⟩, shorter⟩, plain⟩, b9⟩, entry⟩,
      plan⟩, b13⟩, trees⟩, reads⟩, ownB_of own⟩, hF.1⟩
  · rename_i hne
    exact absurd oldCode (hne L Q c₀ z₀ c link group code maskCode)

/-- The further test on the plan and the shape, from its six clauses. -/
theorem linkP_of_state {p : P2} {s : S} {L : Params.ReqLink} {Q : ReqGroup} {c : Code}
    (group : s.check.frame.groups[s.check.frame.link]? = some Q)
    (oldCode : (frontAt s L Q).st.codes.base[(frontAt s L Q).f.rows.code]? = some c)
    (seeds : p.seeds = (sendingAt p (frontAt s L Q)).seeds *
      ((sendingAt p (frontAt s L Q)).coordinates + 1))
    (answers : p.answers = (sendingAt p (frontAt s L Q)).answers) (logN : p.logN = c.logN)
    (positions : 0 < p.positions)
    (shapes : treesShapeB
      (withGroupS (stSh s.st) s.check.frame.shape.code s.check.frame.shape.maskCode)
      (Ground.Sh.bookSh s.book) c.logN
      (treesOfS (Ground.Sh.bookSh s.book) (singleSh s.check.frame.rows)) = true)
    (read : readsOfS (Ground.Sh.bookSh s.book) p.firstTree
      (treesOfS (Ground.Sh.bookSh s.book) (singleSh s.check.frame.rows)) = some p.read) :
    linkP p (chainF s) = true := by
  unfold linkP
  split
  · rename_i Q' c' f2 f5
    obtain rfl : Q = Q' := Option.some.inj (group.symm.trans f2)
    obtain rfl : c = c' := Option.some.inj (oldCode.symm.trans f5)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨⟨⟨⟨seeds, answers⟩, logN⟩, positions⟩, shapes⟩, read⟩
  · rename_i hne
    exact absurd oldCode (hne Q c group)

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.ownB_of
#print axioms VerifiableInference.Desc.First.Shape.readFitsB_of
#print axioms VerifiableInference.Desc.First.Shape.linkB_of_state
#print axioms VerifiableInference.Desc.First.Shape.linkP_of_state
