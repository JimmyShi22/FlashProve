-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Walk/Shape/FrameChain.lean: the link's frame (Johnson/Desc/First/Walk/Frame.lean)
against the shape of the first chain's state (chainSh, Johnson/Desc/First/Shape/Chain.lean): for
"laid" (layFront) and for "opened" at a layers' link behind link 0 (openLay) and at an attention
link (openAtt): ONE STEP ON THE SHAPE each, and two laws. General laws; nothing is evaluated.

The two laws, for a text f : S → Except String S and a step g on shapes:
  "carries": f s = .ok t and g (chainSh s) = .ok u give u = chainSh t.
  "returns": g (chainSh s) = .ok u gives a t with f s = .ok t. NO TEST ON VALUES STANDS IN THESE
  TEXTS: every guard is on numbers and marks that the shape holds.

  `laidG l`: no link is open · no link runs and one is still to come · the chain stands at link l:
    the shape is handed on. **`laid_carries`**, **`laid_returns`**.
  `openB l kind`: no link is open · the link's first call has run · no mark of failure · the number
    of plain scalars is the kind's · the chain stands at link l.
  `enterSh here t L X l a`: THE PLAN's NUMBERS ENTER THE SHAPE HERE: where the chain stands; the
    shape of the plan's structure of the smallness test; THE FRESH LEDGER's SHAPE, FROM NUMBERS
    (LedSh.fresh, Johnson/Desc/First/Shape/Fresh.lean); the link's context.
  `openLayG P`, `openAttG P`: the two steps. **`openLay_carries`**, **`openLay_returns`** (under the
    sub-protocol's own test on the plan, planLay), **`openAtt_carries`**, **`openAtt_returns`**
    (under planAtt).

By the library's equivalences layFront_iff, openLay_iff, openAtt_iff, layFirstQuiet_iff,
attFirstQuiet_iff (Johnson/Top/H0/Walk/FrameProps.lean) and S.unmarked_ok.

Limits. Link 0's "opened" (openLayZero), the head's link, and "cleared" are not here. The texts are
the bare ones: in a seated chain "laid" is asked together with "no mark" and the wrapper's
comparison, and "opened" is joined behind the link's first sub-protocol under that wrapper. That a
step returns at a shape that the chain reaches is not shown. "Carries" is under the step's own
return. The two "opened" steps hold none of the tests on the plan: that is why "returns" has its
premise, of which openAtt_returns spends one clause and openLay_returns four of six. enterSh leaves
tables, look, lookHeard, own, head and fin as they stand: right at a state's shape between two
links. openB here is another thing than First.Shape.openB. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.First.Shape.Chain
import Johnson.Desc.First.Shape.Fresh
import Johnson.Top.H0.Walk.FrameProps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S Here)
open VerifiableInference.Desc.First.Shape
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Props

/-! ## 1 Readers -/

theorem here_between (s : S) : ((chainSh s).here == 0) = s.atBetween := by
  show (hereNo s.here == 0) = s.atBetween
  unfold S.atBetween hereNo
  cases s.here with
  | head a => by_cases h : a.opened = true <;> simp [h]
  | _ => rfl

theorem marked_sh (s : S) : (chainSh s).marked = s.failed.isSome := rfl

theorem check_sh (s : S) : (chainSh s).check = checkSh s.check := rfl

/-! ## 2 "laid" -/

/-- The test. -/
def laidB (l : Nat) (a : ChainSh) : Bool :=
  a.here == 0 && !a.check.inLink && decide (a.check.link < a.check.links) && a.check.link == l

/-- **The step on the shape.** -/
def laidG (l : Nat) (a : ChainSh) : Except String ChainSh :=
  if laidB l a then .ok a else .error "laid: the shape"

theorem laidB_iff (l : Nat) (s : S) : laidB l (chainSh s) = true ↔ LayFront l s := by
  unfold laidB LayFront FirstDue
  rw [here_between, check_sh]
  show (s.atBetween && !s.check.inLink &&
    decide (s.check.frame.link < s.check.frame.shape.link.length) &&
    s.check.frame.link == l) = true ↔ _
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, ⟨h2, h3⟩, h4⟩
  · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

theorem laid_carries (l : Nat) (s t : S) (u : ChainSh) (h : layFront l s = .ok t)
    (hg : laidG l (chainSh s) = .ok u) : u = chainSh t := by
  obtain ⟨rfl, hL⟩ := layFront_iff.1 h
  unfold laidG at hg
  rw [if_pos ((laidB_iff l t).2 hL)] at hg
  exact (Except.ok.inj hg).symm

theorem laid_returns (l : Nat) (s : S) (u : ChainSh) (hg : laidG l (chainSh s) = .ok u) :
    ∃ t, layFront l s = .ok t := by
  unfold laidG at hg
  by_cases hb : laidB l (chainSh s) = true
  · exact ⟨s, layFront_iff.2 ⟨rfl, (laidB_iff l s).1 hb⟩⟩
  · rw [if_neg hb] at hg
    exact nomatch hg

/-! ## 3 "opened" -/

/-- The test: what "opened" asks of the state. kind: 0 layers, 1 attention, 2 the head. -/
def openB (l kind : Nat) (a : ChainSh) : Bool :=
  a.here == 0 && a.check.inLink && a.check.moments == 1 && !a.marked &&
    a.check.frame.plain == (if kind == 2 then 1 else 0) && a.check.frame.link == l

/-- **The plan's numbers enter the shape.** here: 1 layers, 2 attention. -/
def enterSh (here : Nat) (t : TailSh) (L : LedSh) (X : LinkPub) (l : Nat) (a : ChainSh) : ChainSh :=
  ((((a.setHere here).layTl (some t)).layLed (some L)).layLink
    (some { check := a.check, link := l, arrayOf := X.arrayOf, list := X.Tp, moments := 1,
            handed := false, done := false })).layAtt
    (if here == 2 then some { planes := false, scores := false, heard5 := none } else none)

theorem openB_iff (l kind : Nat) (s : S) : openB l kind (chainSh s) = true ↔
    s.atBetween = true ∧ FirstRun s.check ∧ s.failed = none ∧
      s.check.frame.plain.length = (if kind == 2 then 1 else 0) ∧ s.check.frame.link = l := by
  unfold openB FirstRun
  rw [here_between, check_sh, marked_sh]
  show (s.atBetween && s.check.inLink && s.check.moments == 1 && !s.failed.isSome &&
    s.check.frame.plain.length == (if kind == 2 then 1 else 0) &&
    s.check.frame.link == l) = true ↔ _
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none]
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    exact ⟨h1, ⟨h2, h3⟩, h4, h5, h6⟩
  · rintro ⟨h1, ⟨h2, h3⟩, h4, h5, h6⟩
    exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩

/-- The shape behind an entering at a layers' link. -/
theorem chainSh_lay (s : S) (hB : s.atBetween = true) (X : LinkPub) (l n : Nat) (tl : HTailF2) :
    chainSh { s with here := (.lay
      { L := { check := s.check, link := l, arrayOf := X.arrayOf, list := X.Tp },
        F := startFork X n, tl := tl }) } =
      enterSh 1 (tailSh tl) ((ledSh X.Fp).fresh n) X l (chainSh s) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | between =>
    rw [← ledSh_startFork]
    rfl
  | _ => exact nomatch hB

/-- The shape behind an entering at an attention link. -/
theorem chainSh_att (s : S) (hB : s.atBetween = true) (X : LinkPub) (l n : Nat) (tl : HTailF2) :
    chainSh { s with here := (.att
      { L := { check := s.check, link := l, arrayOf := X.arrayOf, list := X.Tp },
        F := startFork X n, tl := tl, d := default, x := default }) } =
      enterSh 2 (tailSh tl) ((ledSh X.Fp).fresh n) X l (chainSh s) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | between =>
    rw [← ledSh_startFork]
    rfl
  | _ => exact nomatch hB

/-- **The step at a layers' link behind link 0.** -/
def openLayG (P : LayPar) (a : ChainSh) : Except String ChainSh :=
  if openB P.l P.X.kind a then
    .ok (enterSh 1 (tailSh P.tl₀) ((ledSh P.X.Fp).fresh P.ns) P.X P.l a)
  else .error "opened: the shape"

/-- **The step at an attention link.** -/
def openAttG (P : AttPar) (a : ChainSh) : Except String ChainSh :=
  if openB P.l P.X.kind a then
    .ok (enterSh 2 (tailSh { P.tl₀ with funClosed := false, foldDrawn := 0 })
      ((ledSh P.X.Fp).fresh P.ns) P.X P.l a)
  else .error "opened: the shape"

/-- What "opened" lays at a layers' link, as an equation. -/
theorem openLay_lays {P : LayPar} {s t : S} (h : openLay P s = .ok t) :
    s.atBetween = true ∧ t = { s with here := (.lay
      { L := { check := s.check, link := P.l, arrayOf := P.X.arrayOf, list := P.X.Tp },
        F := startFork P.X P.ns, tl := P.tl₀ }) } := by
  obtain ⟨hB, -, a, ⟨-, ⟨-, -, hL, ho⟩, -, -, -, hF⟩, he⟩ := openLay_iff.1 h
  refine ⟨hB, ?_⟩
  have hu := ((S.unmarked_ok _ _).1 he).1
  have hb' : ({ s with out := a.out } : S).atBetween = true := hB
  rw [← hu, hL, hF, ho]
  simp [S.enterLay, hB]

theorem openAtt_lays {P : AttPar} {s t : S} (h : openAtt P s = .ok t) :
    s.atBetween = true ∧ t = { s with here := (.att
      { L := { check := s.check, link := P.l, arrayOf := P.X.arrayOf, list := P.X.Tp },
        F := startFork P.X P.ns, tl := { P.tl₀ with funClosed := false, foldDrawn := 0 },
        d := default, x := default }) } := by
  obtain ⟨hB, -, a, ⟨-, ⟨-, -, hL, ho⟩, hF, ht⟩, he⟩ := openAtt_iff.1 h
  refine ⟨hB, ?_⟩
  have hu := ((S.unmarked_ok _ _).1 he).1
  rw [← hu, hL, hF, ho, ht]
  simp [S.enterAtt, hB]

theorem openLay_carries (P : LayPar) (s t : S) (u : ChainSh) (h : openLay P s = .ok t)
    (hg : openLayG P (chainSh s) = .ok u) : u = chainSh t := by
  obtain ⟨hB, rfl⟩ := openLay_lays h
  unfold openLayG at hg
  by_cases hb : openB P.l P.X.kind (chainSh s) = true
  · rw [if_pos hb] at hg
    rw [chainSh_lay s hB]
    exact (Except.ok.inj hg).symm
  · rw [if_neg hb] at hg
    exact nomatch hg

theorem openAtt_carries (P : AttPar) (s t : S) (u : ChainSh) (h : openAtt P s = .ok t)
    (hg : openAttG P (chainSh s) = .ok u) : u = chainSh t := by
  obtain ⟨hB, rfl⟩ := openAtt_lays h
  unfold openAttG at hg
  by_cases hb : openB P.l P.X.kind (chainSh s) = true
  · rw [if_pos hb] at hg
    rw [chainSh_att s hB]
    exact (Except.ok.inj hg).symm
  · rw [if_neg hb] at hg
    exact nomatch hg

theorem openLay_returns {shape : Params.ReqShape} (P : LayPar) (hp : planLay shape P = true)
    (s : S) (u : ChainSh) (hg : openLayG P (chainSh s) = .ok u) : ∃ t, openLay P s = .ok t := by
  unfold openLayG at hg
  by_cases hb : openB P.l P.X.kind (chainSh s) = true
  · obtain ⟨hB, hR, hf, h1, h2⟩ := (openB_iff _ _ s).1 hb
    obtain ⟨q0, -, q1, q2, q3, -⟩ := (planLay_iff shape P).1 hp
    refine ⟨_, openLay_iff.2 ⟨hB, hR,
      ⟨{ check := s.check, link := P.l, arrayOf := P.X.arrayOf, list := P.X.Tp }, s.out,
        startFork P.X P.ns⟩, ⟨q0, ⟨h1, h2, rfl, rfl⟩, q1, q2, q3, rfl⟩,
      (S.unmarked_ok _ _).2 ⟨rfl, ?_⟩⟩⟩
    have hb' : ({ s with out := s.out } : S).atBetween = true := hB
    unfold S.enterLay
    rw [if_pos hb']
    exact hf
  · rw [if_neg hb] at hg
    exact nomatch hg

theorem openAtt_returns {shape : Params.ReqShape} (P : AttPar) (hp : planAtt shape P = true)
    (s : S) (u : ChainSh) (hg : openAttG P (chainSh s) = .ok u) : ∃ t, openAtt P s = .ok t := by
  unfold openAttG at hg
  by_cases hb : openB P.l P.X.kind (chainSh s) = true
  · obtain ⟨hB, hR, hf, h1, h2⟩ := (openB_iff _ _ s).1 hb
    obtain ⟨q0, -⟩ := (planAtt_iff shape P).1 hp
    refine ⟨_, openAtt_iff.2 ⟨hB, hR,
      ⟨{ check := s.check, link := P.l, arrayOf := P.X.arrayOf, list := P.X.Tp }, s.out,
        startFork P.X P.ns, { P.tl₀ with funClosed := false, foldDrawn := 0 }⟩,
      ⟨q0, ⟨h1, h2, rfl, rfl⟩, rfl, rfl⟩, (S.unmarked_ok _ _).2 ⟨rfl, ?_⟩⟩⟩
    have hb' : ({ s with out := s.out } : S).atBetween = true := hB
    unfold S.enterAtt
    rw [if_pos hb']
    exact hf
  · rw [if_neg hb] at hg
    exact nomatch hg

end Johnson.Desc.First.Walk.Shape

#print axioms Johnson.Desc.First.Walk.Shape.laid_carries
#print axioms Johnson.Desc.First.Walk.Shape.laid_returns
#print axioms Johnson.Desc.First.Walk.Shape.openLay_carries
#print axioms Johnson.Desc.First.Walk.Shape.openLay_returns
#print axioms Johnson.Desc.First.Walk.Shape.openAtt_carries
#print axioms Johnson.Desc.First.Walk.Shape.openAtt_returns
#print axioms Johnson.Desc.First.Walk.Shape.here_between
#print axioms Johnson.Desc.First.Walk.Shape.marked_sh
#print axioms Johnson.Desc.First.Walk.Shape.check_sh
#print axioms Johnson.Desc.First.Walk.Shape.laidB
#print axioms Johnson.Desc.First.Walk.Shape.laidG
#print axioms Johnson.Desc.First.Walk.Shape.laidB_iff
#print axioms Johnson.Desc.First.Walk.Shape.openB
#print axioms Johnson.Desc.First.Walk.Shape.enterSh
#print axioms Johnson.Desc.First.Walk.Shape.openB_iff
#print axioms Johnson.Desc.First.Walk.Shape.chainSh_lay
#print axioms Johnson.Desc.First.Walk.Shape.chainSh_att
#print axioms Johnson.Desc.First.Walk.Shape.openLayG
#print axioms Johnson.Desc.First.Walk.Shape.openAttG
#print axioms Johnson.Desc.First.Walk.Shape.openLay_lays
#print axioms Johnson.Desc.First.Walk.Shape.openAtt_lays
