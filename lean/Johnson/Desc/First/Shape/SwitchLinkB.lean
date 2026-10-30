-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/SwitchLinkB.lean: THE CODE SWITCH AT A SEGMENT's FIRST PLACE (kind K2):
"RETURNS" FROM THREE TESTS WITH CODE: ONE ON THE CHAIN's SHAPE WITH THE ROWS' MAKES BESIDE IT, ONE
ON VALUES OF THE STATE, ONE ON THE TWO ROUNDS AND THE COLUMNS. General laws; nothing is evaluated.

What it is for. The law link_returns_sent (Johnson/Desc/K2/Honest/Returns/LinkSent.lean) leads from
LinkPlain, a structure of premises at the state in front, to a yes of the kind's own decision. Here
these premises are sorted by what they read.

  1 `withGroupS` | `withGroup_sh` | `withGroup_forms`: the statement with the new group, on its
    shape and on the makes. `sendingS` | `sending_sh`: the sending's public numbers, off the codes,
    the target and what the front announces (linkOthers, Switch.lean).
  2 `dueB`, `waitsB`, `locB` | `loc_sh`, `leftAfterS` | `leftAfter_sh`, `ownB` | `own_of_B`: single
    clauses.
  3 **`linkB p x`**: ALL THAT HANGS ON THE PLAN's NUMBERS p AND ON x : ChainF: five look-ups (the
    segment · its group · the two new codes · the old main code) · the kind stands at a link · the
    chain stands between two links · a first call is due · no count of rows waits · the frame's next
    call is a first one, not at link 0 · the new mask code is not longer than the new main code · no
    plain scalar · the new group's number is the plan's · the first round's entry fits what is
    announced · the sending's tests on the plan · as many messages as places in the book · as many
    trees as roots · ReadFits but "opens" (readFitsB) · the front's own messages against what it
    announces (ownB) · FrontCore but "the ones" and the positions' range (frontCoreB at no
    position). `linkB_here`: its clause on where the chain stands.
  4 **`linkR p x r₁ r₂ gs`**: ALL THAT READS THE ROUNDS OR THE COLUMNS: the positions lie in the
    plan's range · round 1 fits its entry, draws as many elements as the seeds take, holds no value,
    no position, no trit · no seed's factor is spelt by three words 0 · round 2 holds
    the answers · the seven conditions of the round "LOC" · the trees open at the columns (allOpenB)
    · no column is left · as many groups of columns as trees read · the listed positions lie in the
    old main code's range.
  5 **`linkPlain_of_B`**: linkB p (chainF s), onesV s.st s.check.frame.rows (SwitchFrontFits.lean:
    THE ONE TEST ON VALUES OF THE STATE) and linkR p (chainF s) r₁ r₂ gs accept: then LinkPlain
    holds at the looked-up witnesses. **`link_returns_B`**: then decideWith sendByL8 p s [r₁, r₂] gs
    returns.

Limits. One way: a yes of the three gives the premises. NO STATE IS SHOWN AT WHICH THEY ACCEPT. That
rounds and columns which fit the kind's declared rounds meet linkR, under further tests on the plan
and the shape, is SwitchLinkFits.lean's and SwitchLinkFactor.lean's. No law here carries onesV from
what the chain's steps lay. The kind's own decision: no member of a chain is named. Nothing on
soundness, completeness or hiding.

-/
import Johnson.Desc.K2.Honest.Returns.LinkSent
import Johnson.Desc.First.Shape.SwitchReadFits
import Johnson.Desc.First.Shape.SwitchFrontPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground.Sh (StSh stSh)
open VerifiableInference.Desc.First.K2 (P2 decideWith par9 flat locOk behindArgs)
open VerifiableInference.Desc.First.Send (planOk1)
open VerifiableInference.Desc.K2.Honest.Returns (FrontCore LinkPlain frontAt sendingAt inFront
  leftAfter link_returns_sent)
open OnBytes.Slice (withGroup)
open OnBytes.Params (ReqMessage)
open _root_.Tw.K2 (Front Col Par9 sendByL8 switchNotices)

/-! ## 1 The front, off shapes -/

/-- The statement's shape with one more group, which has no member and no row. -/
def withGroupS (a : StSh) (code maskCode : Nat) : StSh :=
  { a with groups := a.groups ++ [⟨code, maskCode, [], [], [], false⟩] }

theorem withGroup_sh (S : Statement) (code maskCode : Nat) :
    stSh (withGroup S code maskCode) = withGroupS (stSh S) code maskCode := by
  unfold withGroup withGroupS Ground.Sh.stSh
  simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
  rfl

theorem withGroup_forms (S : Statement) (code maskCode : Nat) :
    formsOf (withGroup S code maskCode) =
      { formsOf S with groups := (formsOf S).groups ++ [[]] } := by
  unfold withGroup formsOf
  simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
  rfl

/-- The sending's public numbers. -/
def sendingS (p : P2) (codes : Codes) (T : SwitchTarget) (others : Array OracleNotice) : K1.Par :=
  { place := default, codes := codes, gp := ⟨(par9 p).samples, (par9 p).firstTree⟩, work := 0
    parts := [("", switchNotices T others)] }

theorem sending_sh (p : P2) (s : S) (L : Params.ReqLink) (Q : ReqGroup) :
    sendingAt p (frontAt s L Q) =
      sendingS p s.st.codes Q.target (linkOthers (frameSh s.check.frame)) := rfl

/-! ## 2 Single clauses -/

/-- A link's first call is due. -/
def dueB (c : CheckSh) : Bool := !c.inLink && decide (c.frame.link < c.frame.shape.link.length)

/-- No count of rows waits. -/
def waitsB (r : Option Nat) : Bool :=
  match r with
  | none => true
  | some r => r == 0

/-- The seven conditions of the round "LOC". took: the answers that the sending takes. -/
def locB (P : Par9) (took logN : Nat) (rL : Fmt.RoundView) : Bool :=
  !(P.eLoc.name != "LOC") && !(P.eLoc.drawNZ != 0) && (P.eSeed.rows == 0) &&
      !(rL.vals.length - took != 0) &&
    (rL.drawn.elems.length == P.eLoc.drawE && rL.drawn.poss.length == P.eLoc.poss &&
        rL.drawn.trits.length == P.eLoc.trits) &&
    (P.eLoc.logN == logN && decide (0 < P.eLoc.poss)) && rL.drawn.elems.isEmpty

theorem loc_sh (P : Par9) (x : Front) (y : _root_.Tw.K2.Sent) (rL : Fmt.RoundView) (cols : List Col)
    (logN : Nat) : locOk (behindArgs P x y rL cols) logN = locB P y.took logN rL := rfl

/-- The columns that the opening of the trees does not take. -/
def leftAfterS (pos : Positions) (b : Ground.Sh.BookSh) : List Nat → List Col → List Col
  | [], c => c
  | t :: ts, c => leftAfterS pos b ts (c.drop (ownAtS pos b t).size)

theorem leftAfter_sh (pos : Positions) (B0 : TreeBook) : ∀ (ts : List Nat) (c : List Col),
    leftAfter pos B0 ts c = leftAfterS pos (Ground.Sh.bookSh B0) ts c
  | [], _ => rfl
  | t :: ts, c => by
    unfold leftAfter leftAfterS
    rw [ownAt_sh, leftAfter_sh pos B0 ts]

/-- The front's own messages against what it announces and the new group's two codes. -/
def ownB (own : List ReqMessage) (others : Array OracleNotice) (code maskCode : Nat) : Bool :=
  own.zipIdx.all fun q =>
    match others[q.2]? with
    | none => false
    | some n =>
      decide (n.shape.answers ≠ 0) && decide (n.shape.mainRows = 0 ∨ n.shape.code = code) &&
        decide (n.shape.maskRows = 0 ∨ n.shape.maskCode = maskCode) &&
        decide (0 < q.1.life → 0 < n.shape.mainRows)

theorem own_of_B {own : List ReqMessage} {others : Array OracleNotice} {code maskCode : Nat}
    (h : ownB own others code maskCode = true) (j : Nat) (m : ReqMessage) (hm : own[j]? = some m) :
    ∃ n, others[j]? = some n ∧ n.shape.answers ≠ 0 ∧
      (n.shape.mainRows = 0 ∨ n.shape.code = code) ∧
      (n.shape.maskRows = 0 ∨ n.shape.maskCode = maskCode) ∧
      (0 < m.life → 0 < n.shape.mainRows) := by
  have hq : (m, j) ∈ own.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    exact hm
  have := List.all_eq_true.1 h _ hq
  dsimp only at this
  cases e : others[j]? with
  | none => rw [e] at this; cases this
  | some n =>
    rw [e] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨n, rfl, this.1.1.1, this.1.1.2, this.1.2, this.2⟩

/-! ## 3 What hangs on the plan and the shape -/

/-- **The test on the plan's numbers and the chain's shape with the rows' makes.** -/
def linkB (p : P2) (x : ChainF) : Bool :=
  match x.1.check.frame.shape.link[x.1.check.frame.link]?,
    x.1.check.frame.groups[x.1.check.frame.link]?,
    x.1.core.st.codes.base[x.1.check.frame.shape.code]?,
    x.1.core.st.codes.mask[x.1.check.frame.shape.maskCode]?,
    x.1.core.st.codes.base[x.1.check.frame.rows.code]? with
  | some L, some Q, some c₀, some z₀, some c =>
    decide (p.stands = .link) && x.1.here == 0 && dueB x.1.check && waitsB x.1.rowsOwed &&
      decide (x.1.check.frame.next = .first) && decide (x.1.check.frame.link ≠ 0) &&
      decide (z₀.logN ≤ c₀.logN) && decide (L.plain = 0) &&
      decide (x.1.core.st.groups.length = p.grp) &&
      planOk1 none (switchNotices Q.target (linkOthers x.1.check.frame)) (par9 p).eSeed &&
      K1.planOkOwn (sendingS p x.1.core.st.codes Q.target (linkOthers x.1.check.frame)) &&
      decide (x.1.core.st.oracles.length = x.1.core.book.place.length) &&
      decide (((layTrees (sendingS p x.1.core.st.codes Q.target (linkOthers x.1.check.frame)).codes
        (sendingS p x.1.core.st.codes Q.target (linkOthers x.1.check.frame)).sent).getD
          {}).shapes.size = (par9 p).eSeed.roots) &&
      readFitsB
        (withGroupS x.1.core.st x.1.check.frame.shape.code x.1.check.frame.shape.maskCode)
        x.1.core.book x.1.check.frame.rows &&
      ownB (x.1.check.frame.blank.atMoment 0) (linkOthers x.1.check.frame)
        x.1.check.frame.shape.code x.1.check.frame.shape.maskCode &&
      frontCoreB
        (withGroupS x.1.core.st x.1.check.frame.shape.code x.1.check.frame.shape.maskCode)
        { x.2 with groups := x.2.groups ++ [[]] } x.1.check.frame.rows Q.target
        x.1.check.frame.shape.code [] c
  | _, _, _, _, _ => false

/-- The test's clause on where the chain stands. -/
theorem linkB_here {p : P2} {x : ChainF} (h : linkB p x = true) : (x.1.here == 0) = true := by
  unfold linkB at h
  split at h
  · simp only [Bool.and_eq_true] at h
    exact h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  · cases h

/-! ## 4 What reads the rounds or the columns -/

/-- **The test on the two rounds and the columns.** -/
def linkR (p : P2) (x : ChainF) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64))) : Bool :=
  match x.1.check.frame.groups[x.1.check.frame.link]?,
    x.1.core.st.codes.base[x.1.check.frame.rows.code]? with
  | some Q, some c =>
    decide (∀ q ∈ r₂.drawn.poss, q < 2 ^ p.logN) && _root_.Desc.Plain.fits (par9 p).eSeed r₁ &&
      decide ((r₁.drawn.elems.map E.ofTriple).length =
        (sendingS p x.1.core.st.codes Q.target (linkOthers x.1.check.frame)).seeds *
          ((sendingS p x.1.core.st.codes Q.target (linkOthers x.1.check.frame)).coordinates + 1)) &&
      r₁.vals.isEmpty && r₁.drawn.poss.isEmpty && r₁.drawn.trits.isEmpty &&
      ((K1.seedsOf (sendingS p x.1.core.st.codes Q.target (linkOthers x.1.check.frame)) r₁).all
        fun z => !isZeroE z.2) &&
      decide ((K1.answersIn (K1.cutTo
        (sendingS p x.1.core.st.codes Q.target (linkOthers x.1.check.frame)) r₂)).length =
        (sendingS p x.1.core.st.codes Q.target (linkOthers x.1.check.frame)).answers) &&
      locB (par9 p) (sendingS p x.1.core.st.codes Q.target (linkOthers x.1.check.frame)).answers
        c.logN r₂ &&
      allOpenB
        (withGroupS x.1.core.st x.1.check.frame.shape.code x.1.check.frame.shape.maskCode)
        x.1.core.book (par9 p).firstTree (Positions.ofDraws c.logN r₂.drawn.poss)
        (treesOfS x.1.core.book x.1.check.frame.rows) (flat p gs) &&
      (leftAfterS (Positions.ofDraws c.logN r₂.drawn.poss) x.1.core.book
        (treesOfS x.1.core.book x.1.check.frame.rows) (flat p gs)).isEmpty &&
      decide (gs.length = p.read.length) &&
      inRangeB
        (withGroupS x.1.core.st x.1.check.frame.shape.code x.1.check.frame.shape.maskCode)
        x.1.check.frame.rows r₂.drawn.poss c
  | _, _ => false

/-! ## 5 "Returns" -/

/-- The chain stands between two links. -/
theorem between_of_here {s : S} (h : ((chainF s).1.here == 0) = true) : s.here = .between := by
  have h0 : hereNo s.here = 0 := beq_iff_eq.1 h
  cases hh : s.here with
  | between => rfl
  | lay a => rw [hh] at h0; cases h0
  | att a => rw [hh] at h0; cases h0
  | head a =>
    rw [hh] at h0
    cases ho : a.opened <;> simp [hereNo, ho] at h0
  | fin a => rw [hh] at h0; cases h0
  | mem a => rw [hh] at h0; cases h0

/-- **The three tests give the premises, at the looked-up witnesses.** -/
theorem linkPlain_of_B {p : P2} {s : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hB : linkB p (chainF s) = true) (hV : onesV s.st s.check.frame.rows = true)
    (hR : linkR p (chainF s) r₁ r₂ gs = true) :
    ∃ L Q c₀ z₀ c, LinkPlain p s r₁ r₂ gs L Q c₀ z₀ c := by
  unfold linkB at hB
  split at hB
  · rename_i L Q c₀ z₀ c e1 e2 e3 e4 e5
    unfold linkR at hR
    split at hR
    · rename_i Q' c' f2 f5
      obtain rfl : Q = Q' := Option.some.inj (e2.symm.trans f2)
      obtain rfl : c = c' := Option.some.inj (e5.symm.trans f5)
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff, List.all_eq_true,
        Bool.not_eq_true'] at hB hR
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩, b11⟩, b12⟩, b13⟩,
        b14⟩, b15⟩, b16⟩, b17⟩ := hB
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a10⟩, a11⟩, a12⟩, a13⟩,
        a14⟩ := hR
      have hst : stSh (frontAt s L Q).st = withGroupS (stSh s.st) s.check.frame.shape.code
          s.check.frame.shape.maskCode := withGroup_sh _ _ _
      have hfo : formsOf (frontAt s L Q).st =
          { formsOf s.st with groups := (formsOf s.st).groups ++ [[]] } := withGroup_forms _ _ _
      have hg : (stSh s.st).groups.length = s.st.groups.size := Ground.Sh.grp_size _
      have hF : FrontCore (frontAt s L Q) c s.check.frame.shape.code r₂.drawn.poss := by
        rw [frontCore_iffB, Bool.and_eq_true, frontCoreB_split, Bool.and_eq_true, hst, hfo]
        exact ⟨⟨b17, a14⟩, hV⟩
      have hRd : K2.Honest.Returns.ReadFits
          (inFront (par9 p) (frontAt s L Q) s.book (K2.Honest.Returns.sentOf p s L Q r₁ r₂) r₂
            (flat p gs))
          (Positions.ofDraws c.logN r₂.drawn.poss) := by
        rw [readFits_iffB, Bool.and_eq_true]
        refine ⟨?_, ?_⟩
        · show readFitsB (stSh (frontAt s L Q).st) _ _ = true
          rw [hst]
          exact b15
        · show allOpenB (stSh (frontAt s L Q).st) _ _ _ _ _ = true
          rw [hst]
          exact a11
      have hNo : leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) s.book
          (K2.Honest.Returns.treesOf
            (inFront (par9 p) (frontAt s L Q) s.book (K2.Honest.Returns.sentOf p s L Q r₁ r₂) r₂
              (flat p gs)))
          (flat p gs) = [] := by
        rw [leftAfter_sh, ← trees_sh]
        exact a12
      refine ⟨L, Q, c₀, z₀, c,
        { stands := b1, range := a1, here := between_of_here b2, due := b3, waits := b4
          first := b5, later := b6, link := e1, group := e2, code := e3, maskCode := e4
          shorter := b7, plain := b8, number := hg ▸ b9, entry := b11, fits₁ := a2, plan := b12
          step := ?_, draw := a3, vals := a4, poss := a5, trits := a6, factor := a7, answers := a8
          trees := b14, oldCode := e5, loc := a10, reads := hRd, front := hF
          own := own_of_B b16, noneLeft := hNo, groups := a13 }⟩
      show s.st.oracles.size = s.book.place.size
      rw [← Ground.Sh.orc_size, ← Ground.Sh.place_size]
      exact b13
    · cases hR
  · cases hB

/-- **The three tests accept: the kind's own decision says yes.** -/
theorem link_returns_B {p : P2} {s : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hB : linkB p (chainF s) = true) (hV : onesV s.st s.check.frame.rows = true)
    (hR : linkR p (chainF s) r₁ r₂ gs = true) :
    ∃ s', decideWith sendByL8 p s [r₁, r₂] gs = .ok s' := by
  obtain ⟨L, Q, c₀, z₀, c, H⟩ := linkPlain_of_B hB hV hR
  exact link_returns_sent H

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.withGroup_sh
#print axioms VerifiableInference.Desc.First.Shape.withGroup_forms
#print axioms VerifiableInference.Desc.First.Shape.sending_sh
#print axioms VerifiableInference.Desc.First.Shape.loc_sh
#print axioms VerifiableInference.Desc.First.Shape.leftAfter_sh
#print axioms VerifiableInference.Desc.First.Shape.own_of_B
#print axioms VerifiableInference.Desc.First.Shape.linkB_here
#print axioms VerifiableInference.Desc.First.Shape.between_of_here
#print axioms VerifiableInference.Desc.First.Shape.linkPlain_of_B
#print axioms VerifiableInference.Desc.First.Shape.link_returns_B
