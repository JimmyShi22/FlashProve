-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameLaw.lean: the link's frame's law: what a yes of each of the frame's
functions (Johnson/Desc/First/Walk/Frame.lean, FrameZero.lean) guarantees to the blocks behind it.
The frame's blocks take no round and draw nothing: so their lemmas have no probability in them:
they say, of the carried record in front and behind: which tests have held, what has been laid,
what has not been touched.

  layFront_ok     lay hands the record on unturned; it stood between two links; a first call was
                  due; the chain stood at this link
  front_ok        [W1] [W2]; the link's context and the walk's result, written out
  back_ok         [W3] [W4] [W5]; what goes on
  openAtt_ok | openLay_ok | openLayZero_ok   the record stood between two links; the link's first
                  call had run; the chain stood at this link; behind: the link is open, with just
                  this context and this fork; the state of the calls, the statement and the mark
                  are untouched; what the walk's result is; at link 0: [I1] ... [I4]
                  (indexMasksAt_ok), and the index-mask message's number laid into the result
  clearWith_ok    a link with its fork was open; the kind's counts held; [W3] [W4]; behind: the
                  record stands between two links, its state of the calls is the link's live copy;
                  where the record leaves no row: the walk's result and the statement are
                  untouched; where it leaves one: just one row is laid at the pile's end, and the
                  statement's messages are what the row's function returned
  clearWith_eq    "cleared", written out whole: which of the record's nine fields it turns, to what

The seam between two links.
  clear_carries   through "cleared": the live state of the calls, the book, the roots, the rows
                  owed, the mark, the request, the statement's codes and groups: to the letter; the
                  walk's state of the calls behind is the link's live copy; between two links
  clear_rows      the closing's open claim by its field, without the next "laid": the frame's rows
                  in the walk's state behind are the live copy's in front. For the chain's last
                  seam, where seam_carries and seam_rows are empty (see the limits)
  seam_carries | seam_rows   the same through "cleared" and the next link's "laid", to in front of
                  the next first call
  clear_messages  at the row's function pendingRowO: as many messages behind as in front, each the
                  same but for its ledger
  openAtt_carries | openLay_carries   "opened" lays the walk's state of the calls into the link

The ledger of the index-mask message (Johnson/Desc/First/Pend/Row.lean's takeEntry).
  nextEntry_ge, takeEntry_spec   the number handed out is not below the ledger's "next"; behind,
                  "next" stands above it and one entry less is left
  takes_sorted, takes_nodup   any run of takings off one ledger hands out strictly rising numbers
  pendingRowO_spec   the row bears just the number taken; the messages behind are those in front
                  with that ledger turned
  clear_row       where a link leaves a row, clear takes just one entry off that ledger, and the
                  row that it lays bears just that entry
  linked_nodup, clearings_nodup   under one named condition (Linked; at the carried record: Kept):
                  no two of the rows that the links' clearings lay bear the same entry

The reply heard.
  layFront_leaves, openAtt_leaves, openLay_leaves, openLayZero_leaves, clearWith_leaves
                  s.out.reply is left as it was: at "opened" where the record's kind is not the
                  head's (a letter); at clear at every link

A yardstick, no law.
  roomOf_eq       the frame's own number of ledger entries is the program `verify-on-bytes`'s
                  indexMasksTaken (onTable links) kCol. Its statement names that verifier's
                  functions over its records with their routines: a walk by constants from it
                  meets Blk, Ctx, Chan, SubM, LinkM. No other theorem of this file leans on it.

Limits.
These are inversions of the written text from a yes: post-conditions, no soundness statement. A text
that refuses all meets them emptily: nothing on completeness. X, counts, left, row, l are letters:
the theorems are tools, spent nowhere yet. (Where
this and lean/THEOREM.md differ, the page holds.)
seam_carries and seam_rows are empty at the chain's last seam, behind the head's link: there the
next "laid" refuses in every accepted run (its test "a first call is due" and the finish's "no link
is still to come" shut each other out).
That a block's own text for the closing lays its open claim into the frame's field rows of the LIVE
copy, and into no other field, is that kind's law to say. In seam_rows keptBefore, group and mask
are idle for the next first call.
takeEntry_spec bounds the number handed out from below alone: that it is an entry of the message
is nowhere: so the ledger's row is "no number twice", not "each entry exactly once".
Kept is proved of no chain: that between two takings nobody else writes that ledger or turns the
message's number is each other block's "what it does not touch". The batching's own takings off
the same ledger are not covered.
openAtt_ok, openLay_ok and openLayZero_ok are silent on the book, the roots, the rows owed and the
request, and on attention's record of the smallness test.
The statement and the walk's result are carried to the letter only where the link leaves no row.
Definitions' unfoldings alone; "#print axioms" at the end says which axioms.

-/
import Johnson.Desc.First.Walk.FrameZero
import Johnson.Desc.First.Pend.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc (need)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Pend (nextEntry takeEntry)

theorem layFront_ok {l : Nat} {s t : S} (h : layFront l s = .ok t) :
    t = s ∧ s.atBetween = true ∧ firstDue s.check = true ∧ s.check.frame.link = l := by
  unfold layFront at h
  cases hB : s.atBetween <;> cases hW : firstDue s.check <;> cases hL : (s.check.frame.link == l)
      <;>
    simp [need, hB, hW, hL, bind, Except.bind, pure, Except.pure] at h
  exact ⟨h.symm, rfl, rfl, by simpa using hL⟩

theorem front_ok {X : LinkPub} {l : Nat} {check : ChainCheck} {out o : Proof.LinksResult} {L :
    LinkCtx}
    (h : front X l check out = .ok (L, o)) :
    check.frame.plain.length = (if X.kind == 2 then 1 else 0) ∧ check.frame.link = l ∧
      L = { check := check, link := l, arrayOf := X.arrayOf, list := X.Tp } ∧ o = out := by
  unfold front at h
  cases hk : (X.kind == 2) <;>
  simp only [hk, Bool.false_eq_true, if_false, if_true, ↓reduceIte] at h ⊢ <;> (
    split at h
    · exact absurd h (by simp)
    · rename_i h1
      split at h
      · exact absurd h (by simp)
      · rename_i h2
        simp at h
        exact ⟨by simpa using h1, by simpa using h2, h.1.symm, h.2.symm⟩)

theorem back_ok {X : LinkPub} {o r : Option WsForkOut} {C : LinkCtx} {F : Fork} {k : ChainCheck}
    (h : back X o C F = .ok (k, r)) :
    C.handed = true ∧ C.done = true ∧ samePlan X F C.list = true ∧ k = C.check ∧
      (X.fv = false → r = none) ∧ (X.fv = true → r = o ∧ o.isSome = true) := by
  unfold back at h
  cases h1 : C.handed <;> cases h2 : C.done <;> cases h3 : samePlan X F C.list <;> cases h4 : X.fv
      <;> cases o <;>
    simp [h1, h2, h3, h4] at h
  all_goals simp [h.1.symm, h.2.symm]

/-! ### opened -/

theorem enterAtt_ok {s : S} {L : LinkCtx} {F : Fork} {tl : HTailF2} (hB : s.atBetween = true) :
    (S.enterAtt s L F tl).link? = some L ∧ (S.enterAtt s L F tl).fork? = some F ∧ (S.enterAtt s L F
        tl).check = s.check ∧
      (S.enterAtt s L F tl).st = s.st ∧ (S.enterAtt s L F tl).out = s.out ∧ (S.enterAtt s L F
          tl).failed = s.failed := by
  simp [S.enterAtt, hB, S.link?, S.fork?]

theorem enterLay_ok {s : S} {L : LinkCtx} {F : Fork} {tl : HTailF2} (hB : s.atBetween = true) :
    (S.enterLay s L F tl).link? = some L ∧ (S.enterLay s L F tl).fork? = some F ∧ (S.enterLay s L F
        tl).check = s.check ∧
      (S.enterLay s L F tl).st = s.st ∧ (S.enterLay s L F tl).out = s.out ∧ (S.enterLay s L F
          tl).failed = s.failed := by
  simp [S.enterLay, hB, S.link?, S.fork?]

theorem openAtt_ok {P : AttPar} {s t : S} (h : openAtt P s = .ok t) :
    s.atBetween = true ∧ firstRun s.check = true ∧ P.l ≠ 0 ∧ s.check.frame.link = P.l ∧
      t.link? = some { check := s.check, link := P.l, arrayOf := P.X.arrayOf, list := P.X.Tp } ∧
      t.fork? = some (startFork P.X P.ns) ∧ t.check = s.check ∧ t.st = s.st ∧ t.failed = s.failed ∧
      t.out = s.out := by
  unfold openAtt at h
  cases hB : s.atBetween with
  | false => simp [need, hB, bind, Except.bind] at h
  | true =>
   cases hA : firstRun s.check with
   | false => simp [need, hB, hA, bind, Except.bind] at h
   | true =>
    cases hq : attFirstQuiet P.X P.l P.ns P.tl₀ s.check s.out with
    | error e => simp [need, hB, hA, hq, bind, Except.bind] at h
    | ok a =>
      simp [need, hB, hA, hq, bind, Except.bind, pure, Except.pure] at h
      have hu := (S.unmarked_ok _ _).mp h
      have h := hu.1
      unfold attFirstQuiet at hq
      split at hq
      · simp at hq
      · rename_i h0
        cases hf : front P.X P.l s.check s.out with
        | error e => simp [hf] at hq
        | ok p =>
          obtain ⟨L, o⟩ := p
          simp [hf] at hq
          have fo := front_ok hf
          have hb' : ({ s with out := a.out } : S).atBetween = true := hB
          have en := enterAtt_ok (s := { s with out := a.out }) (L := a.L) (F := a.F) (tl := a.tl)
              hb'
          rw [h] at en
          subst hq
          exact ⟨rfl, rfl, by simpa using h0, fo.2.1, by rw [en.1, fo.2.2.1], en.2.1, en.2.2.1,
              en.2.2.2.1, en.2.2.2.2.2,
            en.2.2.2.2.1.trans fo.2.2.2⟩

theorem openLay_ok {P : LayPar} {s t : S} (h : openLay P s = .ok t) :
    s.atBetween = true ∧ firstRun s.check = true ∧ P.l ≠ 0 ∧ s.check.frame.link = P.l ∧ P.l = (if
        P.p4 then 2 * P.g else P.g) ∧
      t.link? = some { check := s.check, link := P.l, arrayOf := P.X.arrayOf, list := P.X.Tp } ∧
      t.fork? = some (startFork P.X P.ns) ∧ t.check = s.check ∧ t.st = s.st ∧ t.failed = s.failed ∧
      t.out = s.out := by
  unfold openLay at h
  cases hB : s.atBetween with
  | false => simp [need, hB, bind, Except.bind] at h
  | true =>
   cases hA : firstRun s.check with
   | false => simp [need, hB, hA, bind, Except.bind] at h
   | true =>
    cases hq : layFirstQuiet P.X P.l P.p4 P.g P.Tp P.Fp P.ns s.check s.out with
    | error e => simp [need, hB, hA, hq, bind, Except.bind] at h
    | ok a =>
      simp [need, hB, hA, hq, bind, Except.bind, pure, Except.pure] at h
      have hu := (S.unmarked_ok _ _).mp h
      have h := hu.1
      unfold layFirstQuiet at hq
      split at hq
      · simp at hq
      · rename_i h0
        cases hf : front P.X P.l s.check s.out with
        | error e => simp [hf] at hq
        | ok p =>
          obtain ⟨L, o⟩ := p
          have fo := front_ok hf
          by_cases h1 : L.link = (if P.p4 then 2 * P.g else P.g)
          · simp [hf, h1] at hq
            split at hq
            · exact absurd hq (by simp)
            · simp at hq
              have hb' : ({ s with out := a.out } : S).atBetween = true := hB
              have en := enterLay_ok (s := { s with out := a.out }) (L := a.L) (F := a.F) (tl :=
                  P.tl₀) hb'
              rw [h] at en
              subst hq
              have hg := h1
              rw [fo.2.2.1] at hg
              exact ⟨rfl, rfl, by simpa using h0, fo.2.1, hg, by rw [en.1, fo.2.2.1], en.2.1,
                  en.2.2.1, en.2.2.2.1, en.2.2.2.2.2,
                en.2.2.2.2.1.trans fo.2.2.2⟩
          · simp [hf, h1] at hq

/-! ### cleared -/

theorem leaveLink_ok {s : S} {C : LinkCtx} {F : Fork} (hC : s.link? = some C) (hF : s.fork? = some
    F) :
    s.leaveLink.atBetween = true ∧ s.leaveLink.check = C.check ∧ s.leaveLink.out = s.out ∧
        s.leaveLink.st = s.st ∧
      s.leaveLink.failed = s.failed := by
  simp [S.leaveLink, S.inLink, hF, S.live, hC, S.atBetween]

theorem clearWith_ok {X : LinkPub} {counts : S → Except String Unit} {left : S → Option WsForkOut}
    {row : RowFn} {s t : S}
    (h : clearWith X counts left row s = .ok t) :
    ∃ C F, s.link? = some C ∧ s.fork? = some F ∧ counts s = .ok () ∧ C.handed = true ∧ C.done = true
        ∧
      samePlan X F C.list = true ∧ t.atBetween = true ∧ t.check = C.check ∧ t.failed = s.failed ∧
      (X.fv = false → t.out = s.out ∧ t.st = s.st) ∧
      (X.fv = true → ∃ w r os, left s = some w ∧ row s.out.indexMasks w X.NCL s.st.oracles = .ok (r,
          os) ∧
        t.out = pendingKept s.out r ∧ t.st = { s.st with oracles := os }) := by
  unfold clearWith at h
  cases hC : s.link? with
  | none => simp [hC] at h
  | some C =>
    cases hF : s.fork? with
    | none => simp [hC, hF] at h
    | some F =>
      cases hk : counts s with
      | error e => simp [hC, hF, hk, bind, Except.bind] at h
      | ok u =>
        cases hb : back X (left s) C F with
        | error e => simp [hC, hF, hk, hb, bind, Except.bind] at h
        | ok p =>
          obtain ⟨k, r⟩ := p
          have bo := back_ok hb
          cases r with
          | none =>
            simp [hC, hF, hk, hb, bind, Except.bind, pure, Except.pure] at h
            have h := ((S.unmarked_ok _ _).mp h).1
            have lv := leaveLink_ok hC hF
            rw [h] at lv
            refine ⟨C, F, rfl, rfl, rfl, bo.1, bo.2.1, bo.2.2.1, lv.1, lv.2.1, lv.2.2.2.2, fun _ =>
                ⟨lv.2.2.1, lv.2.2.2.1⟩, ?_⟩
            intro hv
            have := (bo.2.2.2.2.2 hv)
            rw [← this.1] at this
            simp at this
          | some w =>
            cases hr : row s.out.indexMasks w X.NCL s.st.oracles with
            | error e => simp [hC, hF, hk, hb, hr, bind, Except.bind] at h
            | ok q =>
              obtain ⟨r, os⟩ := q
              simp [hC, hF, hk, hb, hr, bind, Except.bind, pure, Except.pure] at h
              have h := ((S.unmarked_ok _ _).mp h).1
              have lv := leaveLink_ok (s := { s with out := pendingKept s.out r, st := { s.st with
                  oracles := os } }) (C := C) (F := F) hC hF
              rw [h] at lv
              refine ⟨C, F, rfl, rfl, rfl, bo.1, bo.2.1, bo.2.2.1, lv.1, lv.2.1, lv.2.2.2.2, ?_, ?_⟩
              · intro hv
                have := bo.2.2.2.2.1 hv
                simp at this
              · intro hv
                exact ⟨w, r, os, ((bo.2.2.2.2.2 hv).1).symm, hr, lv.2.2.1, lv.2.2.2.1⟩

/-! ### the seam between two links: what «cleared» and the next link's «laid» carry -/

/-- **«cleared», written out whole.** Of the carried record's nine fields it turns: the place
  (between two links) · the walk's state of the calls (:= the link's live copy) · and, where the
  record leaves a row, the walk's result (one row
more on the pile) and the statement's messages (what the row's function returned). THE BOOK OF TREES
  · THE NUMBER OF ROOTS · THE COUNT OF ROWS OWED · THE MARK · THE REQUEST, AND ALL OF THE STATEMENT
  BUT ITS MESSAGES: NOT TOUCHED. -/
theorem clearWith_eq {X : LinkPub} {counts : S → Except String Unit} {left : S → Option WsForkOut}
    {row : RowFn} {s t : S}
    (h : clearWith X counts left row s = .ok t) :
    (X.fv = false → t = { s with check := s.live, here := .between }) ∧
    (X.fv = true → ∃ w r os, left s = some w ∧ row s.out.indexMasks w X.NCL s.st.oracles = .ok (r,
        os) ∧
      t = { s with check := s.live, here := .between, out := pendingKept s.out r, st := { s.st with
          oracles := os } }) := by
  have ok := clearWith_ok h
  obtain ⟨C, F, hC, hF, hk, _, _, _, _, _, _, _, _⟩ := ok
  unfold clearWith at h
  cases hb : back X (left s) C F with
  | error e => simp [hC, hF, hk, hb, bind, Except.bind] at h
  | ok p =>
    obtain ⟨k, r⟩ := p
    have bo := back_ok hb
    cases r with
    | none =>
      simp [hC, hF, hk, hb, bind, Except.bind, pure, Except.pure] at h
      have h := ((S.unmarked_ok _ _).mp h).1
      constructor
      · intro _
        rw [← h]
        simp [S.leaveLink, S.inLink, hF]
      · intro hv
        have := bo.2.2.2.2.2 hv
        rw [← this.1] at this
        simp at this
    | some w =>
      cases hr : row s.out.indexMasks w X.NCL s.st.oracles with
      | error e => simp [hC, hF, hk, hb, hr, bind, Except.bind] at h
      | ok q =>
        obtain ⟨r, os⟩ := q
        simp [hC, hF, hk, hb, hr, bind, Except.bind, pure, Except.pure] at h
        have h := ((S.unmarked_ok _ _).mp h).1
        constructor
        · intro hv
          have := bo.2.2.2.2.1 hv
          simp at this
        · intro hv
          refine ⟨w, r, os, ((bo.2.2.2.2.2 hv).1).symm, hr, ?_⟩
          rw [← h]
          have hF' : ({ s with out := pendingKept s.out r, st := { s.st with oracles := os } } :
              S).fork? = some F := hF
          simp [S.leaveLink, S.inLink, hF', S.live, S.link?]

/-- (On the last four clauses: the walk's state of the calls behind «cleared» IS the link's live
  copy: at the chain's last seam, behind the head's link, no «laid» follows, and the finish reads
  the walk's state; and a claim
on single rows only NAMES its messages by number: so the statement's codes and groups are said too;
  its messages: clear_messages.)
**THE LIVE STATE OF THE CALLS IS CARRIED WHOLE ACROSS A LINK's END.** What the link's last call left
  in the live state of the calls (its frame: the rows, the group, what is kept: WHATEVER CLAIM
  STANDS OPEN THERE) is, behind «cleared», the
live state of the calls, to the letter. -/
theorem clear_carries {X : LinkPub} {counts : S → Except String Unit} {left : S → Option WsForkOut}
    {row : RowFn} {s t : S}
    (h : clearWith X counts left row s = .ok t) :
    t.live = s.live ∧ t.book = s.book ∧ t.roots = s.roots ∧ t.rowsOwed = s.rowsOwed ∧ t.failed =
        s.failed ∧ t.req = s.req ∧
      t.check = s.live ∧ t.st.codes = s.st.codes ∧ t.st.groups = s.st.groups ∧ t.atBetween = true :=
          by
  have e := clearWith_eq h
  cases hv : X.fv with
  | false =>
    rw [e.1 hv]
    simp [S.live, S.link?, S.atBetween]
  | true =>
    obtain ⟨w, r, os, _, _, ht⟩ := e.2 hv
    rw [ht]
    simp [S.live, S.link?, S.atBetween]

/-- **THE LAST SEAM, AND EVERY SEAM, WITHOUT THE NEXT «laid».** Behind the chain's last link no
  «laid» follows (its test «a first call is due» and the finish's «no link is still to come» shut
  each other out: seam_carries | seam_rows are empty
there). What «cleared» alone gives: the closing's open claim, by its field, stands in THE WALK's
  state of the calls, which the finish reads; the record stands between two links. -/
theorem clear_rows {X : LinkPub} {counts : S → Except String Unit} {left : S → Option WsForkOut}
    {row : RowFn} {s t : S}
    (h : clearWith X counts left row s = .ok t) :
    t.check.frame.rows = s.live.frame.rows ∧ t.check = s.live ∧ t.atBetween = true := by
  have c := clear_carries h
  exact ⟨by rw [c.2.2.2.2.2.2.1], c.2.2.2.2.2.2.1, c.2.2.2.2.2.2.2.2.2⟩

/-- **THE SEAM.** From behind a link's last call, through «cleared» and the next link's «laid», to
  in front of the next link's first call: the live state of the calls, the book of trees, the number
  of roots, the count of rows owed, the mark
and the request are carried to the letter; the record stands between two links; a first call is due;
  the chain stands at the next link. -/
theorem seam_carries {X : LinkPub} {counts : S → Except String Unit} {left : S → Option WsForkOut}
    {row : RowFn} {l : Nat} {s t u : S}
    (h : clearWith X counts left row s = .ok t) (h' : layFront l t = .ok u) :
    u.live = s.live ∧ u.check = s.live ∧ u.book = s.book ∧ u.roots = s.roots ∧ u.rowsOwed =
        s.rowsOwed ∧ u.failed = s.failed ∧
      u.req = s.req ∧ u.atBetween = true ∧ firstDue s.live = true ∧ s.live.frame.link = l ∧
      u.st.codes = s.st.codes ∧ u.st.groups = s.st.groups := by
  have c := clear_carries h
  have lf := layFront_ok h'
  obtain ⟨C, F, hC, _, _, _, _, _, _, hck, _⟩ := clearWith_ok h
  have hl : s.live = C.check := by simp [S.live, hC]
  rw [lf.1]
  refine ⟨c.1, by rw [hck, hl], c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, c.2.2.2.2.2.1, lf.2.1, ?_,
      ?_,
    c.2.2.2.2.2.2.2.1, c.2.2.2.2.2.2.2.2.1⟩
  · rw [hl, ← hck]; exact lf.2.2.1
  · rw [hl, ← hck]; exact lf.2.2.2

/-- **THE CLOSING's OPEN CLAIM, BY ITS FIELD.** In `verify-on-bytes`'s text the closing of a link
  lays its folded claim on single rows into the frame's field rows («what the last closing has
  returned»: OnBytes/Iop/Req.lean: ReqFrame.rows;
ReqFrame.close writes it, with the next link's number and «a first call is due»), and the next
  link's first call reads it there (the code switch's first argument). THAT FIELD, as the link's
  last call left it in the live state of the calls, is what
stands in the walk's state of the calls in front of the next link's first call. (That a block's own
  text for the closing lays its claim into this field, and into no other, is that kind's law to
  say.) -/
theorem seam_rows {X : LinkPub} {counts : S → Except String Unit} {left : S → Option WsForkOut} {row
    : RowFn} {l : Nat} {s t u : S}
    (h : clearWith X counts left row s = .ok t) (h' : layFront l t = .ok u) :
    u.check.frame.rows = s.live.frame.rows ∧ u.check.frame.keptBefore = s.live.frame.keptBefore ∧
      u.check.frame.group = s.live.frame.group ∧ u.check.frame.mask = s.live.frame.mask := by
  have e := (seam_carries h h').2.1
  rw [e]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Behind the next link's first call «opened» lays the state of the calls, as that call left it,
  into the link's context: the live state of the calls is the walk's, to the letter. -/
theorem openAtt_carries {P : AttPar} {s t : S} (h : openAtt P s = .ok t) : t.live = s.check := by
  have ok := openAtt_ok h
  simp [S.live, ok.2.2.2.2.1]

theorem openLay_carries {P : LayPar} {s t : S} (h : openLay P s = .ok t) : t.live = s.check := by
  have ok := openLay_ok h
  simp [S.live, ok.2.2.2.2.2.1]

/-! ### the reply heard is left as it was (the row «reply_leaves») -/

theorem layFront_leaves {l : Nat} {s t : S} (h : layFront l s = .ok t) : t.out.reply = s.out.reply
    := by
  rw [(layFront_ok h).1]

theorem openAtt_leaves {P : AttPar} {s t : S} (h : openAtt P s = .ok t) :
    t.out.reply = s.out.reply := by
  rw [(openAtt_ok h).2.2.2.2.2.2.2.2.2]

theorem openLay_leaves {P : LayPar} {s t : S} (h : openLay P s = .ok t) :
    t.out.reply = s.out.reply := by
  rw [(openLay_ok h).2.2.2.2.2.2.2.2.2.2]

/-- At every link, the head's among them: whatever the counts, what is left and the row's function
  are. -/
theorem clearWith_leaves {X : LinkPub} {counts : S → Except String Unit} {left : S → Option
    WsForkOut} {row : RowFn} {s t : S}
    (h : clearWith X counts left row s = .ok t) : t.out.reply = s.out.reply := by
  obtain ⟨C, F, _, _, _, _, _, _, _, _, _, h0, h1⟩ := clearWith_ok h
  cases hv : X.fv with
  | false => rw [(h0 hv).1]
  | true =>
    obtain ⟨w, r, os, _, _, hout, _⟩ := h1 hv
    rw [hout]
    rfl

/-! ### room -/

/-- The frame's own number is `verify-on-bytes`'s. A yardstick, no law: see the head. -/
theorem roomOf_eq (links : Array Stages.LinkH) (kCol : Nat) :
    roomOf (links.toList.map (·.fv)) kCol = Stages.indexMasksTaken (Stages.onTable links) kCol := by
  have h : ((links.toList.map (·.fv)).filter id).length = (links.toList.filter (·.fv)).length := by
    rw [List.filter_map, List.length_map]
    rfl
  simp only [roomOf, Stages.indexMasksTaken, Stages.onTable, Batt.masksOf, h]

/-! ### the ledger -/

theorem nextEntry_ge (rows logRows : Nat) : ∀ (fuel n : Nat), n ≤ nextEntry rows logRows fuel n
  | 0, n => by simp [nextEntry]
  | fuel + 1, n => by
    unfold nextEntry
    split
    · exact Nat.le_refl n
    · exact Nat.le_trans (Nat.le_succ n) (nextEntry_ge rows logRows fuel (n + 1))

theorem takeEntry_spec {l l' : Ledger} {c : Nat} (h : takeEntry l = some (c, l')) :
    l.next ≤ c ∧ l'.next = c + 1 ∧ l'.left + 1 = l.left ∧ l.closed = false ∧ l'.closed = false ∧
      l'.rows = l.rows ∧ l'.logRows = l.logRows := by
  unfold takeEntry at h
  split at h
  · rename_i hc
    simp at hc
    simp at h
    obtain ⟨h1, h2⟩ := h
    subst h2
    subst h1
    refine ⟨nextEntry_ge _ _ _ _, rfl, ?_, hc.1, hc.1, rfl, rfl⟩
    show l.left - 1 + 1 = l.left
    omega
  · simp at h

/-- A run of n takings off one ledger: the numbers handed out, in order, and the ledger behind. -/
def takes : Nat → Ledger → Option (List Nat × Ledger)
  | 0, l => some ([], l)
  | n + 1, l =>
    match takeEntry l with
    | none => none
    | some (c, l') => (takes n l').map fun x => (c :: x.1, x.2)

theorem takes_ge : ∀ (n : Nat) {l l' : Ledger} {cs : List Nat}, takes n l = some (cs, l') → ∀ c ∈
    cs, l.next ≤ c
  | 0, l, l', cs, h => by
    unfold takes at h
    cases h
    intro c hc
    cases hc
  | n + 1, l, l', cs, h => by
    unfold takes at h
    split at h
    · simp at h
    · rename_i c₀ l₀ h₀
      cases hx : takes n l₀ with
      | none => simp [hx] at h
      | some x =>
        simp [hx] at h
        obtain ⟨h1, _⟩ := h
        have sp := takeEntry_spec h₀
        intro c hc
        rw [← h1] at hc
        cases hc with
        | head => exact sp.1
        | tail _ hc' =>
          have := takes_ge n (l := l₀) (l' := x.2) (cs := x.1) (by simp [hx]) c hc'
          omega

/-- **No number twice.** The numbers that any run of takings off one ledger hands out rise strictly.
  -/
theorem takes_sorted : ∀ (n : Nat) {l l' : Ledger} {cs : List Nat}, takes n l = some (cs, l') →
    cs.Pairwise (· < ·)
  | 0, l, l', cs, h => by
    unfold takes at h
    cases h
    exact List.Pairwise.nil
  | n + 1, l, l', cs, h => by
    unfold takes at h
    split at h
    · simp at h
    · rename_i c₀ l₀ h₀
      cases hx : takes n l₀ with
      | none => simp [hx] at h
      | some x =>
        simp [hx] at h
        obtain ⟨h1, _⟩ := h
        have sp := takeEntry_spec h₀
        rw [← h1]
        refine List.Pairwise.cons ?_ (takes_sorted n (l := l₀) (l' := x.2) (cs := x.1) (by simp
            [hx]))
        intro c hc
        have := takes_ge n (l := l₀) (l' := x.2) (cs := x.1) (by simp [hx]) c hc
        omega

theorem takes_nodup {n : Nat} {l l' : Ledger} {cs : List Nat} (h : takes n l = some (cs, l')) :
    cs.Nodup :=
  (takes_sorted n h).imp (fun hab => Nat.ne_of_lt hab)

/-! ### link 0 -/

theorem indexMasksAt_ok {room im : Nat} {check : ChainCheck} {os : Array Oracle} (h : indexMasksAt
    room check os = .ok im) :
    check.frame.atStart.size = 1 ∧ check.frame.atStart[0]? = some im ∧
      ∃ x l, os[im]? = some x ∧ x.ledger = some l ∧ room ≤ (if l.closed then 0 else l.left) := by
  unfold indexMasksAt at h
  split at h
  · exact absurd h (by simp)
  · rename_i h1
    split at h
    · exact absurd h (by simp)
    · rename_i im' h2
      split at h
      · exact absurd h (by simp)
      · rename_i x h3
        split at h
        · exact absurd h (by simp)
        · rename_i l h4
          by_cases h5 : room ≤ (if l.closed then 0 else l.left)
          · simp [h5] at h
            subst h
            exact ⟨by simpa using h1, h2, x, l, h3, h4, h5⟩
          · simp [h5] at h

/-- **«opened» at link 0.** -/
theorem openLayZero_ok {P : LayPar} {fvs : List Bool} {kCol : Nat} {s t : S} (h : openLayZero P fvs
    kCol s = .ok t) :
    s.atBetween = true ∧ firstRun s.check = true ∧ s.check.frame.link = 0 ∧ 0 = (if P.p4 then 2 *
        P.g else P.g) ∧
      (∃ im, indexMasksAt (roomOf fvs kCol) s.check s.st.oracles = .ok im ∧
        t.out = { s.out with indexMasks := im }) ∧
      t.link? = some { check := s.check, link := 0, arrayOf := P.X.arrayOf, list := P.X.Tp } ∧
      t.fork? = some (startFork P.X P.ns) ∧ t.check = s.check ∧ t.st = s.st ∧ t.failed = s.failed :=
          by
  unfold openLayZero at h
  cases hB : s.atBetween with
  | false => simp [need, hB, bind, Except.bind] at h
  | true =>
   cases hA : firstRun s.check with
   | false => simp [need, hB, hA, bind, Except.bind] at h
   | true =>
    cases hq : layFirstQuietZero P.X P.p4 P.g P.Tp P.Fp P.ns (roomOf fvs kCol) s.check s.out
        s.st.oracles with
    | error e => simp [need, hB, hA, hq, bind, Except.bind] at h
    | ok a =>
      simp [need, hB, hA, hq, bind, Except.bind, pure, Except.pure] at h
      have hu := (S.unmarked_ok _ _).mp h
      have h := hu.1
      unfold layFirstQuietZero at hq
      cases hi : indexMasksAt (roomOf fvs kCol) s.check s.st.oracles with
      | error e => simp [hi] at hq
      | ok im =>
        cases hf : front P.X 0 s.check { s.out with indexMasks := im } with
        | error e => simp [hi, hf] at hq
        | ok p =>
          obtain ⟨L, o⟩ := p
          have fo := front_ok hf
          by_cases h1 : L.link = (if P.p4 then 2 * P.g else P.g)
          · simp [hi, hf, h1] at hq
            split at hq
            · exact absurd hq (by simp)
            · simp at hq
              have hb' : ({ s with out := a.out } : S).atBetween = true := hB
              have en := enterLay_ok (s := { s with out := a.out }) (L := a.L) (F := a.F) (tl :=
                  P.tl₀) hb'
              rw [h] at en
              subst hq
              have hg := h1
              rw [fo.2.2.1] at hg
              exact ⟨rfl, rfl, fo.2.1, hg, ⟨im, rfl, en.2.2.2.2.1.trans fo.2.2.2⟩, by rw [en.1,
                  fo.2.2.1], en.2.1, en.2.2.1,
                en.2.2.2.1, en.2.2.2.2.2⟩
          · simp [hi, hf, h1] at hq

theorem openLayZero_leaves {P : LayPar} {fvs : List Bool} {kCol : Nat} {s t : S}
    (h : openLayZero P fvs kCol s = .ok t) : t.out.reply = s.out.reply := by
  obtain ⟨im, _, ho⟩ := (openLayZero_ok h).2.2.2.2.1
  rw [ho]

/-! ### the row bears the number taken -/

open VerifiableInference.Desc.First.Pend (pendingRowO) in
theorem pendingRowO_spec {lay : WsLay} {im n : Nat} {o : WsForkOut} {Sh : Params.LinShape} {os os' :
    Array Oracle} {row : TensorRow}
    (h : pendingRowO lay im o n Sh os = .ok (row, os')) :
    ∃ l c l', (os[im]?).bind (·.ledger) = some l ∧ takeEntry l = some (c, l') ∧ row.masks = [(⟨im,
        c⟩, o.beta)] ∧
      os' = os.modify im fun x => { x with ledger := some l' } := by
  unfold pendingRowO at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h)
  all_goals (try (simp at h; done))
  all_goals (
    simp at h
    refine ⟨_, _, _, by assumption, by assumption, ?_, h.2.symm⟩
    rw [← h.1])

/-! ### clear, the ledger and the pile -/

/-- The index-mask message's ledger, as the carried record has it. -/
def ledgerAt (s : S) : Option Ledger := (s.st.oracles[s.out.indexMasks]?).bind (·.ledger)

open VerifiableInference.Desc.First.Pend (pendingRowO) in
/-- **Where a link leaves a row, clear takes JUST ONE entry off the index-mask message's ledger, and
  the row that it lays at the pile's end bears JUST that entry.** -/
theorem clear_row {X : LinkPub} {counts : S → Except String Unit} {left : S → Option WsForkOut} {lay
    : WsLay} {lin : Params.LinShape} {s t : S}
    (h : clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t) (hv :
        X.fv = true) :
    ∃ l c l' w r, ledgerAt s = some l ∧ takeEntry l = some (c, l') ∧ left s = some w ∧
      t.out.pending = s.out.pending ++ [r] ∧ r.masks = [(⟨s.out.indexMasks, c⟩, w.beta)] ∧
      t.out.indexMasks = s.out.indexMasks ∧ ledgerAt t = some l' := by
  obtain ⟨C, F, _, _, _, _, _, _, _, _, _, _, hrow⟩ := clearWith_ok h
  obtain ⟨w, r, os, hw, hr, hout, hst⟩ := hrow hv
  obtain ⟨l, c, l', hl, ht, hm, hos⟩ := pendingRowO_spec hr
  refine ⟨l, c, l', w, r, hl, ht, hw, ?_, hm, ?_, ?_⟩
  · rw [hout]; rfl
  · rw [hout]; rfl
  · unfold ledgerAt
    rw [hout, hst, hos]
    show ((s.st.oracles.modify s.out.indexMasks fun x => { x with ledger := some l'
        })[s.out.indexMasks]?).bind (·.ledger) = some l'
    cases hx : s.st.oracles[s.out.indexMasks]? with
    | none => simp [hx] at hl
    | some x => simp [Array.getElem?_modify, hx]

open VerifiableInference.Desc.First.Pend (pendingRowO) in
/-- **THE STATEMENT's MESSAGES ACROSS A LINK's END**, at the row's function pendingRowO: each
  message behind «cleared» is the message in front but for its ledger; their number is the same.
  (Which ledger turns, and how: clear_row.) -/
theorem clear_messages {X : LinkPub} {counts : S → Except String Unit} {left : S → Option WsForkOut}
    {lay : WsLay} {lin : Params.LinShape} {s t : S}
    (h : clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t) :
    t.st.oracles.size = s.st.oracles.size ∧
      ∀ i : Nat, (t.st.oracles[i]?).map (fun (x : Oracle) => { x with ledger := none }) =
        (s.st.oracles[i]?).map fun (x : Oracle) => { x with ledger := none } := by
  have e := clearWith_eq h
  cases hv : X.fv with
  | false =>
    rw [e.1 hv]
    exact ⟨rfl, fun _ => rfl⟩
  | true =>
    obtain ⟨w, r, os, _, hr, ht⟩ := e.2 hv
    obtain ⟨l, c, l', _, _, _, hos⟩ := pendingRowO_spec hr
    rw [ht, hos]
    refine ⟨by simp, fun i => ?_⟩
    simp only [Array.getElem?_modify]
    split
    · cases s.st.oracles[i]? <;> simp
    · rfl

/-- Each taking starts from the ledger that the taking before it left: nobody else has written it
  between. -/
def Linked : Ledger → List (Nat × Ledger) → Prop
  | _, [] => True
  | l, (c, l') :: rest => takeEntry l = some (c, l') ∧ Linked l' rest

theorem linked_takes : ∀ (rest : List (Nat × Ledger)) (l : Ledger), Linked l rest →
    ∃ e, takes rest.length l = some (rest.map (·.1), e)
  | [], l, _ => ⟨l, rfl⟩
  | (c, l') :: rest, l, h => by
    obtain ⟨e, he⟩ := linked_takes rest l' h.2
    refine ⟨e, ?_⟩
    simp [takes, h.1, he]

/-- **Over a chain, under one named condition.** If each taking starts from the ledger that the
  taking before it left, no entry is handed out twice. -/
theorem linked_nodup {l : Ledger} {rest : List (Nat × Ledger)} (h : Linked l rest) : (rest.map
    (·.1)).Nodup := by
  obtain ⟨e, he⟩ := linked_takes rest l h
  exact takes_nodup he

/-! ### the links' clearings, one after the other -/

open VerifiableInference.Desc.First.Pend (pendingRowO) in
/-- t is what some link's clear, at a record that leaves a row, makes of s. -/
def ClearedBy (lay : WsLay) (lin : Params.LinShape) (s t : S) : Prop :=
  ∃ (X : LinkPub) (counts : S → Except String Unit) (left : S → Option WsForkOut), X.fv = true ∧
    clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t

/-- THE NAMED CONDITION, AT THE CARRIED RECORD: a row of clearings (s, t), each of which finds, as
  the record p in front of it (the start; then the clearing before it) left them, THE NUMBER of the
  index-mask message in the walk's
result AND THAT MESSAGE's LEDGER: WHATEVER RAN BETWEEN HAS TURNED NEITHER. -/
def Kept (lay : WsLay) (lin : Params.LinShape) : S → List (S × S) → Prop
  | _, [] => True
  | p, (s, t) :: rest => s.out.indexMasks = p.out.indexMasks ∧ ledgerAt s = ledgerAt p ∧ ClearedBy
      lay lin s t ∧ Kept lay lin t rest

/-- The row that a clearing lays bears the entry c of the message number im. -/
def Bears (im : Nat) (x : S × S) (c : Nat) : Prop :=
  ∃ (r : TensorRow) (β : E), x.2.out.pending = x.1.out.pending ++ [r] ∧ r.masks = [(⟨im, c⟩, β)]

/-- Clearing by clearing. -/
def AllBear (im : Nat) : List (S × S) → List Nat → Prop
  | [], [] => True
  | x :: xs, c :: cs => Bears im x c ∧ AllBear im xs cs
  | _, _ => False

theorem kept_linked (lay : WsLay) (lin : Params.LinShape) : ∀ (steps : List (S × S)) (p : S) (l :
    Ledger),
    ledgerAt p = some l → Kept lay lin p steps →
      ∃ rest : List (Nat × Ledger), Linked l rest ∧ AllBear p.out.indexMasks steps (rest.map (·.1))
  | [], _, _, _, _ => ⟨[], trivial, trivial⟩
  | (s, t) :: steps, p, l, hp, h => by
    obtain ⟨hi, hs, ⟨X, counts, left, hv, hc⟩, hk⟩ := h
    obtain ⟨l₁, c, l', w, r, h1, h2, _, h4, h5, h6, h7⟩ := clear_row hc hv
    have e : l₁ = l := by
      rw [hs, hp] at h1
      exact (Option.some.inj h1).symm
    subst e
    obtain ⟨rest, hl, hf⟩ := kept_linked lay lin steps t l' h7 hk
    rw [h6, hi] at hf
    rw [hi] at h5
    exact ⟨(c, l') :: rest, ⟨h2, hl⟩, ⟨⟨r, w.beta, h4, h5⟩, hf⟩⟩

/-- **NO ENTRY TWICE, AT THE CARRIED RECORD, UNDER THE NAMED CONDITION Kept:** the rows
  that the links' clearings lay on the pile, one after the other, bear entries OF ONE MESSAGE, the
  index-mask message as the record in front
names it, no two of which are the same. -/
theorem clearings_nodup {lay : WsLay} {lin : Params.LinShape} {steps : List (S × S)} {p : S} {l :
    Ledger}
    (hp : ledgerAt p = some l) (h : Kept lay lin p steps) :
    ∃ cs : List Nat, cs.Nodup ∧ AllBear p.out.indexMasks steps cs := by
  obtain ⟨rest, hl, hf⟩ := kept_linked lay lin steps p l hp h
  exact ⟨rest.map (·.1), linked_nodup hl, hf⟩

#print axioms clear_rows
#print axioms seam_rows
#print axioms clear_messages
#print axioms clearWith_eq
#print axioms clear_carries
#print axioms seam_carries
#print axioms openAtt_carries
#print axioms openLay_carries
#print axioms openLayZero_ok
#print axioms openLayZero_leaves
#print axioms layFront_leaves
#print axioms openAtt_leaves
#print axioms openLay_leaves
#print axioms clearWith_leaves
#print axioms enterAtt_ok
#print axioms enterLay_ok
#print axioms leaveLink_ok
#print axioms nextEntry_ge
#print axioms takes_ge
#print axioms takes_sorted
#print axioms linked_takes
#print axioms kept_linked
#print axioms clearings_nodup
#print axioms clear_row
#print axioms linked_nodup
#print axioms indexMasksAt_ok
#print axioms pendingRowO_spec
#print axioms layFront_ok
#print axioms front_ok
#print axioms back_ok
#print axioms openAtt_ok
#print axioms openLay_ok
#print axioms clearWith_ok
#print axioms roomOf_eq
#print axioms takeEntry_spec
#print axioms takes_nodup

end Johnson.Desc.First.Walk.Law
