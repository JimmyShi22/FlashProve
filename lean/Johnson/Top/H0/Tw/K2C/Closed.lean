-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/Closed.lean: the kind «the code switch»: THE CLOSED FORM OF A YES: WHAT THE
TEXT's YES IS, AS EQUATIONS BETWEEN PURE FUNCTIONS' VALUES: AT EVERY INPUT («if and only if» at the
two inner layers; at the outer ones the direction from a yes to the equations): so that a law on
what the switch hands on can start from an
equation and not from the text. No Mathlib. No soundness is claimed: EVERY HEART STAYS A NAME
(swRows · targetOk · rowsCan · rowsSymbols · symbolsAt · openOne · the sending · the plain ground's
joins · the walk's firstKept): inversions, no meaning.
  locPositions_iff    the round «LOC» closes ⇔ [G1 … G7] hold, and then its positions are
  Positions.ofDraws logN (the draws)
  switchBehind_iff    the step behind the sending says yes with o ⇔ there are the old main code, the
  symbols y, the statements S1 S2 S3 and the rows with: the code is in the list [G30] · LOC closes
  at its log-length · readOld gives (o.book, o.opened, y) [G8 … G16] ·
                      g's ledger [G31] · g joins · the kept join [G17-G22] · the group is there, its
                      test not begun [G32] · rowsCan S3 old T kept pos y, and so swRows S3 old T g
                      kept pos y = some rows [G33] · addRowsG S3 grp rows = o.st [G23-G29] · o.out =
                      the numbers cut as the target says, with the positions
  switchE_inv         guard, sending and the step behind: settled [S4] · the entry LOC counts no
  rows [S3] · targetOk [G0] · the sending = y · it took no more items than the message holds [S5] ·
  it laid as many trees as the entry has roots [S6] · switchBehind at just these arguments = w
  link_inv            decide's yes at a link, whole: in range [G34] · the record stands between the
  links · a first call is due [W0] · two rounds [S1] · firstFront = x [F0-F6] · no plain scalar is
  due [S2] · switchE = (w, roots) · firstBehind = (S', f, mine) [F7-F9, the joins] ·
                      every column taken [B1] · the group is the plan's [G35] · AND THE RECORD
                      BEHIND IS GIVEN FIELD BY FIELD; head_inv | finish_inv: the like at the head's
                      link and at the finish
  switchE_numbers · yesPositions · yesCode    a yes ⇒ round 2 drew just p.positions positions; the
  carried rows' main code is there and its log-length is p.logN: the fence of [G34], the positions
  and the code stand at one number
NOT HERE: the converse at the outer layers; openOne's, the sending's and the plain ground's own
inversions.

-/
import Johnson.Top.H0.Tw.K2C.Laws
import Johnson.Top.H0.Tw.K2.RowsMadeAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (SwIn SwOut locPositions readOld closeLedgerG joinG addRowsG switchBehind switchE
    firstEW chainFirstEW firstFront firstBehind switchGuard switchNotices firstFalse)
open VerifiableInference.Desc.Ground (ok rowsL)
open Johnson.Desc.First.Walk (firstDue firstKept)

/-- [G1 … G7], as one Bool: the text's own seven conditions. -/
def locOk (i : SwIn) (logN : Nat) : Bool :=
  !(i.entry.name != "LOC") && !(i.entry.drawNZ != 0) && i.settled && !(i.itemsLeft != 0) &&
    (i.drawn.elems.length == i.entry.drawE && i.drawn.poss.length == i.entry.poss &&
        i.drawn.trits.length == i.entry.trits) &&
    (i.entry.logN == logN && decide (0 < i.entry.poss)) && i.drawn.elems.isEmpty

theorem locPositions_iff (i : SwIn) (logN : Nat) (pos : Positions) :
    locPositions i logN = .ok pos ↔ locOk i logN = true ∧ pos = Positions.ofDraws logN
        i.drawn.poss := by
  unfold locPositions locOk
  cases (i.entry.name != "LOC") <;> cases (i.entry.drawNZ != 0) <;> cases i.settled <;> cases
      (i.itemsLeft != 0) <;>
    cases (i.drawn.elems.length == i.entry.drawE && i.drawn.poss.length == i.entry.poss &&
        i.drawn.trits.length == i.entry.trits) <;>
    cases (i.entry.logN == logN && decide (0 < i.entry.poss)) <;> cases i.drawn.elems.isEmpty <;>
        simp [eq_comm]

/-- What the switch returns, of the numbers that the sending gave and the positions. -/
def outOf (i : SwIn) (pos : Positions) : Switched :=
  { g := i.ids.getD 0 noId, kept := i.ids.extract 1 (1 + i.T.kept.size),
    others := i.ids.extract (1 + i.T.kept.size) i.ids.size, positions := pos }

/-- The closed form of the step behind the sending. -/
structure BehindIs (i : SwIn) (o : SwOut) (c : Code) (y : Array E) (S1 S2 S3 : Statement) (rows :
    List OnBytes.Row) : Prop where
  hCode : i.st.codes.base[i.old.code]? = some c
  hLoc : locOk i c.logN = true
  hRead : readOld i (Positions.ofDraws c.logN i.drawn.poss) = .ok (o.book, o.opened, y)
  hLedger : (if 0 < i.T.shape.maskRows then closeLedgerG i.st (i.ids.getD 0 noId) else
      .ok i.st) = .ok S1
  hJoinG : joinG S1 i.grp (i.ids.getD 0 noId) false = .ok S2
  hJoinKept : ((i.ids.extract 1 (1 + i.T.kept.size)).zip i.T.kept).foldlM (fun S p =>
      joinG S i.grp p.1 p.2.keptAgain) S2 = .ok S3
  hGroup : ok (rowsL S3 i.grp) = true
  hCan : _root_.Tw.K2.rowsCan S3 i.old i.T (i.ids.extract 1 (1 + i.T.kept.size)) (Positions.ofDraws
      c.logN i.drawn.poss) y = true
  hRows : VerifiableInference.Desc.Own.swRows S3 i.old i.T (i.ids.getD 0 noId) (i.ids.extract 1 (1 +
      i.T.kept.size)) (Positions.ofDraws c.logN i.drawn.poss) y = some rows
  hAdded : addRowsG S3 i.grp rows = .ok o.st
  hOut : o.out = outOf i (Positions.ofDraws c.logN i.drawn.poss)

theorem switchBehind_inv {i : SwIn} {o : SwOut} (h : switchBehind i = .ok o) :
    ∃ c y S1 S2 S3 rows, BehindIs i o c y S1 S2 S3 rows := by
  unfold switchBehind at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  · rename_i _ c hc _ pos hp _ r hr hm _ S1 h1 _ S2 h2 _ S3 h3 hg hk _ S4 h4
    obtain ⟨B, left, y⟩ := r
    obtain ⟨hl, rfl⟩ := (locPositions_iff i c.logN pos).1 hp
    have hk' : _root_.Tw.K2.rowsCan S3 i.old i.T (i.ids.extract 1 (1 + i.T.kept.size))
        (Positions.ofDraws c.logN i.drawn.poss) y = true := by simpa using hk
    obtain ⟨rows, hw⟩ :=
        Option.isSome_iff_exists.1 (_root_.Tw.K2.rowsCan_someOwn (g := i.ids.getD 0 noId) hk')
    simp only [hw, Option.getD_some] at h4
    cases h
    exact ⟨c, y, S1, S2, S3, rows, hc, hl, hr, by rw [if_pos hm]; exact h1, h2, h3, by
        simpa using hg, hk', hw, h4, rfl⟩
  · rename_i _ c hc _ pos hp _ r hr hm _ S2 h2 _ S3 h3 hg hk _ S4 h4
    obtain ⟨B, left, y⟩ := r
    obtain ⟨hl, rfl⟩ := (locPositions_iff i c.logN pos).1 hp
    have hk' : _root_.Tw.K2.rowsCan S3 i.old i.T (i.ids.extract 1 (1 + i.T.kept.size))
        (Positions.ofDraws c.logN i.drawn.poss) y = true := by simpa using hk
    obtain ⟨rows, hw⟩ :=
        Option.isSome_iff_exists.1 (_root_.Tw.K2.rowsCan_someOwn (g := i.ids.getD 0 noId) hk')
    simp only [hw, Option.getD_some] at h4
    cases h
    exact ⟨c, y, i.st, S2, S3, rows, hc, hl, hr, by rw [if_neg hm], h2, h3, by
        simpa using hg, hk', hw, h4, rfl⟩

theorem switchBehind_of {i : SwIn} {o : SwOut} {c y S1 S2 S3 rows} (b : BehindIs i o c y S1 S2 S3
    rows) : switchBehind i = .ok o := by
  have hp := (locPositions_iff i c.logN _).2 ⟨b.hLoc, rfl⟩
  have hl := b.hLedger
  unfold switchBehind
  simp only [bind, Except.bind, pure, Except.pure, b.hCode, hp, b.hRead]
  have ho := b.hOut
  by_cases hm : 0 < i.T.shape.maskRows
  · simp only [hm, if_true] at hl
    simp only [hm, if_true, hl, b.hJoinG, b.hJoinKept, b.hGroup, b.hCan, b.hRows, Option.getD_some,
        b.hAdded]
    cases o
    simp_all [outOf]
  · simp only [hm, if_false] at hl
    cases hl
    simp only [hm, if_false, b.hJoinG, b.hJoinKept, b.hGroup, b.hCan, b.hRows, Option.getD_some,
        b.hAdded]
    cases o
    simp_all [outOf]

theorem switchBehind_iff (i : SwIn) (o : SwOut) :
    switchBehind i = .ok o ↔ ∃ c y S1 S2 S3 rows, BehindIs i o c y S1 S2 S3 rows :=
  ⟨switchBehind_inv, fun ⟨_, _, _, _, _, _, b⟩ => switchBehind_of b⟩


/-! ### guard, sending, the step behind -/

/-- The arguments that the step behind the sending is handed. -/
def behindArgs (P : _root_.Tw.K2.Par9) (x : _root_.Tw.K2.Front) (y : _root_.Tw.K2.Sent) (rL :
    Fmt.RoundView) (cols : List _root_.Tw.K2.Col) : SwIn :=
  ⟨y.st, y.book, P.firstTree, cols, x.f.rows, x.T, x.f.group, y.ids, P.eLoc, P.eSeed.rows == 0,
      rL.drawn, rL.vals.length - y.took⟩

structure SwitchIs (behind : SwIn → Except String SwOut) (P : _root_.Tw.K2.Par9) (send :
    _root_.Tw.K2.SendFn) (s : _root_.Tw.K2.S9) (x : _root_.Tw.K2.Front)
    (rS rL : Fmt.RoundView) (cols : List _root_.Tw.K2.Col) (w : SwOut) (roots : Nat) (y :
               _root_.Tw.K2.Sent) : Prop where
  hSettled : s.settled = true
  hRows : P.eLoc.rows = 0
  hGuard : switchGuard x.st x.f.rows x.T = true
  hSend : send P x.st s.book s.roots s.settled (switchNotices x.T x.others) rS rL = .ok y
  hTook : y.took ≤ rL.vals.length
  hTrees : y.roots = s.roots + P.eSeed.roots
  hBehind : behind (behindArgs P x y rL cols) = .ok w
  hRoots : roots = y.roots

theorem switchE_inv {behind P send s x rS rL cols w roots}
    (h : switchE behind P send s x rS rL cols = .ok (w, roots)) : ∃ y,
        SwitchIs behind P send s x rS rL cols w roots y := by
  unfold switchE at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  rename_i h1 h2 h3 _ y hs ht hT _ w' hb
  cases h
  exact ⟨y, by simpa using h1, by simpa using h2, by simpa using h3, hs, by omega, by
      simpa using hT, hb, rfl⟩

theorem firstEW_inv {behind P send} {s : _root_.Tw.K2.S9} {rounds cols t left} (h : firstEW behind P
    send s rounds cols = .ok (t, left)) :
    ∃ rS rL x w roots S' f mine, rounds = [rS,
        rL] ∧ firstFront s.st s.frame = .ok x ∧ s.plain.length = x.plain ∧
      switchE behind P send s x rS rL cols = .ok (w,
          roots) ∧ firstBehind w.st x w.out s.plain = .ok (S', f, mine) ∧
      t = ⟨S', w.book, roots, f, [], P.eLoc.rows == 0⟩ ∧ left = w.opened := by
  unfold firstEW at h
  split at h
  · rename_i rS rL
    obtain ⟨x, hx, h⟩ := bindOk h
    dsimp only at h
    split at h
    · cases h
    · rename_i hpl
      obtain ⟨_, _, h⟩ := bindOk h
      obtain ⟨⟨w, roots⟩, hw, h⟩ := bindOk h
      dsimp only at h
      obtain ⟨⟨S', f, mine⟩, hb, h⟩ := bindOk h
      cases h
      exact ⟨rS, rL, x, w, roots, S', f, mine, rfl, hx, by simpa using hpl, hw, hb, rfl, rfl⟩
  · cases h

theorem chainFirstEW_inv {behind P send} {s : _root_.Tw.K2.S9C} {rounds cols u left} (h :
    chainFirstEW behind P send s rounds cols = .ok (u, left)) :
    firstDue s.check = true ∧ ∃ t, firstEW behind P send ⟨s.st, s.book, s.roots, s.check.frame, [],
        s.settled⟩ rounds cols = .ok (t, left) ∧
      u = ⟨t.st, t.book, t.roots, firstKept s.check t.frame t.frame.own, t.settled⟩ := by
  unfold chainFirstEW at h
  split at h
  · cases h
  · rename_i hd
    obtain ⟨⟨t, l⟩, ht, h⟩ := bindOk h
    cases h
    exact ⟨by simpa using hd, t, ht, rfl⟩

theorem rightGroup_eq {p : P2} {g : Nat} (h : rightGroup p g = .ok ()) : g = p.grp := by
  unfold rightGroup at h
  split at h
  · rename_i c
    simpa using c
  · cases h

/-- The front of a link's switch keeps the frame's carried rows. -/
theorem firstFront_rows {S0 : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front} (h : firstFront S0
    f = .ok x) : x.f.rows = f.rows := by
  unfold firstFront at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  cases h
  rfl

/-! ### decide's yes at a link, whole -/

structure LinkIs (snd : _root_.Tw.K2.SendFn) (p : P2) (s : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat
           × List UInt64))) (s' : S)
    (x : _root_.Tw.K2.Front) (w : SwOut) (roots : Nat) (S' : Statement) (f : ReqFrame) (mine : Array
        Nat) : Prop where
  hRange : ∀ q ∈ r₂.drawn.poss, q < 2 ^ p.logN
  hHere : s.here = .between
  hDue : firstDue s.check = true
  hFront : firstFront s.st s.check.frame = .ok x
  hPlain : x.plain = 0
  hSwitch : switchE switchBehind (par9 p) snd ⟨s.st, s.book, s.roots, s.check.frame, [],
      s.noneWaits⟩ x r₁ r₂ (flat p gs) = .ok (w, roots)
  hBehind : firstBehind w.st x w.out [] = .ok (S', f, mine)
  hTaken : w.opened = [] ∧ gs.length = p.read.length
  hGrp : f.group = p.grp
  hOut : s' = { s with st := S', book := w.book, roots := roots, check := firstKept s.check f f.own,
                       rowsOwed := none }

theorem link_inv {snd p s rs gs s'} (hp : p.stands = .link) (h : decideWith snd p s rs gs = .ok s')
    :
    ∃ r₁ r₂ x w roots S' f mine, rs = [r₁, r₂] ∧ LinkIs snd p s r₁ r₂ gs s' x w roots S' f mine :=
        by
  have hy := decideWith_yes h
  unfold decideWith at h
  simp only at h
  split at h
  · cases h
  · split at h
    · rename_i hst hh
      obtain ⟨⟨u, left⟩, hx, h⟩ := bindOk h
      obtain ⟨_, ha, h⟩ := bindOk h
      obtain ⟨_, hg, h⟩ := bindOk h
      cases h
      obtain ⟨hd, t, ht, rfl⟩ := chainFirstEW_inv hx
      obtain ⟨rS, rL, x, w, roots, S', f, mine, rfl, hf, hpl, hw, hb, rfl, rfl⟩ := firstEW_inv ht
      have hr : ∀ q ∈ rL.drawn.poss, q < 2 ^ p.logN := by
        have := hy.inRange
        simp [inRange] at this
        exact this
      have hl : w.opened = [] := by
        unfold allTaken at ha
        split at ha
        · rename_i c
          simp at c
          exact c.1
        · cases ha
      exact ⟨rS, rL, x, w, roots, S', f, mine, rfl, hr, hh, hd, hf, by
          simpa using hpl.symm, hw, hb, ⟨hl, hy.groups⟩, rightGroup_eq hg, rfl⟩
    · rename_i hst _
      rw [hp] at hst
      cases hst
    · rename_i hst _
      rw [hp] at hst
      cases hst
    · cases h


/-! ### the reading of the old rows -/

structure ReadIs (i : SwIn) (pos : Positions) (B : TreeBook) (left : List _root_.Tw.K2.Col) (y :
    Array E)
    (places : Array (Nat × Nat)) (cols : Array (Nat × Array Nat × Array (Array F))) (opened : Array
        (Array Column)) : Prop where
  hPlaces : (singleRowsOracles i.old).mapM (fun o => i.book.place[o]?) = some places
  hAll : ((listOfT (places.map (·.1)).toList).all fun t =>
      ((i.book.trees[t]?).map (·.parts)).getD #[] |>.all (singleRowsOracles i.old).contains) = true
  hOpen : (listOfT (places.map (·.1)).toList).foldlM (fun s t =>
      _root_.Tw.K2.openOne i.st i.firstTree pos i.book t s) (i.book, i.opened, #[]) = .ok (B, left,
          cols)
  hSymbols : ((singleRowsOracles i.old).zip places).mapM (fun y =>
      VerifiableInference.Desc.Own.symbolsAt i.st i.book pos cols.toList y.1 y.2) = some opened
  hLayout : VerifiableInference.Desc.Own.rowsSymbols i.old opened pos.all.size = some y

theorem readOld_inv {i : SwIn} {pos B left y} (h : readOld i pos = .ok (B, left,
    y)) : ∃ places cols opened, ReadIs i pos B left y places cols opened := by
  unfold readOld at h
  simp only at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  rename_i _ places hp ha _ B' left' cols ho _ opened hs _ y' hl
  cases h
  exact ⟨places, cols, opened, hp, by simpa using ha, ho, hs, hl⟩

/-! ### decide's yes at the head's link and at the finish -/

theorem switchAloneEW_inv {behind P send} {s : _root_.Tw.K2.S9S} {x rounds cols o t left} (h :
    _root_.Tw.K2.switchAloneEW behind P send s x rounds cols = .ok (o, t, left)) :
    ∃ rS rL w roots, rounds = [rS, rL] ∧ switchE behind P send ⟨s.st, s.book, s.roots, x.f, [],
        s.settled⟩ x rS rL cols = .ok (w, roots) ∧
      o = w.out ∧ t = ⟨w.st, w.book, roots, P.eLoc.rows == 0⟩ ∧ left = w.opened := by
  unfold _root_.Tw.K2.switchAloneEW at h
  split at h
  · rename_i rS rL
    obtain ⟨⟨w, roots⟩, hw, h⟩ := bindOk h
    cases h
    exact ⟨rS, rL, w, roots, rfl, hw, rfl, rfl, rfl⟩
  · cases h

/-- What the switch at the head's link is handed as its front. -/
def headFrontOf (s : S) (a : HeadOwn) (T : SwitchTarget) : _root_.Tw.K2.Front :=
  ⟨s.st, a.fr, s.check.frame.atMoment 0,
      ReqFrame.notices (s.check.frame.atMoment 0) ++ #[foldMaskNotice (s.check.frame.foldShape
          s.check.frame.link {})], T, 0⟩

structure HeadIs (snd : _root_.Tw.K2.SendFn) (p : P2) (s : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat
           × List UInt64))) (s' : S)
    (a : HeadOwn) (G : ReqGroup) (w : SwOut) (roots : Nat) : Prop where
  hRange : ∀ q ∈ r₂.drawn.poss, q < 2 ^ p.logN
  hHere : s.here = .head a
  hGrp : a.fr.group = p.grp
  hGroup : s.check.frame.groups[s.check.frame.link]? = some G
  hSwitch : switchE switchBehind (par9 p) snd ⟨s.st, s.book, s.roots, a.fr, [],
      s.noneWaits⟩ (headFrontOf s a G.target) r₁ r₂ (flat p gs) = .ok (w, roots)
  hTaken : w.opened = [] ∧ gs.length = p.read.length
  hOut : s' = { s with st := w.st, book := w.book, roots := roots, rowsOwed := none,
                       here := .head { a with kept := w.out.kept, ids := w.out.others } }

theorem allTaken_left {p : P2} {gs left} (h : allTaken p gs left = .ok ()) : left = [] := by
  unfold allTaken at h
  split at h
  · rename_i c
    simp at c
    exact c.1
  · cases h

theorem head_inv {snd p s rs gs s'} (hp : p.stands = .head) (h : decideWith snd p s rs gs = .ok s')
    :
    ∃ r₁ r₂ a G w roots, rs = [r₁, r₂] ∧ HeadIs snd p s r₁ r₂ gs s' a G w roots := by
  have hy := decideWith_yes h
  unfold decideWith at h
  simp only at h
  split at h
  · cases h
  · split at h
    · rename_i hst _
      rw [hp] at hst
      cases hst
    · rename_i a hst hh
      obtain ⟨_, hg, h⟩ := bindOk h
      obtain ⟨⟨o, t, left⟩, hx, h⟩ := bindOk h
      obtain ⟨_, ha, h⟩ := bindOk h
      cases h
      unfold _root_.Tw.K2.headSwitchEW at hx
      split at hx
      · cases hx
      · rename_i G hG
        obtain ⟨rS, rL, w, roots, rfl, hw, rfl, rfl, rfl⟩ := switchAloneEW_inv hx
        have hr : ∀ q ∈ rL.drawn.poss, q < 2 ^ p.logN := by
          have := hy.inRange
          simp [inRange] at this
          exact this
        exact ⟨rS, rL, a, G, w, roots, rfl, hr, hh, rightGroup_eq hg, hG, hw, ⟨allTaken_left ha,
            hy.groups⟩, rfl⟩
    · rename_i hst _
      rw [hp] at hst
      cases hst
    · cases h

/-- What the switch at the finish is handed as its front. -/
def finFrontOf (s : S) (a : FinOwn) (G : ReqGroup) : _root_.Tw.K2.Front :=
  ⟨s.st, a.fr, [], #[foldMaskNotice (a.fr.foldShape a.fr.link {})], G.target, 0⟩

structure FinIs (snd : _root_.Tw.K2.SendFn) (p : P2) (s : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat
           × List UInt64))) (s' : S)
    (a : FinOwn) (G : ReqGroup) (w : SwOut) (roots : Nat) : Prop where
  hRange : ∀ q ∈ r₂.drawn.poss, q < 2 ^ p.logN
  hHere : s.here = .fin a
  hGrp : a.fr.group = p.grp
  hLaid : a.G = some G
  hSwitch : switchE switchBehind (par9 p) snd ⟨s.st, s.book, s.roots, a.fr, [],
      s.noneWaits⟩ (finFrontOf s a G) r₁ r₂ (flat p gs) = .ok (w, roots)
  hTaken : w.opened = [] ∧ gs.length = p.read.length
  hOut : s' = { s with st := w.st, book := w.book, roots := roots, rowsOwed := none,
                       here := .fin { a with sw := w.out } }

theorem finish_inv {snd p s rs gs s'} (hp : p.stands = .finish) (h : decideWith snd p s rs gs = .ok
    s') :
    ∃ r₁ r₂ a G w roots, rs = [r₁, r₂] ∧ FinIs snd p s r₁ r₂ gs s' a G w roots := by
  have hy := decideWith_yes h
  unfold decideWith at h
  simp only at h
  split at h
  · cases h
  · split at h
    · rename_i hst _
      rw [hp] at hst
      cases hst
    · rename_i hst _
      rw [hp] at hst
      cases hst
    · rename_i a hst hh
      obtain ⟨_, hg, h⟩ := bindOk h
      obtain ⟨G, hG, h⟩ := bindOk h
      have hG' : a.G = some G := by
        cases hq : a.G with
        | none => rw [hq] at hG; cases hG
        | some G' => rw [hq] at hG; cases hG; rfl
      obtain ⟨⟨o, t, left⟩, hx, h⟩ := bindOk h
      obtain ⟨_, ha, h⟩ := bindOk h
      cases h
      obtain ⟨rS, rL, w, roots, rfl, hw, rfl, rfl, rfl⟩ := switchAloneEW_inv hx
      have hr : ∀ q ∈ rL.drawn.poss, q < 2 ^ p.logN := by
        have := hy.inRange
        simp [inRange] at this
        exact this
      exact ⟨rS, rL, a, G, w, roots, rfl, hr, hh, rightGroup_eq hg, hG', hw, ⟨allTaken_left ha,
          hy.groups⟩, rfl⟩
    · cases h


/-! ### the numbers at a yes: the positions are as many as the plan says, and the old main code has
the plan's log-length -/

theorem locOk_numbers {i : SwIn} {logN : Nat} (h : locOk i logN = true) :
    i.drawn.poss.length = i.entry.poss ∧ i.entry.logN = logN ∧ 0 < i.entry.poss := by
  simp [locOk] at h
  exact ⟨h.1.1.2.1.2, h.1.2.1, h.1.2.2⟩

theorem par9_loc (p : P2) : (par9 p).eLoc.poss = p.positions ∧ (par9 p).eLoc.logN = p.logN :=
    ⟨rfl, rfl⟩

/-- Where guard, sending and the step behind say yes at a place's numbers: round 2 drew as many
positions as the plan says, and the carried rows' main code, read in the
statement behind the sending, is there and has the plan's log-length: so the fence of [G34], the
positions and the code stand at ONE number. -/
theorem switchE_numbers {send : _root_.Tw.K2.SendFn} {p : P2} {s : _root_.Tw.K2.S9} {x rS rL cols w
    roots}
    (h : switchE switchBehind (par9 p) send s x rS rL cols = .ok (w, roots)) :
    rL.drawn.poss.length = p.positions ∧ 0 < p.positions ∧
      ∃ y c,
          send (par9 p) x.st s.book s.roots s.settled (switchNotices x.T x.others) rS rL = .ok y ∧
        y.st.codes.base[x.f.rows.code]? = some c ∧ c.logN = p.logN := by
  obtain ⟨y, hs⟩ := switchE_inv h
  obtain ⟨c, _, _, _, _, _, hb⟩ := switchBehind_inv hs.hBehind
  have hn := locOk_numbers hb.hLoc
  exact ⟨hn.1, hn.2.2, y, c, hs.hSend, hb.hCode, hn.2.1.symm⟩

/-- **A yes ⇒ round 2 drew just as many positions as the place's numbers say**, at every sort of
place. -/
def YesPositions : Prop :=
    ∀ snd p s r₁ r₂ gs s', decideWith snd p s [r₁,
        r₂] gs = .ok s' → r₂.drawn.poss.length = p.positions
theorem yesPositions : YesPositions := fun snd p s r₁ r₂ gs s' h => by
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨a, b, x, w, roots, S', f, mine, e, hl⟩ := link_inv hp h
    cases e
    exact (switchE_numbers hl.hSwitch).1
  · obtain ⟨a, b, o, G, w, roots, e, hl⟩ := head_inv hp h
    cases e
    exact (switchE_numbers hl.hSwitch).1
  · obtain ⟨a, b, o, G, w, roots, e, hl⟩ := finish_inv hp h
    cases e
    exact (switchE_numbers hl.hSwitch).1

/-- **A yes ⇒ the carried rows' main code is there and has the place's log-length.** x: THE FRONT
THAT THE SWITCH WAS HANDED, GIVEN WHOLE: at a link what firstFront makes of the record (its rows are
the frame's: firstFront_rows); at the head's link
headFrontOf; at the finish finFrontOf (their rows: the part's own frame's). y: WHAT THE SENDING
RETURNED AT THIS VERY YES; the codes are read in its statement. -/
def YesCode : Prop := ∀ snd p s r₁ r₂ gs s', decideWith snd p s [r₁, r₂] gs = .ok s' →
  ∃ (x : _root_.Tw.K2.Front) (y : _root_.Tw.K2.Sent) (c : Code),
    ((p.stands = .link ∧ firstFront s.st s.check.frame = .ok x) ∨
      (∃ a G,
          s.here = .head a ∧ s.check.frame.groups[s.check.frame.link]? = some G ∧ x = headFrontOf s
              a G.target) ∨
      (∃ a G, s.here = .fin a ∧ a.G = some G ∧ x = finFrontOf s a G)) ∧
    snd (par9 p) x.st s.book s.roots s.noneWaits (switchNotices x.T x.others) r₁ r₂ = .ok y ∧
    y.st.codes.base[x.f.rows.code]? = some c ∧ c.logN = p.logN
theorem yesCode : YesCode := fun snd p s r₁ r₂ gs s' h => by
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨a, b, x, w, roots, S', f, mine, e, hl⟩ := link_inv hp h
    cases e
    obtain ⟨_, _, y, c, hs, hc, hn⟩ := switchE_numbers hl.hSwitch
    exact ⟨x, y, c, .inl ⟨hp, hl.hFront⟩, hs, hc, hn⟩
  · obtain ⟨a, b, o, G, w, roots, e, hl⟩ := head_inv hp h
    cases e
    obtain ⟨_, _, y, c, hs, hc, hn⟩ := switchE_numbers hl.hSwitch
    exact ⟨_, y, c, .inr (.inl ⟨o, G, hl.hHere, hl.hGroup, rfl⟩), hs, hc, hn⟩
  · obtain ⟨a, b, o, G, w, roots, e, hl⟩ := finish_inv hp h
    cases e
    obtain ⟨_, _, y, c, hs, hc, hn⟩ := switchE_numbers hl.hSwitch
    exact ⟨_, y, c, .inr (.inr ⟨o, G, hl.hHere, hl.hLaid, rfl⟩), hs, hc, hn⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.locPositions_iff
#print axioms VerifiableInference.Desc.First.K2.switchBehind_iff
#print axioms VerifiableInference.Desc.First.K2.switchE_inv
#print axioms VerifiableInference.Desc.First.K2.link_inv
#print axioms VerifiableInference.Desc.First.K2.readOld_inv
#print axioms VerifiableInference.Desc.First.K2.head_inv
#print axioms VerifiableInference.Desc.First.K2.finish_inv
#print axioms VerifiableInference.Desc.First.K2.switchE_numbers
#print axioms VerifiableInference.Desc.First.K2.yesPositions
#print axioms VerifiableInference.Desc.First.K2.yesCode
