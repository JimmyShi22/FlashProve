-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/HeardRows.lean: the code switch: THE ARRAY THAT IS HEARD IS THE ARRAY
OUT OF WHICH THE ROWS ARE MADE, and the rows are laid into the statement that the text hands on.

Long.lean's yes_oldRead and yes_long say that the old rows' symbols are read, and hide under "there
is" which single rows and which array. Here they are named, at one yes of the text's decide:
  RowsFrom, rows_of_switch, oldRead_from  the record of what one yes of the switch at a front lays
             down (BehindSame.lean and Whole.lean spend it); a yes gives it; the reading of the old
             rows out of it
  YesRows, yes_rows  there are the front x that the switch is handed (frontAt), what the sending
             returned, the step's result w, a statement S3, the array Y and a list rows with:
             oldRead gives (x.f.rows, the positions of round 2's draws at the place's log-length,
             Y); Y has one symbol for each row at each listed position (size_of_rows: the program's
             first guard in switchRows, read off); switchRows S3 x.f.rows x.T (g's number) (the kept
             members' new numbers) (these positions) Y = some rows: THE SAME Y; addRowsG S3
             x.f.group rows = .ok w.st: the rows are laid on the front's group; and the record
             behind: at the head's link and at the finish its statement IS w.st; at a link it is
             what firstBehind makes of w.st.
The sending snd is a letter. No new reasoning: the fields of the text's own inversions (LinkIs,
HeadIs, FinIs, SwitchIs, BehindIs), gathered. Not here: what the rows are (RowsOrder.lean,
RowsAt.lean); what firstBehind does to the rows at a link (RowsKept.lean's first_keeps). No
soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.Long

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (SwIn SwOut readOld switchBehind switchE firstFront switchNotices addRowsG
  firstBehind)

/-- The program's switchRows answers only where the array has one symbol for each row at each listed
position: its first guard, read off. -/
theorem size_of_rows {S old T g anew pos} {Y : Array E} {rows : List OnBytes.Row}
    (h : switchRows S old T g anew pos Y = some rows) : Y.size = pos.all.size * old.rows := by
  by_contra hne
  have hg : (Y.size == pos.all.size * old.rows) = false := by simpa using hne
  have hnone : switchRows S old T g anew pos Y = none := by
    unfold switchRows
    simp [guard, hg]
  rw [hnone] at h
  cases h

/-- What one yes of the switch at a front lays down. -/
structure RowsFrom (snd : _root_.Tw.K2.SendFn) (p : P2) (s9 : _root_.Tw.K2.S9)
    (x : _root_.Tw.K2.Front) (r₁ r₂ : Fmt.RoundView) (cols : List _root_.Tw.K2.Col) (w : SwOut)
    (y : _root_.Tw.K2.Sent) (S3 : Statement) (Y : Array E) (rows : List OnBytes.Row) : Prop where
  sent : snd (par9 p) x.st s9.book s9.roots s9.settled (switchNotices x.T x.others) r₁ r₂ = .ok y
  code : ∃ c, (behindArgs (par9 p) x y r₂ cols).st.codes.base[
    (behindArgs (par9 p) x y r₂ cols).old.code]? = some c ∧ c.logN = p.logN
  read : readOld (behindArgs (par9 p) x y r₂ cols) (Positions.ofDraws p.logN r₂.drawn.poss) =
    .ok (w.book, w.opened, Y)
  made : switchRows S3 x.f.rows x.T (y.ids.getD 0 noId) (y.ids.extract 1 (1 + x.T.kept.size))
    (Positions.ofDraws p.logN r₂.drawn.poss) Y = some rows
  laid : addRowsG S3 x.f.group rows = .ok w.st

theorem rows_of_switch {snd : _root_.Tw.K2.SendFn} {p : P2} {s9 : _root_.Tw.K2.S9}
    {x : _root_.Tw.K2.Front} {r₁ r₂ : Fmt.RoundView} {cols w roots}
    (h : switchE switchBehind (par9 p) snd s9 x r₁ r₂ cols = .ok (w, roots)) :
    ∃ y S3 Y rows, RowsFrom snd p s9 x r₁ r₂ cols w y S3 Y rows := by
  obtain ⟨y, hs⟩ := switchE_inv h
  obtain ⟨c, Y, S1, S2, S3, rows, hb⟩ := switchBehind_inv hs.hBehind
  have hn : c.logN = p.logN := (locOk_numbers hb.hLoc).2.1.symm
  have hR : readOld (behindArgs (par9 p) x y r₂ cols) (Positions.ofDraws c.logN r₂.drawn.poss) =
      .ok (w.book, w.opened, Y) := hb.hRead
  have hM : switchRows S3 x.f.rows x.T (y.ids.getD 0 noId)
      (y.ids.extract 1 (1 + x.T.kept.size)) (Positions.ofDraws c.logN r₂.drawn.poss) Y =
        some rows := hb.hRows
  rw [hn] at hR hM
  exact ⟨y, S3, Y, rows, hs.hSend, ⟨c, hb.hCode, hn⟩, hR, hM, hb.hAdded⟩

/-- The reading, from what the switch lays down at a front that frontAt gives. -/
theorem oldRead_from {snd : _root_.Tw.K2.SendFn} {p : P2} {s : S} {fr : ReqFrame}
    {x : _root_.Tw.K2.Front} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))} {w y S3 Y rows}
    (hx : frontAt p s = some x)
    (R : RowsFrom snd p ⟨s.st, s.book, s.roots, fr, [], s.noneWaits⟩ x r₁ r₂ (flat p gs) w y S3 Y
      rows) :
    oldRead snd p s r₁ r₂ gs = some (x.f.rows, Positions.ofDraws p.logN r₂.drawn.poss, Y) := by
  obtain ⟨c, hc, hn⟩ := R.code
  have hr := R.read
  rw [← hn] at hr ⊢
  exact oldRead_of hx R.sent hc hr

/-- **A yes of decide: the array that is heard is the array out of which the rows are made.** -/
def YesRows : Prop := ∀ snd p s r₁ r₂ gs s', decideWith snd p s [r₁, r₂] gs = .ok s' →
  ∃ (x : _root_.Tw.K2.Front) (w : SwOut) (y : _root_.Tw.K2.Sent) (S3 : Statement) (Y : Array E)
    (rows : List OnBytes.Row),
    frontAt p s = some x ∧
    oldRead snd p s r₁ r₂ gs = some (x.f.rows, Positions.ofDraws p.logN r₂.drawn.poss, Y) ∧
    Y.size = (Positions.ofDraws p.logN r₂.drawn.poss).all.size * x.f.rows.rows ∧
    switchRows S3 x.f.rows x.T (y.ids.getD 0 noId) (y.ids.extract 1 (1 + x.T.kept.size))
      (Positions.ofDraws p.logN r₂.drawn.poss) Y = some rows ∧
    addRowsG S3 x.f.group rows = .ok w.st ∧
    ((p.stands = .link ∧ ∃ f mine, firstBehind w.st x w.out [] = .ok (s'.st, f, mine)) ∨
      (p.stands ≠ .link ∧ s'.st = w.st))

theorem yes_rows : YesRows := fun snd p s r₁ r₂ gs s' h => by
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨a, b, x, w, roots, S', f, mine, e, hl⟩ := link_inv hp h
    cases e
    obtain ⟨y, S3, Y, rows, R⟩ := rows_of_switch hl.hSwitch
    have hx : frontAt p s = some x := by simp [frontAt, hp, hl.hFront, Except.toOption]
    have hst : s'.st = S' := congrArg (fun t : S => t.st) hl.hOut
    refine ⟨x, w, y, S3, Y, rows, hx, oldRead_from hx R, size_of_rows R.made, R.made, R.laid,
      Or.inl ⟨hp, f, mine, ?_⟩⟩
    rw [hst]
    exact hl.hBehind
  · obtain ⟨a, b, o, G, w, roots, e, hl⟩ := head_inv hp h
    cases e
    obtain ⟨y, S3, Y, rows, R⟩ := rows_of_switch hl.hSwitch
    have hx : frontAt p s = some (headFrontOf s o G.target) := by
      simp [frontAt, hp, hl.hHere, hl.hGroup]
    exact ⟨_, w, y, S3, Y, rows, hx, oldRead_from hx R, size_of_rows R.made, R.made, R.laid,
      Or.inr ⟨by rw [hp]; decide, congrArg (fun t : S => t.st) hl.hOut⟩⟩
  · obtain ⟨a, b, o, G, w, roots, e, hl⟩ := finish_inv hp h
    cases e
    obtain ⟨y, S3, Y, rows, R⟩ := rows_of_switch hl.hSwitch
    have hx : frontAt p s = some (finFrontOf s o G) := by simp [frontAt, hp, hl.hHere, hl.hLaid]
    exact ⟨_, w, y, S3, Y, rows, hx, oldRead_from hx R, size_of_rows R.made, R.made, R.laid,
      Or.inr ⟨by rw [hp]; decide, congrArg (fun t : S => t.st) hl.hOut⟩⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.yes_rows
