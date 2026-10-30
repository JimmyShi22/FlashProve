-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/Whole.lean: the code switch: ALL THAT A YES OF THE KIND's OWN
DECISION GIVES, AT ONE SET OF WITNESSES.

yes_rows_kept (RowsKept.lean), yes_rows_same (BehindSame.lean) and yes_switch (K2Hands/AtYes.lean)
each say «there are x, y, S3, Y, rows with …». Whoever wants two of them at once cannot tell that
the witnesses are the same. Here they are gathered in one record and shown at once, at the sending
that the kind runs (sendByL8).
  AtYes       the record: the front x; the target's test says yes at x.st; the sending's own yes;
              what it left and laid (SentOk); the reading of the old rows' own yes; the joins behind
              it leave the tables (SameTables); the old main code, with the place's logN; the array
              that was heard; the rows made out of it in S3; the group in S3; its open rows are
              those that the group had IN FRONT; the group's rows in the record behind are these and
              then the rows made; the record behind has S3's codes, shapes and stored sample rows
  ledger_rows, behind_rows  closing the ledger, and all the steps between the sending and the making
              of the rows, leave every group's open rows: on this the record's clause «its open rows
              are those that the group had in front» stands
  same_added  laying rows into a group leaves the codes and the messages
  atYes_of    AtYes from a yes of the switch at a front and what stands behind it
  YesWhole, yes_whole  a yes of decideWith sendByL8 gives x, y, S3, Y, rows, G, c with AtYes
yes_whole itself adds no reasoning: the three proofs' steps in a row, with the lemmas above. No
soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.RowsKept
import Johnson.Top.H0.K2Hears.SentKeeps
import Johnson.Top.H0.Tw.K2.TargetAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (SwIn SwOut switchE switchBehind switchNotices sendByL8 switchGuard joinG)

/-- All that a yes gives. -/
structure AtYes (p : P2) (s s' : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (x : _root_.Tw.K2.Front) (y : _root_.Tw.K2.Sent) (S3 : Statement) (Y : Array E)
    (rows : List OnBytes.Row) (G : Group) (c : Code) : Prop where
  front : frontAt p s = some x
  check : switchTargetCheck x.st x.f.rows x.T = true
  sentBy : sendByL8 (par9 p) x.st s.book s.roots s.noneWaits (switchNotices x.T x.others) r₁ r₂ =
    .ok y
  sent : SentOk x.st (switchNotices x.T x.others) y.ids y.st
  same : SameTables y.st S3
  code : y.st.codes.base[x.f.rows.code]? = some c
  logN : c.logN = p.logN
  heard : oldRead sendByL8 p s r₁ r₂ gs =
    some (x.f.rows, Positions.ofDraws p.logN r₂.drawn.poss, Y)
  read : ∃ B left, _root_.Tw.K2.readOld (behindArgs (par9 p) x y r₂ (flat p gs))
    (Positions.ofDraws p.logN r₂.drawn.poss) = .ok (B, left, Y)
  made : switchRows S3 x.f.rows x.T (y.ids.getD 0 noId) (y.ids.extract 1 (1 + x.T.kept.size))
    (Positions.ofDraws p.logN r₂.drawn.poss) Y = some rows
  group : S3.groups[x.f.group]? = some G
  before : (x.st.groups[x.f.group]?).map (·.rows) = some G.rows
  kept : (s'.st.groups[x.f.group]?).map (·.rows) = some (G.rows ++ rows.toArray)
  tables : SameTables S3 s'.st

theorem ledger_rows {S S' : Statement} {o : Nat} (h : _root_.Tw.K2.closeLedgerG S o = .ok S')
    (i : Nat) : (S'.groups[i]?).map (·.rows) = (S.groups[i]?).map (·.rows) := by
  unfold _root_.Tw.K2.closeLedgerG at h
  split at h
  · rename_i d hd
    cases h
    unfold VerifiableInference.Desc.Ground.closeLedgerP at hd
    split at hd
    · cases hd
      rfl
    · cases hd
  · cases h

/-- **The steps between the sending and the making of the rows leave every group's open rows.** -/
theorem behind_rows {i : SwIn} {o : SwOut} {c : Code} {y : Array E} {S1 S2 S3 : Statement}
    {rows : List OnBytes.Row} (h : BehindIs i o c y S1 S2 S3 rows) (k : Nat) :
    (S3.groups[k]?).map (·.rows) = (i.st.groups[k]?).map (·.rows) := by
  have a : (S1.groups[k]?).map (·.rows) = (i.st.groups[k]?).map (·.rows) := by
    have hl := h.hLedger
    split at hl
    · exact ledger_rows hl k
    · cases hl
      rfl
  have b : (S2.groups[k]?).map (·.rows) = (S1.groups[k]?).map (·.rows) := join_rows h.hJoinG k
  have d : (S3.groups[k]?).map (·.rows) = (S2.groups[k]?).map (·.rows) := by
    have hk := h.hJoinKept
    rw [← Array.foldlM_toList] at hk
    exact joins_rows (α := Nat × KeptTarget) i.grp (fun p => p.1) (fun p =>
        p.2.keptAgain) _ S2 S3 hk
      k
  exact (d.trans b).trans a

/-- Laying rows into a group leaves the codes and the messages. -/
theorem same_added {S S' : Statement} {g : Nat} {rows : List OnBytes.Row}
    (h : _root_.Tw.K2.addRowsG S g rows = .ok S') : SameTables S S' := by
  unfold _root_.Tw.K2.addRowsG at h
  split at h
  · rename_i d hd
    cases h
    unfold VerifiableInference.Desc.Ground.addRowsP at hd
    split at hd
    · rw [from_rows g rows _ d hd]
      obtain ⟨e1, e2⟩ := OnBytes.Slice.withRows_oracles g rows (_root_.Tw.K2.dOf S).st
      exact ⟨e2, by rw [e1]; rfl, fun _ => by rw [e1]; rfl, fun _ => by rw [e1]; rfl⟩
    · cases hd
  · cases h

/-- From a yes of the switch at a front, and what stands behind it. -/
theorem atYes_of {p : P2} {s s' : S} {s9 : _root_.Tw.K2.S9} {x : _root_.Tw.K2.Front}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))} {w roots}
    (h : switchE switchBehind (par9 p) sendByL8 s9 x r₁ r₂ (flat p gs) = .ok (w, roots))
    (e1 : s9.book = s.book) (e2 : s9.roots = s.roots) (e3 : s9.settled = s.noneWaits)
    (hx : frontAt p s = some x)
    (ho : ∀ y S3 Y rows, RowsFrom sendByL8 p s9 x r₁ r₂ (flat p gs) w y S3 Y rows →
      oldRead sendByL8 p s r₁ r₂ gs =
        some (x.f.rows, Positions.ofDraws p.logN r₂.drawn.poss, Y))
    (hb : ∀ i : Nat, (s'.st.groups[i]?).map (·.rows) = (w.st.groups[i]?).map (·.rows))
    (hb2 : SameTables w.st s'.st) :
    ∃ y S3 Y rows G c, AtYes p s s' r₁ r₂ gs x y S3 Y rows G c := by
  obtain ⟨y, hs⟩ := switchE_inv h
  obtain ⟨c, Y, S1, S2, S3, rows, hB⟩ := switchBehind_inv hs.hBehind
  have hn : c.logN = p.logN := (locOk_numbers hB.hLoc).2.1.symm
  have hR : _root_.Tw.K2.readOld (behindArgs (par9 p) x y r₂ (flat p gs))
      (Positions.ofDraws c.logN r₂.drawn.poss) = .ok (w.book, w.opened, Y) := hB.hRead
  have hM : switchRows S3 x.f.rows x.T (y.ids.getD 0 noId)
      (y.ids.extract 1 (1 + x.T.kept.size)) (Positions.ofDraws c.logN r₂.drawn.poss) Y =
        some rows := hB.hRows
  rw [hn] at hR hM
  have R : RowsFrom sendByL8 p s9 x r₁ r₂ (flat p gs) w y S3 Y rows :=
    ⟨hs.hSend, ⟨c, hB.hCode, hn⟩, hR, hM, hB.hAdded⟩
  have hK := sent_ok hs.hSend
  obtain ⟨G, hG, hG'⟩ := added_rows R.laid
  refine ⟨y, S3, Y, rows, G, c, hx, ?_, by rw [← e1, ← e2, ← e3]; exact hs.hSend, hK,
    behind_same hB, hB.hCode, hn, ho y S3 Y rows R, ⟨_, _, hR⟩, hM, hG, ?_, ?_,
    (same_added R.laid).trans hb2⟩
  · rw [← _root_.Tw.K2.targetOk_eq]
    exact hs.hGuard
  · have e := behind_rows hB x.f.group
    rw [hG] at e
    have e2 : (behindArgs (par9 p) x y r₂ (flat p gs)).st.groups = x.st.groups := hK.groups
    rw [e2] at e
    exact e.symm
  · rw [hb, hG']
    rfl

/-- **A yes of decide, whole.** -/
def YesWhole : Prop := ∀ p s r₁ r₂ gs s', decideWith sendByL8 p s [r₁, r₂] gs = .ok s' →
  ∃ x y S3 Y rows G c, AtYes p s s' r₁ r₂ gs x y S3 Y rows G c

theorem yes_whole : YesWhole := fun p s r₁ r₂ gs s' h => by
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨a, b, x, w, roots, S', f, mine, e, hl⟩ := link_inv hp h
    cases e
    have hx : frontAt p s = some x := by simp [frontAt, hp, hl.hFront, Except.toOption]
    have hst : s'.st = S' := congrArg (fun t : S => t.st) hl.hOut
    exact ⟨x, atYes_of hl.hSwitch rfl rfl rfl hx (fun _ _ _ _ R => oldRead_from hx R)
      (by rw [hst]; exact (first_keeps hl.hBehind).2)
      (by rw [hst]; exact (first_keeps hl.hBehind).1)⟩
  · obtain ⟨a, b, o, G, w, roots, e, hl⟩ := head_inv hp h
    cases e
    have hx : frontAt p s = some (headFrontOf s o G.target) := by
      simp [frontAt, hp, hl.hHere, hl.hGroup]
    have hst : s'.st = w.st := congrArg (fun t : S => t.st) hl.hOut
    exact ⟨_, atYes_of hl.hSwitch rfl rfl rfl hx (fun _ _ _ _ R => oldRead_from hx R)
      (fun i => by rw [hst]) (by rw [hst]; exact SameTables.refl _)⟩
  · obtain ⟨a, b, o, G, w, roots, e, hl⟩ := finish_inv hp h
    cases e
    have hx : frontAt p s = some (finFrontOf s o G) := by simp [frontAt, hp, hl.hHere, hl.hLaid]
    have hst : s'.st = w.st := congrArg (fun t : S => t.st) hl.hOut
    exact ⟨_, atYes_of hl.hSwitch rfl rfl rfl hx (fun _ _ _ _ R => oldRead_from hx R)
      (fun i => by rw [hst]) (by rw [hst]; exact SameTables.refl _)⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.yes_whole
