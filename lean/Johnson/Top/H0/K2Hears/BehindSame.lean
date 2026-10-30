-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/BehindSame.lean: the code switch: WHAT THE STATEMENT S3 IS, in which
the program makes the rows of a switch: the statement behind the sending, with g's ledger shut and
with g and the kept members' new messages joined to the group. These steps leave the codes, every
message's shape and every message's stored sample rows as they were.

HeardRows.lean's yes_rows hides S3 under "there is". Whoever pays the premises of the last join
(Johnson/Top/H0/K2Hands/) from switchFrame's own text needs what S3 is: switchFrame reads of it the
codes, the kept members' shapes and pads; switchOldSamples reads the kept members' stored sample
rows.
  SameTables S S', refl, trans  the same codes; at every number the same shape and the same sample
                    rows; as many messages
  same_ledger, same_join, same_joins  the three steps of the text (closeLedgerG, joinG, the loop
                    over the kept members' new messages)
  behind_same       from the text's own inversion BehindIs (Tw/K2C/Closed.lean): SameTables i.st S3
  rows_of_switch_same, YesRowsSame, yes_rows_same  yes_rows with one clause more: SameTables y.st
                    S3, y what the sending returned
By closeLedgers_codes, closeLedgers_get, closeLedgers_size, joined_shape,
joined_sampleRows. NOT HERE: that the SENDING leaves the codes and the old messages as they were
(from x.st to y.st): the sending snd is a letter in this file (at the sending that K2 runs:
SentKeeps.lean's sent_ok). What firstBehind does at a link (RowsKept.lean's first_keeps). No
soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.HeardRows
import OnBytes.Slice.BlkSentSeat
import OnBytes.Slice.BlkCsRun
import OnBytes.Slice.BlkProxEarlierMessagesAndGroups
import OnBytes.Slice.BlkStLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (SwIn SwOut closeLedgerG joinG addRowsG firstBehind switchE switchBehind dOf)
open VerifiableInference.Desc.Ground (joinP closeLedgerP)

/-- Two statements with the same codes and, message by message, the same shape and sample rows. -/
structure SameTables (S S' : Statement) : Prop where
  codes : S'.codes = S.codes
  size : S'.oracles.size = S.oracles.size
  shape : ∀ i : Nat, (S'.oracles[i]?).map (·.shape) = (S.oracles[i]?).map (·.shape)
  samples : ∀ i : Nat, (S'.oracles[i]?).map (·.sampleRows) = (S.oracles[i]?).map (·.sampleRows)

theorem SameTables.refl (S : Statement) : SameTables S S := ⟨rfl, rfl, fun _ => rfl, fun _ => rfl⟩

theorem SameTables.trans {A B C : Statement} (h : SameTables A B) (k : SameTables B C) :
    SameTables A C :=
  ⟨k.codes.trans h.codes, k.size.trans h.size, fun i => (k.shape i).trans (h.shape i),
    fun i => (k.samples i).trans (h.samples i)⟩

theorem same_ledger {S S' : Statement} {o : Nat} (h : closeLedgerG S o = .ok S') :
    SameTables S S' := by
  unfold closeLedgerG at h
  split at h
  · rename_i d hd
    cases h
    unfold closeLedgerP at hd
    split at hd
    · cases hd
      show SameTables S (OnBytes.Slice.closeLedgers S [o])
      refine ⟨OnBytes.Slice.closeLedgers_codes _ _, OnBytes.Slice.ProxRun.closeLedgers_size _ _,
        fun i => ?_, fun i => ?_⟩
      · rw [OnBytes.Slice.ProxRun.closeLedgers_get, Option.map_map]
        congr 1
        funext x
        show (if i ∈ [o] then OnBytes.Slice.ProxRun.shut x else x).shape = x.shape
        split <;> rfl
      · rw [OnBytes.Slice.ProxRun.closeLedgers_get, Option.map_map]
        congr 1
        funext x
        show (if i ∈ [o] then OnBytes.Slice.ProxRun.shut x else x).sampleRows = x.sampleRows
        split <;> rfl
    · cases hd
  · cases h

theorem same_join {S S' : Statement} {g o : Nat} {kept : Bool} (h : joinG S g o kept = .ok S') :
    SameTables S S' := by
  unfold joinG at h
  split at h
  · rename_i d hd
    cases h
    unfold joinP at hd
    split at hd
    · obtain ⟨G, -, rfl⟩ := Option.map_eq_some_iff.1 hd
      show SameTables S (OnBytes.Slice.withMessageInGroup S g o kept G)
      exact ⟨rfl, by simp [OnBytes.Slice.withMessageInGroup], OnBytes.Slice.joined_shape S g o kept G,
        OnBytes.Slice.joined_sampleRows S g o kept G⟩
    · cases hd
  · cases h

theorem same_joins {α : Type} (g : Nat) (f : α → Nat) (k : α → Bool) : ∀ (l : List α)
    (S S' : Statement), l.foldlM (fun S p => joinG S g (f p) (k p)) S = .ok S' → SameTables S S'
  | [], S, S', h => by
    cases h
    exact SameTables.refl S
  | p :: l, S, S', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨S1, h1, h2⟩ := bindOk h
    exact (same_join h1).trans (same_joins g f k l S1 S' h2)

/-- **What S3 is, as far as the rows' maker reads it.** -/
theorem behind_same {i : SwIn} {o : SwOut} {c : Code} {y : Array E} {S1 S2 S3 : Statement}
    {rows : List OnBytes.Row} (h : BehindIs i o c y S1 S2 S3 rows) : SameTables i.st S3 := by
  have a : SameTables i.st S1 := by
    have hl := h.hLedger
    split at hl
    · exact same_ledger hl
    · cases hl
      exact SameTables.refl _
  have b : SameTables S1 S2 := same_join h.hJoinG
  have d : SameTables S2 S3 := by
    have hk := h.hJoinKept
    rw [← Array.foldlM_toList] at hk
    exact same_joins (α := Nat × KeptTarget) i.grp (fun p => p.1) (fun p =>
        p.2.keptAgain) _ S2 S3 hk
  exact (a.trans b).trans d

theorem rows_of_switch_same {snd : _root_.Tw.K2.SendFn} {p : P2} {s9 : _root_.Tw.K2.S9}
    {x : _root_.Tw.K2.Front} {r₁ r₂ : Fmt.RoundView} {cols w roots}
    (h : switchE switchBehind (par9 p) snd s9 x r₁ r₂ cols = .ok (w, roots)) :
    ∃ y S3 Y rows, RowsFrom snd p s9 x r₁ r₂ cols w y S3 Y rows ∧ SameTables y.st S3 := by
  obtain ⟨y, hs⟩ := switchE_inv h
  obtain ⟨c, Y, S1, S2, S3, rows, hb⟩ := switchBehind_inv hs.hBehind
  have hn : c.logN = p.logN := (locOk_numbers hb.hLoc).2.1.symm
  have hR : _root_.Tw.K2.readOld (behindArgs (par9 p) x y r₂ cols)
      (Positions.ofDraws c.logN r₂.drawn.poss) = .ok (w.book, w.opened, Y) := hb.hRead
  have hM : switchRows S3 x.f.rows x.T (y.ids.getD 0 noId)
      (y.ids.extract 1 (1 + x.T.kept.size)) (Positions.ofDraws c.logN r₂.drawn.poss) Y =
        some rows := hb.hRows
  rw [hn] at hR hM
  exact ⟨y, S3, Y, rows, ⟨hs.hSend, ⟨c, hb.hCode, hn⟩, hR, hM, hb.hAdded⟩, behind_same hb⟩

/-- **A yes of decide, with what S3 is.** -/
def YesRowsSame : Prop := ∀ snd p s r₁ r₂ gs s', decideWith snd p s [r₁, r₂] gs = .ok s' →
  ∃ (x : _root_.Tw.K2.Front) (w : SwOut) (y : _root_.Tw.K2.Sent) (S3 : Statement) (Y : Array E)
    (rows : List OnBytes.Row),
    frontAt p s = some x ∧
    snd (par9 p) x.st s.book s.roots s.noneWaits (_root_.Tw.K2.switchNotices x.T x.others) r₁ r₂ =
      .ok y ∧
    SameTables y.st S3 ∧
    oldRead snd p s r₁ r₂ gs = some (x.f.rows, Positions.ofDraws p.logN r₂.drawn.poss, Y) ∧
    switchRows S3 x.f.rows x.T (y.ids.getD 0 noId) (y.ids.extract 1 (1 + x.T.kept.size))
      (Positions.ofDraws p.logN r₂.drawn.poss) Y = some rows ∧
    addRowsG S3 x.f.group rows = .ok w.st

theorem yes_rows_same : YesRowsSame := fun snd p s r₁ r₂ gs s' h => by
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨a, b, x, w, roots, S', f, mine, e, hl⟩ := link_inv hp h
    cases e
    obtain ⟨y, S3, Y, rows, R, hS⟩ := rows_of_switch_same hl.hSwitch
    have hx : frontAt p s = some x := by simp [frontAt, hp, hl.hFront, Except.toOption]
    exact ⟨x, w, y, S3, Y, rows, hx, R.sent, hS, oldRead_from hx R, R.made, R.laid⟩
  · obtain ⟨a, b, o, G, w, roots, e, hl⟩ := head_inv hp h
    cases e
    obtain ⟨y, S3, Y, rows, R, hS⟩ := rows_of_switch_same hl.hSwitch
    have hx : frontAt p s = some (headFrontOf s o G.target) := by
      simp [frontAt, hp, hl.hHere, hl.hGroup]
    exact ⟨_, w, y, S3, Y, rows, hx, R.sent, hS, oldRead_from hx R, R.made, R.laid⟩
  · obtain ⟨a, b, o, G, w, roots, e, hl⟩ := finish_inv hp h
    cases e
    obtain ⟨y, S3, Y, rows, R, hS⟩ := rows_of_switch_same hl.hSwitch
    have hx : frontAt p s = some (finFrontOf s o G) := by simp [frontAt, hp, hl.hHere, hl.hLaid]
    exact ⟨_, w, y, S3, Y, rows, hx, R.sent, hS, oldRead_from hx R, R.made, R.laid⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.behind_same
#print axioms VerifiableInference.Desc.First.K2.yes_rows_same
