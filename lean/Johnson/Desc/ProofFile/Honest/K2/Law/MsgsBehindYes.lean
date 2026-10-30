-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MsgsBehindYes.lean: the kind "the code switch" (K2): BEHIND THE
SENDING INSIDE A YES OF THE KIND's OWN DECISION, EVERY MESSAGE OF THE STATEMENT KEEPS ITS SHAPE, ITS
MARK "SAMPLED" AND ITS SAMPLE ROWS, AND NO MESSAGE COMES: the shared sending's `SameMsgs`
(Johnson/Desc/K1/Law/SeedIs.lean) between the statement that the sending returns and the statement
of the state that the decision returns; and the like through the head's quiet step. WHY: the library
has this with the kind's own `SameTables` (Johnson/Top/H0/K2Hears/BehindSame.lean, Whole.lean,
RowsKept.lean; Johnson/Top/H0/Tw/K2C/HeadQuietSame.lean), which does not read the mark; the record
`K2SeatedL`'s field sends (Honest/K2/SeatedL.lean) asks `SameMsgs`. THE STEPS ARE THOSE FILES',
lemma by lemma, at the stronger relation. No definition; nothing is evaluated.

  `msgs_refl`       every statement against itself
  `msgs_ledger`, `msgs_join`, `msgs_joins`, `msgs_added`   the ground's steps that stand behind a
                    sending: a ledger is shut; a message joins a group; rows are added
  `msgs_behind`     the step behind the sending, up to the statement at which the rows are made
  `msgs_first`      what stands behind a later link's switch
  `msgs_switch`     the switch itself: there is what the sending returns, and from there on
  `yes_msgs`        THE END: at a yes of the kind's own decision: the front x, what the sending
                    returns y, and `SameMsgs` y.st s'.st
  `headOpenQ_msgs`  the head's quiet step

By, sealed, of other authors: `joinP_msgs`, `SameMsgs.trans` (Johnson/Desc/K1/Law/SeedAtRecord.lean)
· `switchE_inv`, `switchBehind_inv`, `link_inv`, `head_inv`, `finish_inv`
(Johnson/Top/H0/Tw/K2C/Closed.lean) · `stands`, `bindOk` (Laws.lean) · `from_rows`
(Johnson/Top/H0/K2Hears/RowsKept.lean) · `headOpenQ_iff`.

Limits. ON THE STATEMENT's MESSAGES ALONE: nothing on the groups, the ledgers or the open rows,
which these steps do turn. One direction: behind a yes. THAT A YES IS SAID ANYWHERE IS NOT SAID.
Nothing on any property.
-/
import Johnson.Top.H0.K2Hears.Whole
import Johnson.Top.H0.Tw.K2C.HeadQuietSame
import Johnson.Top.H0.Tw.K2C.SendsOn
import Johnson.Desc.K1.Law.SeedAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2
open VerifiableInference.Desc.K1 (SameMsgs joinP_msgs)
open VerifiableInference.Desc.Ground (joinP closeLedgerP addRowsP)
open _root_.Tw.K2 (SwIn SwOut switchE switchBehind switchNotices sendByL8 joinG closeLedgerG
  addRowsG firstBehind dOf)

/-- Every statement against itself. -/
theorem msgs_refl (A : Statement) : SameMsgs A A := ⟨rfl, fun _ => rfl⟩

/-- A ledger is shut. -/
theorem msgs_ledger {A A' : Statement} {o : Nat} (h : closeLedgerG A o = .ok A') :
    SameMsgs A A' := by
  unfold closeLedgerG at h
  split at h
  · rename_i d hd
    cases h
    unfold closeLedgerP at hd
    split at hd
    · cases hd
      show SameMsgs A (OnBytes.Slice.closeLedgers A [o])
      refine ⟨OnBytes.Slice.closeLedgers_codes _ _, fun i => ?_⟩
      rw [OnBytes.Slice.ProxRun.closeLedgers_get, Option.map_map]
      congr 1
      funext x
      show ((if i ∈ [o] then OnBytes.Slice.ProxRun.shut x else x).shape,
        (if i ∈ [o] then OnBytes.Slice.ProxRun.shut x else x).sampled,
        (if i ∈ [o] then OnBytes.Slice.ProxRun.shut x else x).sampleRows) =
          (x.shape, x.sampled, x.sampleRows)
      split <;> rfl
    · cases hd
  · cases h

/-- A message joins a group. -/
theorem msgs_join {A A' : Statement} {g o : Nat} {kept : Bool} (h : joinG A g o kept = .ok A') :
    SameMsgs A A' := by
  unfold joinG at h
  split at h
  · rename_i d hd
    cases h
    exact joinP_msgs (dOf A) d g o kept hd
  · cases h

/-- Messages join a group, one behind the other. -/
theorem msgs_joins {α : Type} (g : Nat) (f : α → Nat) (k : α → Bool) : ∀ (l : List α)
    (A A' : Statement), l.foldlM (fun T p => joinG T g (f p) (k p)) A = .ok A' → SameMsgs A A'
  | [], A, A', h => by
    cases h
    exact msgs_refl A
  | p :: l, A, A', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨A1, h1, h2⟩ := bindOk h
    exact (msgs_join h1).trans (msgs_joins g f k l A1 A' h2)

/-- Rows are added to a group. -/
theorem msgs_added {A A' : Statement} {g : Nat} {rows : List OnBytes.Row}
    (h : addRowsG A g rows = .ok A') : SameMsgs A A' := by
  unfold addRowsG at h
  split at h
  · rename_i d hd
    cases h
    unfold addRowsP at hd
    split at hd
    · rw [from_rows g rows _ d hd]
      obtain ⟨e1, e2⟩ := OnBytes.Slice.withRows_oracles g rows (dOf A).st
      exact ⟨e2, fun _ => by rw [e1]; rfl⟩
    · cases hd
  · cases h

/-- The step behind the sending, up to the statement at which the rows are made. -/
theorem msgs_behind {i : SwIn} {o : SwOut} {c : Code} {y : Array E} {S1 S2 S3 : Statement}
    {rows : List OnBytes.Row} (h : BehindIs i o c y S1 S2 S3 rows) : SameMsgs i.st S3 := by
  have a : SameMsgs i.st S1 := by
    have hl := h.hLedger
    split at hl
    · exact msgs_ledger hl
    · cases hl
      exact msgs_refl _
  have b : SameMsgs S1 S2 := msgs_join h.hJoinG
  have d : SameMsgs S2 S3 := by
    have hk := h.hJoinKept
    rw [← Array.foldlM_toList] at hk
    exact msgs_joins (α := Nat × KeptTarget) i.grp (fun p => p.1) (fun p => p.2.keptAgain) _ S2 S3
      hk
  exact (a.trans b).trans d

/-- What stands behind a later link's switch. -/
theorem msgs_first {A A' : Statement} {x : _root_.Tw.K2.Front} {s : Switched} {plain : List E}
    {f : ReqFrame} {mine : Array Nat} (h : firstBehind A x s plain = .ok (A', f, mine)) :
    SameMsgs A A' := by
  unfold firstBehind at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i A'' hS
          have e : A'' = A' := by
            injection h with h1
            exact (Prod.mk.inj h1).1
          rw [e] at hS
          exact msgs_joins (α := OnBytes.Params.ReqMessage × Nat) x.f.group (fun y => y.2)
            (fun y => decide (0 < y.1.life)) _ A A' hS

/-- **The switch itself.** -/
theorem msgs_switch {p : P2} {s9 : _root_.Tw.K2.S9} {x : _root_.Tw.K2.Front} {r₁ r₂ : Fmt.RoundView}
    {cols : List _root_.Tw.K2.Col} {w : SwOut} {roots : Nat}
    (h : switchE switchBehind (par9 p) sendByL8 s9 x r₁ r₂ cols = .ok (w, roots)) :
    ∃ y, sendByL8 (par9 p) x.st s9.book s9.roots s9.settled (switchNotices x.T x.others) r₁ r₂ =
        .ok y ∧ SameMsgs y.st w.st := by
  obtain ⟨y, hs⟩ := switchE_inv h
  obtain ⟨c, Y, S1, S2, S3, rows, hB⟩ := switchBehind_inv hs.hBehind
  exact ⟨y, hs.hSend, (msgs_behind hB).trans (msgs_added hB.hAdded)⟩

/-- **AT A YES OF THE KIND's OWN DECISION**: the front, what the sending returns, and from there on
every message is as it was. -/
theorem yes_msgs {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : decideWith sendByL8 p s [r₁, r₂] gs = .ok s') :
    ∃ (x : _root_.Tw.K2.Front) (y : _root_.Tw.K2.Sent), FrontOf p s x ∧
      sendByL8 (par9 p) x.st s.book s.roots s.noneWaits (switchNotices x.T x.others) r₁ r₂ =
        .ok y ∧ SameMsgs y.st s'.st := by
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨a, b, x, w, roots, A', f, mine, e, hl⟩ := link_inv hp h
    cases e
    obtain ⟨y, hy, hm⟩ := msgs_switch hl.hSwitch
    have hst : s'.st = A' := congrArg (fun t : S => t.st) hl.hOut
    exact ⟨x, y, Or.inl ⟨hp, hl.hFront⟩, hy, by rw [hst]; exact hm.trans (msgs_first hl.hBehind)⟩
  · obtain ⟨a, b, o, G, w, roots, e, hl⟩ := head_inv hp h
    cases e
    obtain ⟨y, hy, hm⟩ := msgs_switch hl.hSwitch
    have hst : s'.st = w.st := congrArg (fun t : S => t.st) hl.hOut
    exact ⟨_, y, Or.inr (Or.inl ⟨hp, o, G, hl.hHere, hl.hGroup, rfl⟩), hy, by rw [hst]; exact hm⟩
  · obtain ⟨a, b, o, G, w, roots, e, hl⟩ := finish_inv hp h
    cases e
    obtain ⟨y, hy, hm⟩ := msgs_switch hl.hSwitch
    have hst : s'.st = w.st := congrArg (fun t : S => t.st) hl.hOut
    exact ⟨_, y, Or.inr (Or.inr ⟨hp, o, G, hl.hHere, hl.hLaid, rfl⟩), hy, by rw [hst]; exact hm⟩

/-- **The head's quiet step.** -/
theorem headOpenQ_msgs {P : HeadPar} {s s' : S} (h : headOpenQ P s = .ok s') :
    SameMsgs s.st s'.st := by
  obtain ⟨a, st, f, mine, L, out, y, cov, s₁, b, k⟩ := (headOpenQ_iff P s s').1 h
  have e : s'.st = st := by rw [k.out']
  rw [e]
  exact msgs_first k.behind

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.msgs_refl
#print axioms ProofFile.Honest.K2.Law.msgs_ledger
#print axioms ProofFile.Honest.K2.Law.msgs_join
#print axioms ProofFile.Honest.K2.Law.msgs_joins
#print axioms ProofFile.Honest.K2.Law.msgs_added
#print axioms ProofFile.Honest.K2.Law.msgs_behind
#print axioms ProofFile.Honest.K2.Law.msgs_first
#print axioms ProofFile.Honest.K2.Law.msgs_switch
#print axioms ProofFile.Honest.K2.Law.yes_msgs
#print axioms ProofFile.Honest.K2.Law.headOpenQ_msgs
