-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/SendingKeeps.lean.
WHAT IT DOES NOT SHOW. No soundness. Nothing on what is sent. Nothing on the quiet step that a place
joins behind a sending. ON THE TEXT OF ANOTHER KIND's FILES (the kind K1):
Desc/K1/KeepsNext.lean walks the same six
steps for "the next free slot" alone; OnBytes/Tie/Pv/Psc/PscLater.lean's rootTaken_slots and
HideLaws.lean's map_modify_same are called; Desc/First/Att/Claims/Widths.lean (widths_rootTaken: the
columns) is not imported and is not called here.
LETTERS. Under "there is" (sending_at): o, o': pinned by s.here = .head o, s'.here = .head o'.
OBJECT. Desc/K1/AtS.lean's commitAtS P link moment arrays: a segment's later moment, at the carried
record: its decision.
USER. Law/RunsFixed.lean's Alike across the sending of the reads in the head's link.
WHAT IT IS. A SENDING MARKS ARRAYS AS SENT. SHOWN HERE OF THE LEDGER BEHIND IT: the slots (their
number, the next free one, the three lists) are as they were, so is the list of owed claims, and so
are every array's numbers of columns and of rows. Of the ledger's other fields nothing is shown.
SentOnly F G G has F's slots and list of owed claims, and its arrays F's columns and rows.
rootTaken_sent, commitOne_sent ... commitOwn_sent the six steps.
  sending_at        at the head's link: the record behind a yes has the same heard things, tables,
                    reply and request, and a ledger that is SentOnly.
  sending_alike     so the record behind is Alike to the record in front.

-/
import Mathlib
import Johnson.Desc.K1.AtS
import Johnson.Desc.Kinds.Law.RunsFixed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model Desc.Plain
open OnBytes.PscRun (SlotsSame rootTaken_slots Later)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (commitOwn commitAtS laid laterOwn Owing)

/-- G has F's slots and list of owed claims, and its arrays have F's columns and rows. -/
structure SentOnly (F G : Fork) : Prop where
  slots : SlotsSame F G
  cols : G.trees.map (·.K) = F.trees.map (·.K)
  rows : G.trees.map (·.R) = F.trees.map (·.R)
  owed : G.owed = F.owed

theorem SentOnly.refl (F : Fork) : SentOnly F F := ⟨SlotsSame.refl F, rfl, rfl, rfl⟩

theorem SentOnly.trans {F G H : Fork} (a : SentOnly F G) (b : SentOnly G H) : SentOnly F H :=
  ⟨a.slots.trans b.slots, b.cols.trans a.cols, b.rows.trans a.rows, b.owed.trans a.owed⟩

theorem rootTaken_sent (F : Fork) (t w : Nat) : SentOnly F (F.rootTaken t w) :=
  ⟨rootTaken_slots F t w,
    map_modify_same (fun X : HTree => X.K) (fun X => { X with root := some w }) (fun _ => rfl)
      F.trees t,
    map_modify_same (fun X : HTree => X.R) (fun X => { X with root := some w }) (fun _ => rfl)
      F.trees t, rfl⟩

theorem commitOne_sent {L : LinkCtx} {F F' : Fork} {t : Nat} (h : L3.commitOne L F t = .ok F') :
    SentOnly F F' := by
  simp only [L3.commitOne] at h
  split at h <;> split at h <;> first
    | (injection h with h; subst h; exact rootTaken_sent _ _ _)
    | cases h

theorem commitAll_sent {L : LinkCtx} : ∀ (ts : List Nat) (F F' : Fork),
    ts.foldlM (L3.commitOne L) F = .ok F' → SentOnly F F'
  | [], F, F', h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact SentOnly.refl _
  | t :: ts, F, F', h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    cases h1 : L3.commitOne L F t with
    | error e => simp [h1] at h
    | ok F₁ =>
      simp only [h1] at h
      exact (commitOne_sent h1).trans (commitAll_sent ts F₁ F' h)

theorem commitBehind_sent {L L' : LinkCtx} {check : ChainCheck} {F F' : Fork} {ts : List Nat}
    (h : L3.commitBehind L check F ts = .ok (L', F')) : SentOnly F F' := by
  simp only [L3.commitBehind, bind, Except.bind] at h
  cases h1 : ts.foldlM (L3.commitOne L) F with
  | error e => simp [h1] at h
  | ok F₁ =>
    simp only [h1] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact commitAll_sent ts F F₁ h1
    · cases h

theorem commitStep_sent {W : Type} {send : L3.Send W} {ts : List Nat} {s s' : L3.St W}
    {rs : List Fmt.RoundView} (h : L3.commitStep send ts s rs = .ok s') : SentOnly s.F s'.F := by
  simp only [L3.commitStep, bind, Except.bind] at h
  cases h0 : L3.commitFront s.L with
  | error e => simp [h0] at h
  | ok u =>
    simp only [h0] at h
    cases h1 : send s.L.check s.w rs with
    | error e => simp [h1] at h
    | ok x =>
      simp only [h1] at h
      cases h2 : L3.commitBehind s.L x.1 s.F ts with
      | error e => simp [h2] at h
      | ok y =>
        simp only [h2, pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact commitBehind_sent (L' := y.1) (F' := y.2) h2

theorem commitOwn_sent {Cl : Type} {P : K1.Par} {link moment : Nat} {arrays : Option (List Nat)}
    {x y : Owing (L3.St (DState Unit))} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (commitOwn (Cl := Cl) P link moment arrays).decide x rs gs = .ok y) :
    SentOnly x.held.F y.held.F := by
  simp only [commitOwn] at h
  split at h
  · split at h
    · cases h
    · rename_i ts
      cases h1 : L3.commitStep (laterOwn P x.owed) ts x.held rs with
      | error e => simp [h1, Except.map] at h
      | ok z =>
        simp only [h1, Except.map, Except.ok.injEq] at h
        subst h
        exact commitStep_sent h1
  · cases h

/-- **At the head's link: what a sending's yes leaves.** -/
theorem sending_at {Cl : Type} {P : K1.Par} {link moment : Nat} {arrays : Option (List Nat)}
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {o : VerifiableInference.Desc.First.HeadOwn} (ho : s.here = .head o)
    (h : (commitAtS (Cl := Cl) P link moment arrays).decide s rs gs = .ok s') :
    ∃ o', s'.here = .head o' ∧ o'.x = o.x ∧ o'.squaresP = o.squaresP ∧ o'.t = o.t ∧
      o'.opened = o.opened ∧ o'.lookHeard = o.lookHeard ∧ s'.out.reply = s.out.reply ∧
      s'.req = s.req ∧ SentOnly o.F o'.F := by
  simp only [commitAtS] at h
  split at h
  · rename_i L F tl hL hF ht
    cases h1 : (commitOwn (Cl := Cl) P link moment arrays).decide
        { owed := K1.owedOf s, held := { L := L, F := F, tl := tl, w := K1.stateOf s () } } rs
        gs with
    | error e => simp [h1, Except.map] at h
    | ok y =>
      simp only [h1, Except.map, Except.ok.injEq] at h
      have hS := commitOwn_sent h1
      have hop : o.opened = true := by
        unfold S.fork? at hF
        rw [ho] at hF
        by_contra hc
        simp [hc] at hF
      have hFo : o.F = F := by
        unfold S.fork? at hF
        rw [ho] at hF
        simpa [hop] using hF
      subst h
      refine ⟨{ o with L := y.held.L, F := y.held.F }, ?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · simp [S.putFork, S.putLink, laid, ho, hop]
      · simp [S.putFork, S.putLink, laid, ho, hop]
      · simp [S.putFork, S.putLink, laid, ho, hop]
      · rw [hFo]
        exact hS
  · cases h

/-- **So the record behind a sending is Alike to the record in front.** -/
theorem sending_alike {Cl : Type} {P : K1.Par} {link moment : Nat} {arrays : Option (List Nat)}
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {o : VerifiableInference.Desc.First.HeadOwn} (ho : s.here = .head o)
    (h : (commitAtS (Cl := Cl) P link moment arrays).decide s rs gs = .ok s') : Alike s s' := by
  obtain ⟨o', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := sending_at ho h
  exact ⟨o, o', ho, h1, h2, h3, h4, h5, h6, h7, h8, h9.slots.later, h9.cols⟩

end VerifiableInference.Desc.Kinds.Head.Law
