-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/SitsMark.lean (over SitsDoor.lean): THE ROW «K02_sits»: AT A MARKED RECORD
THE SEATED SWITCH HAS NO YES; and behind a yes there is no mark. NO BLOCK IMPORTS THIS FILE. Why.
The tie to the table of joints asks of each piece «a mark stays» (TiedBy's seventh clause). A
seated block's guard refuses a mark behind it; the switch and the quiet steps around it leave the
mark as it is: so at a marked record nothing says yes, and the clause holds idly
(K2C/TiedForm.lean's premise hM).
  NoMarkDoor enter leave   the door's share: the way in leaves the mark; a yes of the way out at
                           t' says that t' bears none, and hands on a record that bears none
  door_guards · door_head · door_finish · door_opened · door_head_opened   at the five doors of
                                                                           SitsAt | SitsJoined
  k2_step_mark    a yes of the kind's own step leaves the mark
  sits_unmarked   Sits b (K2.codeSwitchKind p) enter leave and NoMarkDoor: a yes of b's step at s: s bears no
                  mark, nor does the record behind
  keepsAt_unmarked · keepsJoined_unmarked   so at every arm of KeepsAt | KeepsJoined
LIMITS. At the step, not yet at a piece's «out». Those of SitsStep.lean. No soundness is
claimed.
-/
import Johnson.P1K2R.SitsDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open VerifiableInference.Desc (Block Place OpenedColumn seatSame)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 codeSwitchKind headOpenQ finishFrontQ finishBehindQ)
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (k2P)

/-- The door's share of «no yes at a marked record». -/
structure NoMarkDoor (enter : S → Except String S) (leave : S → S → Except String S) : Prop where
  into : ∀ s t, enter s = .ok t → t.failed = s.failed
  out : ∀ s t' s', leave s t' = .ok s' → t'.failed = none ∧ s'.failed = none

theorem noMark_none {t u : S} (h : noMark t = .ok u) : t.failed = none := by
  unfold noMark at h
  split at h
  · assumption
  · cases h

theorem guards_none {s t u : S} (h : guards s t = .ok u) : t.failed = none ∧ u.failed = none := by
  have e := guards_same h
  unfold guards at h
  obtain ⟨m, h1, _⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  have k := noMark_none h1
  exact ⟨k, by rw [e]; exact k⟩

theorem door_guards : NoMarkDoor (fun s => .ok s) fun s t => guards s t :=
  ⟨fun _ _ e => by cases e; rfl, fun _ _ _ e => guards_none e⟩

theorem door_head (HP : VerifiableInference.Desc.First.K2.HeadPar) :
    NoMarkDoor (fun s => .ok s) fun s t => (headOpenQ HP t).bind (guards s) :=
  ⟨fun _ _ e => by cases e; rfl, fun s t' s' e => by
    obtain ⟨m, h1, h2⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 e
    obtain ⟨k1, k2⟩ := guards_none h2
    exact ⟨((VerifiableInference.Desc.First.K2.headOpenOpens HP t' m h1).2.2).symm.trans k1, k2⟩⟩

theorem door_finish : NoMarkDoor finishFrontQ fun s t => (finishBehindQ t).bind (guards s) :=
  ⟨fun s t e => VerifiableInference.Desc.First.K2.finishFrontMarks s t e, fun s t' s' e => by
    obtain ⟨m, h1, h2⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 e
    obtain ⟨k1, k2⟩ := guards_none h2
    exact ⟨(VerifiableInference.Desc.First.K2.finishBehindMarks t' m h1).symm.trans k1, k2⟩⟩

theorem leaveOpened_none {f : LinkFrame} {s t s' : S} (h : leaveOpened f s t = .ok s') :
    t.failed = none ∧ s'.failed = none := by
  unfold leaveOpened at h
  obtain ⟨m, h1, h⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  obtain ⟨u, _, h⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  obtain ⟨u₁, h3, h⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  obtain ⟨u₂, h4, h5⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  refine ⟨noMark_none h1, ?_⟩
  rw [seatSame_same h5, seatSame_same h4, noMark_same h3]
  exact noMark_none h3

theorem door_opened (f : LinkFrame) : NoMarkDoor (fun s => .ok s) fun s t => leaveOpened f s t :=
  ⟨fun _ _ e => by cases e; rfl, fun _ _ _ e => leaveOpened_none e⟩

theorem door_head_opened (f : LinkFrame) (HP : VerifiableInference.Desc.First.K2.HeadPar) :
    NoMarkDoor (fun s => .ok s) fun s t => (headOpenQ HP t).bind (leaveOpened f s) :=
  ⟨fun _ _ e => by cases e; rfl, fun s t' s' e => by
    obtain ⟨m, h1, h2⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 e
    obtain ⟨k1, k2⟩ := leaveOpened_none h2
    exact ⟨((VerifiableInference.Desc.First.K2.headOpenOpens HP t' m h1).2.2).symm.trans k1, k2⟩⟩

/-- A yes of the kind's own step leaves the mark. -/
theorem k2_step_mark {p : P2} {ft : Nat} {t t' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {k : Nat}
    (h : (codeSwitchKind p : Block S Unit).step ft t rs cols = .ok (t', k)) : t'.failed = t.failed :=
  (VerifiableInference.Desc.First.K2.keeps _ _ _ _ _ _
    ((VerifiableInference.Desc.Sound.step_ok_iff ft _ t t' rs cols k).1 h).2.2.2).1

/-- **At a marked record the seated switch has no yes.** -/
theorem sits_unmarked {b : Block S Cl} {p : P2} {enter : S → Except String S}
    {leave : S → S → Except String S} (hs : Sits b (codeSwitchKind p : Block S Unit) enter leave)
    (hd : NoMarkDoor enter leave) {ft : Nat} {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {k : Nat} (h : b.step ft s rs cols = .ok (s', k)) : s.failed = none ∧ s'.failed = none := by
  obtain ⟨t, t', e1, e2, e3⟩ := hs.step ft s s' rs cols k h
  obtain ⟨k1, k2⟩ := hd.out s t' s' e3
  exact ⟨((hd.into s t e1).symm.trans ((k2_step_mark e2).symm.trans k1)), k2⟩

theorem keepsAt_unmarked {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {nm : String} {b : Block S Cl}
    (h : KeepsAt Z G a nm b) {ft : Nat} {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {k : Nat}
    (hy : b.step ft s rs cols = .ok (s', k)) : s.failed = none ∧ s'.failed = none := by
  obtain ⟨P, n, _, _, h⟩ := h
  rcases h with ⟨_, hX⟩ | ⟨l, HP, _, _, hX⟩ | ⟨l, _, hX⟩
  · exact sits_unmarked hX.1 door_finish hy
  · exact sits_unmarked hX.1 (door_head HP) hy
  · exact sits_unmarked hX.1 door_guards hy

theorem keepsJoined_unmarked {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {nm : String}
    {b : Block S Cl} {f : LinkFrame} (h : KeepsJoined Z G a nm b f) {ft : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {k : Nat} (hy : b.step ft s rs cols = .ok (s', k)) :
    s.failed = none ∧ s'.failed = none := by
  obtain ⟨P, n, _, _, h⟩ := h
  rcases h with ⟨l, HP, _, _, hX⟩ | ⟨l, _, hX⟩
  · exact sits_unmarked hX.1 (door_head_opened f HP) hy
  · exact sits_unmarked hX.1 (door_opened f) hy

end P1K2

#print axioms P1K2.sits_unmarked
#print axioms P1K2.keepsAt_unmarked
#print axioms P1K2.keepsJoined_unmarked
