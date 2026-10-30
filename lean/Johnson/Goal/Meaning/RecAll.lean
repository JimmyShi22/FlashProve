-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RecAll.lean: the first chain's record holds the plan's codes, and EVERY COPY of
the frame of the links in it holds the plan's shape and groups: the property, and that the writers
of Johnson/Desc/First/State.lean hand it on.

The record S has up to three copies of the frame: the walk's (s.check.frame); inside a link the
link's own (L.check.frame), which S.leaveLink lays back over the walk's; in the head's front and in
the finish the frame fr, which moves alone there. So no reader of one copy is kept by every step.
  FramePub sh f: f.shape = sh, f.groups = reqGroups sh, and RowsPub sh f: the carried rows have a
    written form for each mask row, and behind the first closing they bear the shape's two codes'
    numbers and two mask rows.
  framesIn s: all copies that s holds.
  RecAll cs sh s: s.st.codes = cs; FramePub sh at every member of framesIn s; reqOk cs sh.
  RecAll.walk, RecAll.live, RecAll.turn: so of s.check.frame, s.live.frame and s.frame.
  same_frames: a record with the same codes and the same copies has the property too.
  The writers: mark, unmarked, putFork, putTl, putLook, hearLook, hear5, withReq, owe (the copies
    stay) · putLink, putLive, enterLay, enterAtt (a copy is handed in: FramePub is asked of it) ·
    enterHead, openHead, enterFin, enterMem, leaveLink (copies are laid over copies).
  recAll_first: the first record (Johnson/Desc/First/StartPlain.lean).
Not claimed: that any block hands the property on.
-/
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc.First

/-- What the last closing has returned has a written form for each of its mask rows; and, behind the
first closing, it bears the shape's two codes' numbers and two mask rows. -/
def RowsPub (sh : ReqShape) (f : ReqFrame) : Prop :=
  f.rows.d.size = f.rows.masks ∧
    (f.link = 0 ∨ (f.rows.code = sh.code ∧ f.rows.maskCode = sh.maskCode ∧ f.rows.masks = 2))

/-- The frame holds the plan's shape, the groups that follow from it, and, behind the first closing,
carried rows with the shape's codes. -/
structure FramePub (sh : ReqShape) (f : ReqFrame) : Prop where
  shape : f.shape = sh
  groups : f.groups = reqGroups sh
  rows : RowsPub sh f

/-- A frame with the same shape, groups, carried rows and link. -/
theorem FramePub.carry {sh : ReqShape} {f f' : ReqFrame} (h : FramePub sh f)
    (e1 : f'.shape = f.shape) (e2 : f'.groups = f.groups) (e3 : f'.rows = f.rows)
    (e4 : f'.link = f.link) : FramePub sh f' :=
  ⟨e1.trans h.shape, e2.trans h.groups, by unfold RowsPub; rw [e3, e4]; exact h.rows⟩

/-- All copies of the frame that the record holds. -/
def framesIn (s : S) : List ReqFrame :=
  s.check.frame ::
    match s.here with
    | .lay a => [a.L.check.frame]
    | .att a => [a.L.check.frame]
    | .head a => [a.fr, a.L.check.frame]
    | .fin a => [a.fr]
    | _ => []

/-- **The record's public part is the plan's, in every copy.** -/
structure RecAll (cs : Codes) (sh : ReqShape) (s : S) : Prop where
  codes : s.st.codes = cs
  frames : ∀ f ∈ framesIn s, FramePub sh f
  ok : reqOk cs sh = true

variable {cs : Codes} {sh : ReqShape} {s : S}

theorem RecAll.walk (R : RecAll cs sh s) : FramePub sh s.check.frame :=
  R.frames _ List.mem_cons_self

theorem RecAll.live (R : RecAll cs sh s) : FramePub sh s.live.frame := by
  unfold S.live S.link?
  have F := R.frames
  unfold framesIn at F
  split
  · rename_i L hL
    split at hL
    · cases hL
      rename_i a ha
      rw [ha] at F
      exact F _ (by simp)
    · cases hL
      rename_i a ha
      rw [ha] at F
      exact F _ (by simp)
    · rename_i a ha
      rw [ha] at F
      split at hL
      · cases hL
        exact F _ (by simp)
      · cases hL
    · cases hL
  · exact R.walk

theorem RecAll.turn (R : RecAll cs sh s) : FramePub sh s.frame := by
  unfold S.frame
  have F := R.frames
  unfold framesIn at F
  split
  · rename_i a ha
    rw [ha] at F
    split
    · exact F _ (by simp)
    · exact F _ (by simp)
  · rename_i a ha
    rw [ha] at F
    exact F _ (by simp)
  · exact R.live

/-- The same codes and the same copies. -/
theorem same_frames {s' : S} (R : RecAll cs sh s) (hc : s'.st.codes = s.st.codes)
    (hf : ∀ f ∈ framesIn s', f ∈ framesIn s) : RecAll cs sh s' :=
  ⟨hc.trans R.codes, fun f hm => R.frames f (hf f hm), R.ok⟩

/-- The same codes; each copy is an old one or has FramePub. -/
theorem more_frames {s' : S} (R : RecAll cs sh s) (hc : s'.st.codes = s.st.codes)
    (hf : ∀ f ∈ framesIn s', f ∈ framesIn s ∨ FramePub sh f) : RecAll cs sh s' :=
  ⟨hc.trans R.codes, fun f hm => (hf f hm).elim (R.frames f) id, R.ok⟩

/-! ## State.lean's writers -/

theorem recAll_mark (R : RecAll cs sh s) (name : String) : RecAll cs sh (s.mark name) := by
  refine same_frames R ?_ ?_ <;> unfold S.mark <;> split <;> simp [framesIn]

theorem recAll_unmarked {s' : S} (R : RecAll cs sh s) (h : s.unmarked = .ok s') :
    RecAll cs sh s' := by
  unfold S.unmarked at h
  split at h
  · cases h
    exact R
  · cases h

/-- A tactic for a writer that leaves the codes and every copy. -/
local macro "stays" R:term "," d:ident : tactic =>
  `(tactic| (refine same_frames $R ?_ ?_ <;> unfold $d <;> repeat' split) <;>
    simp_all [framesIn, S.mark] <;> (repeat' split) <;> simp_all)

theorem recAll_putFork (R : RecAll cs sh s) (F : Fork) : RecAll cs sh (s.putFork F) := by
  stays R, S.putFork

theorem recAll_putTl (R : RecAll cs sh s) (tl : HTailF2) : RecAll cs sh (s.putTl tl) := by
  stays R, S.putTl

theorem recAll_putLook (R : RecAll cs sh s) (g : Forest.Heard) : RecAll cs sh (s.putLook g) := by
  stays R, S.putLook

theorem recAll_hearLook (R : RecAll cs sh s) (g : Forest.Heard) :
    RecAll cs sh (s.hearLook g) := by
  stays R, S.hearLook

theorem recAll_hear5 (R : RecAll cs sh s) (h : Att.P.Heard) : RecAll cs sh (s.hear5 h) := by
  stays R, S.hear5

theorem recAll_withReq (R : RecAll cs sh s) (req : Array UInt32) :
    RecAll cs sh (s.withReq req) :=
  same_frames R rfl fun _ h => h

theorem recAll_owe (R : RecAll cs sh s) (rows : Nat) : RecAll cs sh (s.owe rows) := by
  stays R, S.owe

theorem recAll_enterMem (R : RecAll cs sh s) : RecAll cs sh s.enterMem := by
  stays R, S.enterMem

theorem recAll_enterHead (R : RecAll cs sh s) (tl : HTailF2) : RecAll cs sh (s.enterHead tl) := by
  stays R, S.enterHead

theorem recAll_enterFin (R : RecAll cs sh s) : RecAll cs sh s.enterFin := by
  stays R, S.enterFin

theorem recAll_openHead (R : RecAll cs sh s) : RecAll cs sh s.openHead := by
  stays R, S.openHead

/-- A copy is handed in. -/
theorem recAll_putLink (R : RecAll cs sh s) {L : LinkCtx} (hL : FramePub sh L.check.frame) :
    RecAll cs sh (s.putLink L) := by
  refine more_frames R ?_ ?_ <;> unfold S.putLink <;> repeat' split
  all_goals simp_all [framesIn]

theorem recAll_enterLay (R : RecAll cs sh s) {L : LinkCtx} (hL : FramePub sh L.check.frame)
    (F : Fork) (tl : HTailF2) : RecAll cs sh (s.enterLay L F tl) := by
  unfold S.enterLay
  split
  · refine more_frames R rfl ?_
    simp_all [framesIn]
  · exact recAll_mark R _

theorem recAll_enterAtt (R : RecAll cs sh s) {L : LinkCtx} (hL : FramePub sh L.check.frame)
    (F : Fork) (tl : HTailF2) : RecAll cs sh (s.enterAtt L F tl) := by
  unfold S.enterAtt
  split
  · refine more_frames R rfl ?_
    simp_all [framesIn]
  · exact recAll_mark R _

theorem recAll_putLive (R : RecAll cs sh s) {c : ChainCheck} (hc : FramePub sh c.frame) :
    RecAll cs sh (s.putLive c) := by
  unfold S.putLive
  split
  · exact recAll_putLink R hc
  · refine more_frames R rfl fun f hf => ?_
    unfold framesIn at hf ⊢
    rcases List.mem_cons.1 hf with rfl | hf
    · exact Or.inr hc
    · exact Or.inl (List.mem_cons_of_mem _ hf)

/-- The link's copy is laid back over the walk's. -/
theorem recAll_leaveLink (R : RecAll cs sh s) : RecAll cs sh s.leaveLink := by
  unfold S.leaveLink
  split
  · refine more_frames R rfl fun f hf => ?_
    have e : f = s.live.frame := by simpa [framesIn] using hf
    rw [e]
    exact Or.inr R.live
  · exact recAll_mark R _

/-- **The first record.** -/
theorem recAll_first {P : Par} {codes : Codes} {shape : ReqShape} {layout : Params.ReqLayout}
    {s : S} (h : S.startP P codes shape layout = some s) : RecAll codes shape s := by
  unfold S.startP at h
  split at h
  · rename_i hk
    cases h
    unfold S.startOk at hk
    simp only [Bool.and_eq_true] at hk
    refine ⟨rfl, fun f hf => ?_, hk.2.1.1⟩
    have e : f = (S.firstRecord codes shape layout).check.frame := by
      simpa [framesIn, S.firstRecord] using hf
    rw [e]
    exact ⟨rfl, rfl, rfl, Or.inl rfl⟩
  · cases h

#print axioms RecAll.turn
#print axioms recAll_putLive
#print axioms recAll_leaveLink
#print axioms recAll_openHead
#print axioms recAll_first

end Meaning.K2
