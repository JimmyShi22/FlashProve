-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RecRel.lean: RecAll (Johnson/Goal/Meaning/RecAll.lean) as a relation for the
chain's general rules (Johnson/Desc/FoldKeeps.lean), and the link's frame's steps' share: laid,
opened, cleared (Johnson/Desc/First/Walk/Frame.lean, FrameZero.lean).

  RecRel cs sh: fun s s' => RecAll cs sh s → RecAll cs sh s'; recRel_refl, recRel_trans.
  layFront_rec, openAtt_rec, openLay_rec, openLayZero_rec, clearWith_rec: each step is
    Keeps.Fn (RecRel cs sh). An opening lays the walk's state of the calls into the link's own copy
    (by the library's openAtt_ok | openLay_ok | openLayZero_ok, Johnson/Top/H0/Walk/FrameLaw.lean);
    the clearing lays the link's copy back over the walk's (S.leaveLink).
  layFront_link: behind "laid" at link l the walk's frame stands at link l (the library's
    layFront_ok).
Not claimed: anything on another kind's blocks, or on the head's and the finish's own fronts.
-/
import Johnson.Goal.Meaning.RecAll
import Johnson.Desc.FoldKeeps
import Johnson.Top.H0.Walk.FrameLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Fn)
open Johnson.Desc.First.Walk

/-- RecAll is handed on. -/
def RecRel (cs : Codes) (sh : ReqShape) : S → S → Prop :=
  fun s s' => RecAll cs sh s → RecAll cs sh s'

theorem recRel_refl (cs : Codes) (sh : ReqShape) (s : S) : RecRel cs sh s s := id

theorem recRel_trans (cs : Codes) (sh : ReqShape) (a b c : S) (h : RecRel cs sh a b)
    (k : RecRel cs sh b c) : RecRel cs sh a c := fun x => k (h x)

variable {cs : Codes} {sh : ReqShape}

theorem bindE {α β : Type} {x : Except String α} {f : α → Except String β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Another field "out" leaves the property. -/
theorem recAll_out {s : S} (R : RecAll cs sh s) (o : Proof.LinksResult) :
    RecAll cs sh { s with out := o } :=
  same_frames R rfl fun _ h => h

theorem layFront_rec (l : Nat) : Fn (RecRel cs sh) (layFront l) := fun s t h R => by
  rw [(Law.layFront_ok h).1]
  exact R

theorem layFront_link {l : Nat} {s t : S} (h : layFront l s = .ok t) : t.check.frame.link = l := by
  obtain ⟨e, -, -, k⟩ := Law.layFront_ok h
  rw [e]
  exact k

theorem openAtt_rec (P : AttPar) : Fn (RecRel cs sh) (openAtt P) := fun s t h R => by
  obtain ⟨hB, -, -, -, hl, -⟩ := Law.openAtt_ok h
  unfold openAtt at h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨a, -, h⟩ := bindE h
  have e := ((S.unmarked_ok _ _).1 h).1
  have hB' : ({ s with out := a.out } : S).atBetween = true := hB
  have k := (Law.enterAtt_ok (L := a.L) (F := a.F) (tl := a.tl) hB').1
  rw [e, hl] at k
  have eL : a.L.check = s.check := by rw [← Option.some.inj k]
  exact recAll_unmarked (recAll_enterAtt (recAll_out R a.out) (by rw [eL]; exact R.walk) _ _) h

theorem openLay_rec (P : LayPar) : Fn (RecRel cs sh) (openLay P) := fun s t h R => by
  obtain ⟨hB, -, -, -, -, hl, -⟩ := Law.openLay_ok h
  unfold openLay at h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨a, -, h⟩ := bindE h
  have e := ((S.unmarked_ok _ _).1 h).1
  have hB' : ({ s with out := a.out } : S).atBetween = true := hB
  have k := (Law.enterLay_ok (L := a.L) (F := a.F) (tl := P.tl₀) hB').1
  rw [e, hl] at k
  have eL : a.L.check = s.check := by rw [← Option.some.inj k]
  exact recAll_unmarked (recAll_enterLay (recAll_out R a.out) (by rw [eL]; exact R.walk) _ _) h

theorem openLayZero_rec (P : LayPar) (fvs : List Bool) (kCol : Nat) :
    Fn (RecRel cs sh) (openLayZero P fvs kCol) := fun s t h R => by
  obtain ⟨hB, -, -, -, -, hl, -⟩ := Law.openLayZero_ok h
  unfold openLayZero at h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨a, -, h⟩ := bindE h
  have e := ((S.unmarked_ok _ _).1 h).1
  have hB' : ({ s with out := a.out } : S).atBetween = true := hB
  have k := (Law.enterLay_ok (L := a.L) (F := a.F) (tl := P.tl₀) hB').1
  rw [e, hl] at k
  have eL : a.L.check = s.check := by rw [← Option.some.inj k]
  exact recAll_unmarked (recAll_enterLay (recAll_out R a.out) (by rw [eL]; exact R.walk) _ _) h

theorem clearWith_rec (X : LinkPub) (counts : S → Except String Unit)
    (left : S → Option WsForkOut) (row : RowFn) : Fn (RecRel cs sh) (clearWith X counts left row) :=
  fun s t h R => by
  unfold clearWith at h
  split at h
  · obtain ⟨-, -, h⟩ := bindE h
    obtain ⟨p, -, h⟩ := bindE h
    split at h
    · exact recAll_unmarked (recAll_leaveLink R) h
    · split at h
      · cases h
      · rename_i r os _
        have R' : RecAll cs sh
            ({ s with out := pendingKept s.out r, st := { s.st with oracles := os } } : S) :=
          same_frames R rfl fun _ hm => hm
        exact recAll_unmarked (recAll_leaveLink R') h
  · cases h

#print axioms openAtt_rec
#print axioms openLay_rec
#print axioms openLayZero_rec
#print axioms clearWith_rec

end Meaning.K2
