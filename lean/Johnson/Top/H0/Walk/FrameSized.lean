-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameSized.lean: the ledger of slots that the link's frame lays at a link's
opening is Sized: its three arrays on slots have the length that the plan's number of slots says,
and no slot is filled.

  startFork_sized       of the start fork itself (Johnson/Desc/First/Walk/FirstQuiet.lean)
  ledger_sized_at_lay   (the closed statement LedgerSizedAtLay; _att, _lay, _zero: its parts)
                        behind "opened", at an attention link, a layers' link and link 0: the fork
                        that is open in the record is Sized, has the plan's number of slots, and
                        none of its slots is filled
  openLay_tl, openLayZero_tl, openAtt_tl   behind "opened" the carried record of the smallness test
                        (S.tl?) is the letter tl₀: at a layers' link to the letter; at an attention
                        link but for two marks of the order of steps

Spent of the library: the definition OnBytes.Model.Road.Sized
(OnBytes/Tie/Pv/Psc/Run/PscHide.lean): a statement on the plain record Fork alone. Its lemma
sized_slots is not spent: startFork is written anew after Fork.slots and does not call it.

Limits. A post-condition of "opened": from a yes. That the blocks behind keep the fork Sized along
the link is their laws' to say. P.ns and P.tl₀ are letters: that they are the plan's is for
whoever fills them in to show.
No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameLaw
import OnBytes.Tie.Pv.Psc.Run.PscHide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc (need)

theorem startFork_sized (X : LinkPub) (ns : Nat) :
    Road.Sized (startFork X ns) ∧ (startFork X ns).ns = ns ∧
      ∀ j, (startFork X ns).gotF.getD j false = false := by
  refine ⟨⟨by simp [startFork, emptySlots], by simp [startFork, emptySlots],
    by simp [startFork, emptySlots]⟩, by simp [startFork, emptySlots], fun j => ?_⟩
  simp [startFork, emptySlots, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

/-- What "opened" leaves open in the record, as a ledger of slots. -/
def SizedAt (ns : Nat) (t : S) : Prop :=
  ∃ F, t.fork? = some F ∧ Road.Sized F ∧ F.ns = ns ∧ ∀ j, F.gotF.getD j false = false

theorem ledger_sized_at_lay_att {P : AttPar} {s t : S} (h : openAtt P s = .ok t) : SizedAt P.ns t :=
  ⟨_, (openAtt_ok h).2.2.2.2.2.1, startFork_sized P.X P.ns⟩

theorem ledger_sized_at_lay_lay {P : LayPar} {s t : S} (h : openLay P s = .ok t) : SizedAt P.ns t :=
  ⟨_, (openLay_ok h).2.2.2.2.2.2.1, startFork_sized P.X P.ns⟩

theorem ledger_sized_at_lay_zero {P : LayPar} {fvs : List Bool} {kCol : Nat} {s t : S}
    (h : openLayZero P fvs kCol s = .ok t) : SizedAt P.ns t :=
  ⟨_, (openLayZero_ok h).2.2.2.2.2.2.1, startFork_sized P.X P.ns⟩

/-- **ledger_sized_at_lay**, as one closed statement: at all three sorts of link. -/
def LedgerSizedAtLay : Prop :=
  (∀ (P : AttPar) (s t : S), openAtt P s = .ok t → SizedAt P.ns t) ∧
  (∀ (P : LayPar) (s t : S), openLay P s = .ok t → SizedAt P.ns t) ∧
  (∀ (P : LayPar) (fvs : List Bool) (kCol : Nat) (s t : S),
    openLayZero P fvs kCol s = .ok t → SizedAt P.ns t)

theorem ledger_sized_at_lay : LedgerSizedAtLay :=
  ⟨fun _ _ _ h => ledger_sized_at_lay_att h, fun _ _ _ h => ledger_sized_at_lay_lay h,
    fun _ _ _ _ _ h => ledger_sized_at_lay_zero h⟩

/-! ### the smallness test's record that "opened" lays is the plan's -/

theorem enterLay_tl {s : S} {L : LinkCtx} {F : Fork} {tl : HTailF2} (hB : s.atBetween = true) :
    (S.enterLay s L F tl).tl? = some tl := by
  simp [S.enterLay, hB, S.tl?]

theorem enterAtt_tl {s : S} {L : LinkCtx} {F : Fork} {tl : HTailF2} (hB : s.atBetween = true) :
    (S.enterAtt s L F tl).tl? = some tl := by
  simp [S.enterAtt, hB, S.tl?]

/-- Behind "opened" at a layers' link the carried record of the smallness test is the plan's, to
the letter. -/
theorem openLay_tl {P : LayPar} {s t : S} (h : openLay P s = .ok t) : t.tl? = some P.tl₀ := by
  have hB := (openLay_ok h).1
  have hA := (openLay_ok h).2.1
  unfold openLay at h
  cases hq : layFirstQuiet P.X P.l P.p4 P.g P.Tp P.Fp P.ns s.check s.out with
  | error e => simp [need, hB, hA, hq, bind, Except.bind] at h
  | ok a =>
    simp [need, hB, hA, hq, bind, Except.bind, pure, Except.pure] at h
    have h := ((S.unmarked_ok _ _).mp h).1
    have hb' : ({ s with out := a.out } : S).atBetween = true := hB
    rw [← h]
    exact enterLay_tl hb'

/-- The like at link 0. -/
theorem openLayZero_tl {P : LayPar} {fvs : List Bool} {kCol : Nat} {s t : S}
    (h : openLayZero P fvs kCol s = .ok t) : t.tl? = some P.tl₀ := by
  have hB := (openLayZero_ok h).1
  have hA := (openLayZero_ok h).2.1
  unfold openLayZero at h
  cases hq : layFirstQuietZero P.X P.p4 P.g P.Tp P.Fp P.ns (roomOf fvs kCol) s.check s.out
      s.st.oracles with
  | error e => simp [need, hB, hA, hq, bind, Except.bind] at h
  | ok a =>
    simp [need, hB, hA, hq, bind, Except.bind, pure, Except.pure] at h
    have h := ((S.unmarked_ok _ _).mp h).1
    have hb' : ({ s with out := a.out } : S).atBetween = true := hB
    rw [← h]
    exact enterLay_tl hb'

/-- Behind "opened" at an attention link it is the plan's with two marks of the order of steps laid
back (the list of tables open; no fold drawn): every other field is the plan's. -/
theorem openAtt_tl {P : AttPar} {s t : S} (h : openAtt P s = .ok t) :
    t.tl? = some { P.tl₀ with funClosed := false, foldDrawn := 0 } := by
  have hB := (openAtt_ok h).1
  have hA := (openAtt_ok h).2.1
  unfold openAtt at h
  cases hq : attFirstQuiet P.X P.l P.ns P.tl₀ s.check s.out with
  | error e => simp [need, hB, hA, hq, bind, Except.bind] at h
  | ok a =>
    simp [need, hB, hA, hq, bind, Except.bind, pure, Except.pure] at h
    have h := ((S.unmarked_ok _ _).mp h).1
    have hb' : ({ s with out := a.out } : S).atBetween = true := hB
    rw [← h, enterAtt_tl hb']
    unfold attFirstQuiet at hq
    split at hq
    · simp at hq
    · cases hf : front P.X P.l s.check s.out with
      | error e => simp [hf] at hq
      | ok p =>
        simp [hf] at hq
        rw [← hq]

#print axioms openLay_tl
#print axioms openLayZero_tl
#print axioms openAtt_tl
#print axioms startFork_sized
#print axioms ledger_sized_at_lay_att
#print axioms ledger_sized_at_lay_lay
#print axioms ledger_sized_at_lay_zero
#print axioms ledger_sized_at_lay

end Johnson.Desc.First.Walk.Law
