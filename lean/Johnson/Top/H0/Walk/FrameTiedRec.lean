-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameTiedRec.lean: the statements of FrameGives.lean, proved: laidAdds,
clearedGives, openedAttGives, openedLayGives, openedZeroGives; with openAtt_eq, openLay_eq,
openLayZero_eq: "opened" as an equation on the record.
Limits: FrameTied.lean's. No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameGives

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc (need)
open VerifiableInference.Desc.First (S ModelPart Stand standOf)
open VerifiableInference.Desc.First.Pend (pendingRowO)

theorem laidAdds : LaidAdds := fun m s t h => by
  obtain ⟨e, _, hW, hL⟩ := Law.layFront_ok h
  subst e
  exact ⟨rfl, hW, hL⟩

theorem clearedGives : ClearedGives := by
  intro X counts left lay lin s t h
  have c := Law.clear_carries h
  have m := Law.clear_messages h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h0, _⟩ := Law.clearWith_ok h
  refine ⟨c.2.2.2.2.2.2.2.2.2, c.2.2.2.2.2.2.1, c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1,
    c.2.2.2.2.2.1, c.2.2.2.2.2.2.2.1, c.2.2.2.2.2.2.2.2.1, m.1, m.2, Law.clearWith_leaves h, ?_, h0,
    fun hv => Law.cleared_lays h hv⟩
  cases hv : X.fv with
  | false => rw [(h0 hv).1]
  | true =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hi, _⟩ := Law.clear_row h hv
    exact hi

/-- «opened» at an attention link, as an equation. -/
theorem openAtt_eq {P : AttPar} {s t : S} (h : openAtt P s = .ok t) :
    ∃ a : AttStart, t =
      { s with out := a.out, here := .att { L := a.L, F := a.F, tl := a.tl, d := default,
                                            x := default } } := by
  unfold openAtt at h
  cases hB : s.atBetween with
  | false => simp [need, hB, bind, Except.bind] at h
  | true =>
   cases hA : firstRun s.check with
   | false => simp [need, hB, hA, bind, Except.bind] at h
   | true =>
    cases hq : attFirstQuiet P.X P.l P.ns P.tl₀ s.check s.out with
    | error e => simp [need, hB, hA, hq, bind, Except.bind] at h
    | ok a =>
      simp [need, hB, hA, hq, bind, Except.bind, pure, Except.pure] at h
      have hu := ((S.unmarked_ok _ _).mp h).1
      have hb' : ({ s with out := a.out } : S).atBetween = true := hB
      refine ⟨a, ?_⟩
      rw [← hu]
      simp [S.enterAtt, hb']

/-- «opened» at a layers' link, as an equation. -/
theorem openLay_eq {P : LayPar} {s t : S} (h : openLay P s = .ok t) :
    ∃ a : LayStart, t = { s with out := a.out, here := .lay { L := a.L, F := a.F, tl := P.tl₀ } } :=
        by
  unfold openLay at h
  cases hB : s.atBetween with
  | false => simp [need, hB, bind, Except.bind] at h
  | true =>
   cases hA : firstRun s.check with
   | false => simp [need, hB, hA, bind, Except.bind] at h
   | true =>
    cases hq : layFirstQuiet P.X P.l P.p4 P.g P.Tp P.Fp P.ns s.check s.out with
    | error e => simp [need, hB, hA, hq, bind, Except.bind] at h
    | ok a =>
      simp [need, hB, hA, hq, bind, Except.bind, pure, Except.pure] at h
      have hu := ((S.unmarked_ok _ _).mp h).1
      have hb' : ({ s with out := a.out } : S).atBetween = true := hB
      refine ⟨a, ?_⟩
      rw [← hu]
      simp [S.enterLay, hb']

/-- «opened» at link 0, as an equation. -/
theorem openLayZero_eq {P : LayPar} {fvs : List Bool} {kCol : Nat} {s t : S}
    (h : openLayZero P fvs kCol s = .ok t) :
    ∃ a : LayStart, t = { s with out := a.out, here := .lay { L := a.L, F := a.F, tl := P.tl₀ } } :=
        by
  unfold openLayZero at h
  cases hB : s.atBetween with
  | false => simp [need, hB, bind, Except.bind] at h
  | true =>
   cases hA : firstRun s.check with
   | false => simp [need, hB, hA, bind, Except.bind] at h
   | true =>
    cases hq : layFirstQuietZero P.X P.p4 P.g P.Tp P.Fp P.ns (roomOf fvs kCol) s.check s.out
        s.st.oracles with
    | error e => simp [need, hB, hA, hq, bind, Except.bind] at h
    | ok a =>
      simp [need, hB, hA, hq, bind, Except.bind, pure, Except.pure] at h
      have hu := ((S.unmarked_ok _ _).mp h).1
      have hb' : ({ s with out := a.out } : S).atBetween = true := hB
      refine ⟨a, ?_⟩
      rw [← hu]
      simp [S.enterLay, hb']

theorem openedAttGives : OpenedAttGives := by
  intro P s t h
  obtain ⟨_, _, _, _, h5, h6, h7, h8, h9, h10⟩ := Law.openAtt_ok h
  obtain ⟨a, e⟩ := openAtt_eq h
  refine ⟨by rw [e]; rfl, ⟨_, h5, rfl⟩, ⟨h7, Law.openAtt_carries h, h8, by rw [e], by rw [e],
    by rw [e], h9, by rw [e]⟩, h10, Law.ledger_sized_at_lay_att h, h6, Law.openAtt_tl h⟩

theorem openedLayGives : OpenedLayGives := by
  intro P s t h
  obtain ⟨_, _, _, _, _, h5, h6, h7, h8, h9, h10⟩ := Law.openLay_ok h
  obtain ⟨a, e⟩ := openLay_eq h
  refine ⟨by rw [e]; rfl, ⟨_, h5, rfl⟩, ⟨h7, Law.openLay_carries h, h8, by rw [e], by rw [e],
    by rw [e], h9, by rw [e]⟩, h10, Law.ledger_sized_at_lay_lay h, h6, Law.openLay_tl h⟩

theorem openedZeroGives : OpenedZeroGives := by
  intro P fvs kCol s t h
  obtain ⟨_, _, _, _, ⟨im, hi, ho⟩, h5, h6, h7, h8, h9⟩ := Law.openLayZero_ok h
  obtain ⟨a, e⟩ := openLayZero_eq h
  refine ⟨by rw [e]; rfl, ⟨_, h5, rfl⟩, ⟨h7, by simp [S.live, h5], h8, by rw [e], by rw [e],
    by rw [e], h9, by rw [e]⟩, ⟨im, Props.indexMasksAt_iff.1 hi, ho⟩,
    Law.ledger_sized_at_lay_zero h, h6, Law.openLayZero_tl h⟩

#print axioms laidAdds
#print axioms clearedGives
#print axioms openedAttGives
#print axioms openedLayGives
#print axioms openedZeroGives

end Johnson.Desc.First.Walk.Tied
