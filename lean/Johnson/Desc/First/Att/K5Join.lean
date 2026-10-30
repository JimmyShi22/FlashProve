-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K5Join.lean: kind K5's fourth named run, "join" (one line that calls the
lookup's
own function K3.joinRun on the kind's key forms: Att/SeatW.lean). Where it returns it turns, of the
ledger, one mark of the list of owed claims alone: it fills no slot, and what lies under a slot
stays,
with its factor.

Main names:
  `joinF_ledger`: the lookup's joinF, where it returns from a ledger F, leaves F.paid g.owedJoin.
  `paid_stays`: Stays F (F.paid i).
  `join_marks`: where K3.joinRun returns: the state behind is seat.mark of that ledger; one claim is
    made.

Limit: that seat.mark lays the ledger alone is the lookup's seat's matter; not shown here.
Sources: Look/K3Lookup.lean, Look/K3Runs.lean, Look/LookClaims.lean; Fork.paid.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3Runs
import Johnson.Desc.First.Att.K5Said

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc (named need)

theorem paid_stays (F : Fork) (i : Nat) : Stays F (F.paid i) := fun _ _ _ h => h

theorem joinF_ledger {g : Forest.Heard} {KF : Array Aff} {F : Fork} {t : Tape} {x : Aff × Fork × Tape}
    (h : First.Look.joinF g KF F t = some x) : x.2.1 = F.paid g.owedJoin := by
  unfold First.Look.joinF at h
  simp only [bind, Fl.andThen, Fl.must, First.Look.joinAddedF, First.Look.paidF, Fl.change, pure, Fl.ret,
    Option.map_some] at h
  split at h
  · rename_i a G u hm
    split at hm
    · simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨_, e1, _⟩ := hm
      subst e1
      simp only [Option.some.injEq] at h
      rw [← h]
    · cases hm
  · cases h

/-- **"join" turns the owed list's one mark alone.** -/
theorem join_marks {S Cl : Type} (seat : K3.Seat S Cl) (keys : S → Option (Array Aff)) (n : Nat) (s s' : S)
    (cls : List Cl) (h : K3.joinRun seat keys n s = .ok (cls, s')) :
    ∃ (F : Fork) (g : Forest.Heard), seat.fork s = some F ∧ seat.heard s = some g ∧
      s' = seat.mark s (F.paid g.owedJoin) ∧ Stays F (F.paid g.owedJoin) ∧ cls.length = 1 := by
  unfold K3.joinRun at h
  cases h1 : seat.fork s with
  | none => simp [h1, named, bind, Except.bind] at h
  | some F =>
    cases h2 : seat.heard s with
    | none => simp [h1, h2, named, bind, Except.bind] at h
    | some g =>
      cases h3 : K3.unpaid F g.owedJoin with
      | false => simp [h1, h2, h3, named, need, bind, Except.bind] at h
      | true =>
        cases h4 : keys s with
        | none => simp [h1, h2, h3, h4, named, need, bind, Except.bind] at h
        | some KF =>
          cases h5 : First.Look.joinF g KF F [] with
          | none => simp [h1, h2, h3, h4, h5, named, need, bind, Except.bind] at h
          | some x =>
            simp [h1, h2, h3, h4, h5, named, need, bind, Except.bind, pure, Except.pure] at h
            refine ⟨F, g, rfl, rfl, ?_, paid_stays _ _, by rw [← h.1]; rfl⟩
            rw [← h.2, joinF_ledger h5]

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.join_marks
