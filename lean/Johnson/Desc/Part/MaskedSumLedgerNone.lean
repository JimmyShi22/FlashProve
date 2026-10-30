--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Part/MaskedSumLedgerNone.lean: the ledger's lemma says something at a call WITHOUT
ends.

ledger_own (Johnson/Desc/Part/MaskedSumLedger.lean) is stated at every call, with ends or without.
This file shows that at a call without ends it is not empty: at the smallest shape that the text
takes there (one variable, summed plainly, two coefficients; no lead), two toy rounds and a ledger
of two slots: the hearing returns; the row returns at the very ledger that the hearing hands back;
the hiding polynomial has just as many coefficients as the call has slots of its own; that number is
2; and so, for every mask row, both slots are worth the mask's entries.
  readAll_none_values : a call without ends reads no end value.
  toyNone_returns     : the hearing returns there.
  ledger_meets_none   : the premises of ledger_own, met together; the range of its conclusion.
  ledger_says_none    : its conclusion there.
How little the witness is: one made-up call. Nothing on soundness, on an honest prover or on hiding.
-/
import Johnson.Desc.Part.MaskedSumLedgerSilly

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.Model

/-- A call without ends reads no end value. -/
theorem readAll_none_values {lead : Nat} {vs : List Var} {rs : List Fmt.RoundView} {R : Read}
    (h : readAll ⟨lead, vs, none⟩ rs = some R) : R.values = [] := by
  unfold readAll at h
  cases rs with
  | nil => cases h
  | cons r rest =>
    simp only at h
    split at h
    · have e := Option.some.inj h
      subst e
      rfl
    · rename_i h3
      cases h3
    · cases h

/-- The hearing returns at the smallest call without ends. -/
theorem toyNone_returns : (hear {} ⟨0, [.plain 2], none⟩ (({} : Fork).slots 2)
    [toyRound 1, toyRound 1]).isSome := by
  have hR0 : (readAll ⟨0, [.plain 2], none⟩ [toyRound 1, toyRound 1]).isSome := rfl
  obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 hR0
  have hv : R.values = [] := readAll_none_values hR
  have hT0 : ((({} : Fork).slots 2).publicPart {}).isSome := rfl
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 hT0
  have hs : shapeOk ⟨0, [.plain 2], none⟩ = true := rfl
  obtain ⟨G, hG⟩ := hideRun_retA
    ({ (({} : Fork).slots 2) with
      next := (({} : Fork).slots 2).next + ownSlots (Call.all ⟨0, [.plain 2], none⟩) +
        R.values.length } : Fork)
    ((({} : Fork).slots 2).next + ownSlots (Call.all ⟨0, [.plain 2], none⟩)) R.values.toArray
    ((R.rounds.map (·.2)).getLastD zeroE) (by simp [Fork.slots])
    (by
      rw [hv]
      decide)
    (by
      intro j a b
      rw [hv] at b
      have b' : j < (({} : Fork).slots 2).next + ownSlots (Call.all ⟨0, [.plain 2], none⟩) + 0 :=
        b
      omega)
  unfold hear
  simp only [hs, hT, hR, guard, if_true, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rw [hG]
  try rfl

/-- **ledger_own's premises can be met together at a call without ends**, and the range of its
conclusion is not empty. -/
theorem ledger_meets_none : ∃ (h : Heard) (G G' : Fork) (f : Aff),
    hear {} ⟨0, [.plain 2], none⟩ (({} : Fork).slots 2) [toyRound 1, toyRound 1] = some (h, G) ∧
      OnBytes.PscRun.Sized G ∧ row h zeroE {} G = some (f, G') ∧
      (hidingAt (h.vars.zip h.r)).1.length = ownSlots (Call.all ⟨0, [.plain 2], none⟩) ∧
      ownSlots (Call.all ⟨0, [.plain 2], none⟩) = 2 := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 toyNone_returns
  have hy' : hear {} ⟨0, [.plain 2], none⟩ (({} : Fork).slots 2) [toyRound 1, toyRound 1] =
      some (y.1, y.2) := hy
  have hF : OnBytes.PscRun.Sized (({} : Fork).slots 2) := OnBytes.PscRun.slots_sized _ _
  have hl := hear_later hF hy'
  have hG : OnBytes.PscRun.Sized y.2 := hl.sized hF
  obtain ⟨e1, _, e3⟩ := heard_lenK hy'
  have e1' : y.1.first = 0 := e1
  have e3' : (hidingAt (y.1.vars.zip y.1.r)).1.length = 2 := e3
  have hns : y.2.ns = 2 := hl.ns
  obtain ⟨_, _, R, _, _, _, hw⟩ := hear_spec hy'
  have hF2 : OnBytes.PscRun.Sized ({ (({} : Fork).slots 2) with
      next := (({} : Fork).slots 2).next + ownSlots (Call.all ⟨0, [.plain 2], none⟩) +
        R.values.length } : Fork) := hF
  obtain ⟨_, _, _, b4⟩ := OnBytes.PscRun.hideRun_ok _ y.2 _ _ _ hF2 hw
  obtain ⟨G', hG'⟩ := hideRun_retA y.2 y.1.first
    (Array.replicate (hidingAt (y.1.vars.zip y.1.r)).1.length zeroE)
    (subE zeroE oneE) (by rw [hG.2.2])
    (by rw [e1', hns]; simp [e3'])
    (by
      intro j _ hj
      have hj2 : j < 2 := by simpa [e1', e3'] using hj
      have c := (b4 j (Or.inl hj2)).2.2
      have hsz : j < y.2.gotF.size := by rw [hG.2.2, hns]; exact hj2
      have nf : ¬ OnBytes.PscRun.Filled y.2 j := by
        intro hf
        have hf0 : OnBytes.PscRun.Filled (({} : Fork).slots 2) j := c.1 hf
        have : (Array.replicate 2 false).getD j false = true := hf0
        simp [Array.getD_eq_getD_getElem?, hj2] at this
      have eq : y.2.gotF.getD j true = y.2.gotF.getD j false := by
        simp [Array.getD_eq_getD_getElem?, hsz]
      rw [eq]
      cases hb : y.2.gotF.getD j false with
      | false => rfl
      | true => exact absurd hb nf)
  refine ⟨y.1, y.2, G', rowAff y.1 zeroE {}, hy', hG, ?_, e3, rfl⟩
  unfold row
  simp only [hG', Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rfl

/-- **What ledger_own says there**: for every reading, mask row and entries: behind the row's write
both of the call's own slots are worth the mask's entries. -/
theorem ledger_says_none : ∃ (h : Heard) (G' : Fork), ∀ (K : Type) [Field K] (ρ : Reading K)
    (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K),
    (G'.worldOf ρ mask entry).slot (h.first + 0) = mask 0 ∧
      (G'.worldOf ρ mask entry).slot (h.first + 1) = mask 1 := by
  obtain ⟨h, G, G', f, hh, hG, hr, _, e2⟩ := ledger_meets_none
  refine ⟨h, G', fun K _ ρ mask entry => ?_⟩
  have key := ledger_own ρ mask entry hh hG hr (OnBytes.PscRun.Later.refl G')
  have k0 := key 0 (by rw [e2]; decide)
  have k1 := key 1 (by rw [e2]; decide)
  exact ⟨k0, k1⟩

end VerifiableInference.Desc.Part.MaskedSum

#print axioms VerifiableInference.Desc.Part.MaskedSum.ledger_meets_none
#print axioms VerifiableInference.Desc.Part.MaskedSum.ledger_says_none
