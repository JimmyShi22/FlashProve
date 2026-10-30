--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Part/MaskedSumLedgerSilly.lean: THE LEDGER's LEMMA AT SILLY MEMBERS, AND A WITNESS.
  OwnOf rw       : ledger_own (Johnson/Desc/Part/MaskedSumLedger.lean) with any row rw in the place of «row». ownOf_row: the text's meets it.
  silly_no_write : a row that hands back the text's form and WRITES NOTHING does NOT meet it: an unfilled slot is worth 0 in the
                   ledger's world, not the mask's entry.
  ledger_meets   : ledger_own's premises can be met together, with row's ledger the very one that the hearing hands back: at a
                   call with no variable but Y (degree 1, one end value), three toy rounds, a ledger of three slots.
HOW LITTLE THE WITNESS IS: one made-up call of the smallest shape that the text takes. At the real sizes the text's «hear» and «row»
have returned at every masked sumcheck of the first chain's plan in a run (no theorem).
Nothing on soundness, on an honest prover or on hiding.
-/
import Johnson.Desc.Part.MaskedSumLedger
import Johnson.Desc.Part.MaskedSumTieRefuses

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.Model
open Iop Prob Cb TWhole Johnson.L5.Layers Cb.Pv.Att OnBytes.Tie.Pv.Att

/-- ledger_own with any row in the place of «row». -/
def OwnOf (rw : Heard → E → Aff → Fork → Option (Aff × Fork)) : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (C : Aff) (lead : Nat) (vs : List Var)
    (e : Ends) (F G F' G' H : Fork) (rs : List Fmt.RoundView) (h : Heard) (S0 : E) (kept f : Aff),
    hear C ⟨lead, vs, some e⟩ F rs = some (h, G) → OnBytes.PscRun.Sized F' → rw h S0 kept F' = some (f, G') →
    OnBytes.PscRun.Later G' H → ∀ i, i < ownSlots (Call.all ⟨lead, vs, some e⟩) →
      (H.worldOf ρ mask entry).slot (h.first + i) = mask (F.next + i)

theorem ownOf_row : OwnOf row := by
  intro K _ ρ mask entry C lead vs e F G F' G' H rs h S0 kept f hh hF' hr hl
  exact ledger_own ρ mask entry hh hF' hr hl

/-- **A row that writes nothing does not meet it.** -/
theorem silly_no_write : ¬ OwnOf (fun h S0 kept F => some (rowAff h S0 kept, F)) := by
  intro H
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 toy_returns
  have hy' : hear {} ⟨0, [], some ⟨1, 1⟩⟩ (({} : Fork).slots 3) [toyRound 1, toyRound 1, toyRound 0] =
      some (y.1, y.2) := hy
  have e1 : y.1.first = 0 := (heard_len hy').1
  have h0 := H Cb.Gl.E Reading.gl (fun _ => 1) (fun _ _ _ => 0) {} 0 [] ⟨1, 1⟩ (({} : Fork).slots 3) y.2
    (({} : Fork).slots 3) (({} : Fork).slots 3) (({} : Fork).slots 3) [toyRound 1, toyRound 1, toyRound 0] y.1 zeroE {}
    (rowAff y.1 zeroE {}) hy' (OnBytes.PscRun.slots_sized _ _) rfl (OnBytes.PscRun.Later.refl _) 0 (by decide)
  rw [e1] at h0
  have h1 : Reading.gl.val zeroE - Reading.gl.val zeroE * 1 = (1 : Cb.Gl.E) := h0
  rw [Reading.gl.zero] at h1
  simp at h1

/-- **ledger_own's premises can be met together.** -/
theorem ledger_meets : ∃ (h : Heard) (G G' : Fork) (f : Aff),
    hear {} ⟨0, [], some ⟨1, 1⟩⟩ (({} : Fork).slots 3) [toyRound 1, toyRound 1, toyRound 0] = some (h, G) ∧
      OnBytes.PscRun.Sized G ∧ row h zeroE {} G = some (f, G') := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 toy_returns
  have hy' : hear {} ⟨0, [], some ⟨1, 1⟩⟩ (({} : Fork).slots 3) [toyRound 1, toyRound 1, toyRound 0] =
      some (y.1, y.2) := hy
  have hF : OnBytes.PscRun.Sized (({} : Fork).slots 3) := OnBytes.PscRun.slots_sized _ _
  have hl := hear_later hF hy'
  have hG : OnBytes.PscRun.Sized y.2 := hl.sized hF
  obtain ⟨e1, _, e3⟩ := heard_len hy'
  have e1' : y.1.first = 0 := e1
  have e3' : (hidingAt (y.1.vars.zip y.1.r)).1.length = 2 := e3
  have hns : y.2.ns = 3 := hl.ns
  obtain ⟨_, _, R, _, _, _, hw⟩ := hear_spec hy'
  have hF2 : OnBytes.PscRun.Sized ({ (({} : Fork).slots 3) with
      next := (({} : Fork).slots 3).next + ownSlots (Call.all ⟨0, [], some ⟨1, 1⟩⟩) + R.values.length } : Fork) := hF
  obtain ⟨_, _, _, b4⟩ := OnBytes.PscRun.hideRun_ok _ y.2 _ _ _ hF2 hw
  obtain ⟨G', hG'⟩ := hideRun_retA y.2 y.1.first (Array.replicate (hidingAt (y.1.vars.zip y.1.r)).1.length zeroE)
    (subE zeroE oneE) (by rw [hG.2.2])
    (by rw [e1', hns]; simp [e3'])
    (by
      intro j _ hj
      have hj2 : j < 2 := by simpa [e1', e3'] using hj
      have c := (b4 j (Or.inl hj2)).2.2
      have hsz : j < y.2.gotF.size := by rw [hG.2.2, hns]; omega
      have nf : ¬ OnBytes.PscRun.Filled y.2 j := by
        intro hf
        have hf0 : OnBytes.PscRun.Filled (({} : Fork).slots 3) j := c.1 hf
        have hj3 : j < 3 := by omega
        have : (Array.replicate 3 false).getD j false = true := hf0
        simp [Array.getD_eq_getD_getElem?, hj3] at this
      have eq : y.2.gotF.getD j true = y.2.gotF.getD j false := by
        simp [Array.getD_eq_getD_getElem?, hsz]
      rw [eq]
      cases hb : y.2.gotF.getD j false with
      | false => rfl
      | true => exact absurd hb nf)
  refine ⟨y.1, y.2, G', rowAff y.1 zeroE {}, hy', hG, ?_⟩
  unfold row
  simp only [hG', Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rfl

end VerifiableInference.Desc.Part.MaskedSum

#print axioms VerifiableInference.Desc.Part.MaskedSum.ownOf_row
#print axioms VerifiableInference.Desc.Part.MaskedSum.silly_no_write
#print axioms VerifiableInference.Desc.Part.MaskedSum.ledger_meets
