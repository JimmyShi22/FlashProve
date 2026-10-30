-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/Fit/TidyRow.lean: THE ONE WRITE OF A PENDING ROW IS THE
TAKING OF A MASK ENTRY: so every GroundQuiet R keeps it. NEW, typed by hand.
  nextEntry_eq   the two texts of "the next real mask row" are one function
  row_of_quiet   pendingRowO … T.oracles = ok (r, os') ⊢ R T { T with oracles := os' }: by
  pendingRowO_iff and GroundQuiet.takeMask
  stQuiet_tidy   StQuiet TidyStay
What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.AtSeats.Fit.SeatFits
import Johnson.Desc.AtSeats.Fit.QuietSeated
import Johnson.Desc.Tidy.Chains
import Johnson.Desc.First.Pend.RowMeans
import Johnson.Desc.K12.Law.CallsWalkG
import Johnson.IMR.SeatOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.First.Pend (pendingRowO pendingRowO_iff takeEntry nextEntry)
open VerifiableInference.Desc.Ground (GroundQuiet TidyStay groundQuiet_tidy tidyStay_begun takeMaskP
  takeMaskL)

theorem nextEntry_eq (rows logRows : Nat) : ∀ fuel n,
    nextEntry rows logRows fuel n = Blk.nextRealRow rows logRows fuel n
  | 0, _ => rfl
  | fuel + 1, n => by
    unfold nextEntry Blk.nextRealRow
    split
    · rfl
    · exact nextEntry_eq rows logRows fuel (n + 1)

/-- **The one write of a pending row is the taking of a mask entry.** -/
theorem row_of_quiet {R : Statement → Statement → Prop} (H : GroundQuiet R) (lay : WsLay) (im : ℕ)
    (o : WsForkOut) (n : ℕ) (lin : LinShape) (T : Statement) (r : TensorRow)
    (os' : Array OnBytes.Oracle) (h : pendingRowO lay im o n lin T.oracles = .ok (r, os')) :
    R T { T with oracles := os' } := by
  obtain ⟨-, -, -, -, first, last, -, -, -, -, -, Gamma, -, g, -, l, hl, c, l', ht, -, hos⟩ :=
    (pendingRowO_iff lay im o n lin T.oracles os' r).1 h
  let d : _root_.Desc.Plain.DState Unit :=
    { st := T, book := { trees := #[], place := #[] }, roots := 0, opened := [], loc := () }
  unfold takeEntry at ht
  split at ht
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    obtain ⟨x, hx, hxl⟩ := Option.bind_eq_some_iff.1 hl
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    have hk : takeMaskP d im = some (nextEntry l.rows l.logRows (2 ^ l.logRows) l.next,
        { d with st := { T with oracles := os' } }) := by
      unfold takeMaskP
      have hok : Ground.ok (takeMaskL d.st im) = true := by
        simp [Ground.ok, takeMaskL, Ground.has, d, hx, hxl, hc.1, hc.2]
      rw [if_pos hok]
      show ((T.oracles[im]?).bind (·.ledger)).map _ = _
      rw [hl]
      simp only [Option.map_some, nextEntry_eq, hos, d]
    exact H.takeMask d _ im _ hk
  · cases ht

theorem stQuiet_tidy : StQuiet TidyStay where
  quiet := groundQuiet_tidy
  begun := tidyStay_begun
  row := row_of_quiet groundQuiet_tidy

end VerifiableInference.Desc.K13.Law
