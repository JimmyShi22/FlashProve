-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/WeightsLow.lean: THE ROW WEIGHTS OF THE PROOF FILE's PENDING ROWS LIE BELOW THE MATRIX's ROWS:
AtPublicFiles.AtFiles.Low at what weightsOnRows and pendingRowO return: the like of weightsFrom_low, at stretchBlocks.

  stretchBlocks_low   each vector of a stretch lies below every length from the stretch's end on
  weightsOnRows_low   so at what weightsOnRows returns, where the shape's rows fit its cube
  pendingRowO_low     so at the row that pendingRowO returns, at its own shape

Limits. Implications from a return. Nothing on soundness, completeness or hiding.
-/
import E2E.KeyWeightsMark
import Johnson.Desc.First.Pend.RowOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Params OnBytes.Model
open AtPublicFiles.AtFiles (Low low_single low_block)
open OnBytes.Road.Rows (blockBits_spec)
open VerifiableInference.Desc.Own (weightsOnRows)

/-- **The blocks of a stretch lie below every length from its end on.** -/
theorem stretchBlocks_low (kRow firstRow : Nat) (values : Array E) (len : Nat) (h63 : kRow ≤ 63)
    (hs : firstRow + values.size ≤ len) (hl : len ≤ 2 ^ kRow) : ∀ (fuel start : Nat), firstRow ≤ start →
    ∀ t ∈ stretchBlocks kRow firstRow values fuel start, Low kRow len t
  | 0, _, _, t, ht => by
    unfold stretchBlocks at ht
    cases ht
  | fuel + 1, start, hf, t, ht => by
    unfold stretchBlocks at ht
    dsimp only at ht
    split at ht
    · cases ht
    · rename_i hlt
      have hlt' : start + 2 ^ 0 ≤ firstRow + values.size := by
        have : ¬ firstRow + values.size ≤ start := hlt
        simp only [Nat.pow_zero]
        omega
      have hb := blockBits_spec kRow start (firstRow + values.size) kRow 0 (Nat.zero_le _)
        (by simp) hlt'
      obtain ⟨hle, hal, hfit⟩ := hb
      rcases List.mem_cons.1 ht with e | ht'
      · subst e
        split
        · exact low_single _ kRow start len h63 (by
            have := Nat.two_pow_pos (blockBits kRow start (firstRow + values.size) kRow 0)
            omega) hl
        · refine low_block oneE kRow _ _ len values _ h63 hle (by
            have := Nat.two_pow_pos (blockBits kRow start (firstRow + values.size) kRow 0)
            omega) ?_ hl
          rw [Nat.mul_div_cancel' hal]
          have := Nat.two_pow_pos (blockBits kRow start (firstRow + values.size) kRow 0)
          omega
      · exact stretchBlocks_low kRow firstRow values len h63 hs hl fuel _ (by omega) t ht'

/-- **At what weightsOnRows returns.** -/
theorem weightsOnRows_low {S : LinShape} {first : Nat} {values : Array E} {g : List Tensor}
    (h : weightsOnRows S first values = some g) (hl : S.matrixRows ≤ 2 ^ S.kRow) :
    ∀ t ∈ g, Low S.kRow S.matrixRows t := by
  unfold weightsOnRows at h
  split at h
  · rename_i h1
    split at h
    · rename_i h2
      have h2' := (Bool.and_eq_true_iff.1 h2).1
      dsimp only at h
      split at h
      · obtain rfl := Option.some.inj h
        exact stretchBlocks_low S.kRow first values S.matrixRows
          (Nat.le_of_lt (of_decide_eq_true h2')) h1 hl _ first (Nat.le_refl _)
      · cases h
    · cases h
  · cases h

/-- **At the row that pendingRowO returns, at its own shape.** -/
theorem pendingRowO_low {lay : WsLay} {indexMasks : Nat} {o : WsForkOut} {claims : Nat}
    {S : LinShape} {oracles oracles' : Array Oracle} {row : TensorRow}
    (h : VerifiableInference.Desc.First.Pend.pendingRowO lay indexMasks o claims S oracles =
      .ok (row, oracles')) : ∀ t ∈ row.g, Low S.kRow S.matrixRows t := by
  unfold VerifiableInference.Desc.First.Pend.pendingRowO at h
  have c4 := (VerifiableInference.Desc.First.Pend.unless_ok h).1
  have h := (VerifiableInference.Desc.First.Pend.unless_ok h).2
  have h := (VerifiableInference.Desc.First.Pend.unless_ok h).2
  have h := (VerifiableInference.Desc.First.Pend.unless_ok h).2
  have h := (VerifiableInference.Desc.First.Pend.unless_ok h).2
  obtain ⟨⟨first, last⟩, -, h⟩ := VerifiableInference.Desc.First.Pend.bind_ok h
  have h := (VerifiableInference.Desc.First.Pend.unless_ok h).2
  have h := (VerifiableInference.Desc.First.Pend.unless_ok h).2
  have h := (VerifiableInference.Desc.First.Pend.unless_ok h).2
  have c12 := (VerifiableInference.Desc.First.Pend.unless_ok h).1
  have h := (VerifiableInference.Desc.First.Pend.unless_ok h).2
  obtain ⟨Gamma, -, h⟩ := VerifiableInference.Desc.First.Pend.bind_ok h
  have hl : S.matrixRows ≤ 2 ^ S.kRow := by
    have e : lay.m0 = S.matrixRows := by simpa using c4
    rw [← e]
    simpa using c12
  split at h
  · rename_i g hg
    split at h
    · split at h
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact weightsOnRows_low hg hl
      · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
    · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.stretchBlocks_low
#print axioms Johnson.AtFull.Shape.Scope.weightsOnRows_low
#print axioms Johnson.AtFull.Shape.Scope.pendingRowO_low
