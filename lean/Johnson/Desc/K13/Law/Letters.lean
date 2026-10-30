-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Letters.lean: what two sentences about the first chain's record mean, each as a
definition of its own, for whoever states a relation border by border: "all rows on the table are
true", and "the row (Eval) says its claim of the words". Definitions, and statements with their
proofs.
Main names:
  `RowsTrue rw s w`: every row on the table (`S.rows`: the pile, in front of the batching; behind it
    the one row, read off the claim) is true of what the reader takes from the witness.
  `rowsHold_iff`, `rowsHoldA_iff`: it is the second half of `RowsHold` and of `RowsHoldA`.
  `rowsTrue_nil`: where no row is on the table it holds of every witness.
  `rowsTrue_congr`: it reads the matrix, and the mask entries of one message, alone, where the rows
    name that message's entries alone.
  `WRow P s m`: the row (Eval), made of the record's claim at W's layout, says its claim of the
  words.
  `claim_of_wrow`: `claim_of_laid` (Johnson/Desc/K13/Law/Laid.lean) with that one sentence in the
    place of "all that the statement claims holds of the words".
Used of `verify-on-bytes`, pure functions: `linEvalRow`, `linLayW`.

What is not claimed. These are meanings, not truths: who shows `WRow` is the kind that closes the
own group's open rows; who shows `RowsTrue` in front of the batching are the kinds that lay rows on
the pile. `WIs` is given by no law yet. The number nR of the matrix's rows is a free letter. `WRow`
holds of all words where nothing goes on to the third chain, or where the row is not made: it says
something only beside `EvalLaid`.

-/
import Johnson.Desc.K13.Law.PinA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Means (Words Says)
open VerifiableInference.Desc.First (S rowOfClaim)
open VerifiableInference.Desc.Sound (Frame)

variable {W : Type} {nR : ℕ}

/-- **All rows on the table are true.** -/
def RowsTrue {k : ℕ} (rw : W → Wit GE nR k) (s : S) (w : W) : Prop :=
  ∀ r ∈ s.rows, Holds ρg (rw w) r

/-- It is the second half of `RowsHold`. -/
theorem rowsHold_iff {F : Frame} {k : ℕ} (rw : W → Wit GE nR k) (Pin : F.E.Str → W → Prop)
    (a : S × F.E.Str) (w : W) : RowsHold rw Pin a w ↔ Pin a.2 w ∧ RowsTrue rw a.1 w := Iff.rfl

/-- And of `RowsHoldA`. -/
theorem rowsHoldA_iff {F : Frame} {k : ℕ} (rw : W → Wit GE nR k) (Pin : S × F.E.Str → W → Prop)
    (a : S × F.E.Str) (w : W) : RowsHoldA rw Pin a w ↔ Pin a w ∧ RowsTrue rw a.1 w := Iff.rfl

/-- Where no row is on the table it holds of every witness. -/
theorem rowsTrue_nil {k : ℕ} (rw : W → Wit GE nR k) {s : S} (hs : s.rows = []) (w : W) :
    RowsTrue rw s w := by
  intro r hr
  rw [hs] at hr
  cases hr

/-- It reads the matrix, and the mask entries of one message, alone. -/
theorem rowsTrue_congr {k : ℕ} (rw : W → Wit GE nR k) {s : S} {idx : ℕ}
    (hs : ∀ r ∈ s.rows, OnLedger idx r) {w w' : W} (h : AgreeAt idx (rw w) (rw w')) :
    RowsTrue rw s w ↔ RowsTrue rw s w' :=
  ⟨fun H r hr => (holds_congr ρg (hs r hr) h).1 (H r hr),
    fun H r hr => (holds_congr ρg (hs r hr) h).2 (H r hr)⟩

/-- **The row (Eval) says its claim of the words.** -/
def WRow (P : Where) (s : S) (m : Words GE) : Prop :=
  ∀ l r, linAt s = some l →
    linEvalRow P.lin l.claim l.w (linLayW s.st.codes P.lin) = some r → Says ρg s.st r m

/-- **At any record that has `EvalLaid`**: that one sentence, and "W's message holds g^T M", give
that all rows on the table are true. -/
theorem claim_of_wrow {P : Where} {s : S} (hL : EvalLaid P s) (m : Words GE)
    (mat : Fin nR → (Fin P.lin.kCol → Bool) → GE) (hR : WRow P s m)
    (hW : ∀ l, linAt s = some l → WIs mat m l.claim.g l.w (linLayW s.st.codes P.lin)) :
    ∀ r ∈ s.rows, Holds ρg (witOf mat m) r := by
  obtain ⟨l, row, r, G, hlin, hrow, hbits, hr, hG, hmem, hE⟩ := hL
  have hS : Says ρg s.st r m := hR l r hlin (by rw [hrow]; exact hr)
  have hW' := hW l hlin
  rw [hrow] at hW'
  have hH' := (eval_back nR P.lin row l.w _ r s.st m mat hbits hr hE hW').1 hS
  have hrows : s.rows = [row] := by
    unfold linAt at hlin
    unfold S.rows
    split at hlin
    · next a hs =>
      simp only [hs, hlin, hrow, rowOfClaim_member]
    · cases hlin
  intro r' hr'
  rw [hrows] at hr'
  rw [List.mem_singleton.1 hr']
  exact hH'

/-- All that the statement claims gives that sentence, at a record that has `EvalLaid`. -/
theorem wrow_of_holds {P : Where} {s : S} (hL : EvalLaid P s) (m : Words GE)
    (hH : OnBytes.Means.Holds ρg s.st m) : WRow P s m := by
  obtain ⟨l, row, r, G, hlin, hrow, _, hr, hG, hmem, _⟩ := hL
  intro l' r' hl' hr'
  rw [hlin] at hl'
  obtain rfl := Option.some.inj hl'
  rw [hrow, hr] at hr'
  obtain rfl := Option.some.inj hr'
  exact hH.rows _ G hG r hmem

end VerifiableInference.Desc.K13.Law
