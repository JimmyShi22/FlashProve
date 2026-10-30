-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/LaidAt.lean: the record of (Eval) (`EvalAt`,
Johnson/Desc/K13/Law/StepBack.lean) read off the first chain's record: a reader with code, and that
it gives a record with the three public facts wherever the block behind W's commitment has left what
it leaves (`EvalLaid`, Johnson/Desc/K13/Law/Laid.lean). A definition, and statements with their
proofs.
Main names:
  `laidOf P s`: the reader: the claim's row, W's number, W's layout under the record's codes, the
    row (Eval) made of them, the record's statement; nothing where no claim lies or no row is made.
  `laidOf_ok`: **at a record that has `EvalLaid` it gives a record that is `Ok`, and the rows on the
    table are just its row.** So `EvalAt.Ok` has a member of the kind that is meant wherever
    `EvalLaid` has one: `rowsB_lays` makes it behind W's commitment.
  `laidOf_says`, `laidOf_true`: there "the record's (Eval) says its claim" is `WRow`, and "the
    record's row is true" is `RowsTrue` (Johnson/Desc/K13/Law/Letters.lean): the two sentences in
    which the step back from (Eval) is said at a reader are K13's files' two letters.
  `laidOf_none`: a try: where no claim lies the reader gives nothing.

What is not claimed. That a record has `EvalLaid`. Nothing on soundness.

-/
import Johnson.Desc.K13.Law.Letters
import Johnson.Desc.K13.Law.StepBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Means (Words Says)
open VerifiableInference.Desc.First (S rowOfClaim)

variable {W : Type} {nR : ℕ}

/-- **The reader.** -/
def laidOf (P : Where) (s : S) : Option EvalAt :=
  (linAt s).bind fun l =>
    (linEvalRow P.lin l.claim l.w (linLayW s.st.codes P.lin)).map fun r =>
      ⟨rowOfClaim l.claim, l.w, linLayW s.st.codes P.lin, r, s.st⟩

/-- **At a record that has `EvalLaid`.** -/
theorem laidOf_ok {P : Where} {s : S} (hL : EvalLaid P s) :
    ∃ D, laidOf P s = some D ∧ D.Ok P.lin ∧ s.rows = [D.row] ∧ D.st = s.st ∧
      ∃ l, linAt s = some l ∧ D.w = l.w ∧ D.lay = linLayW s.st.codes P.lin ∧
        l.claim = memberClaim D.row := by
  obtain ⟨l, row, r, G, hlin, hrow, hbits, hr, _, _, hE⟩ := hL
  have hrows : s.rows = [row] := by
    unfold linAt at hlin
    unfold S.rows
    split at hlin
    · next a hs =>
      simp only [hs, hlin, hrow, rowOfClaim_member]
    · cases hlin
  refine ⟨⟨row, l.w, linLayW s.st.codes P.lin, r, s.st⟩, ?_, ⟨hbits, hr, hE⟩, hrows, rfl, l, hlin,
    rfl, rfl, hrow⟩
  unfold laidOf
  rw [hlin]
  show (linEvalRow P.lin l.claim l.w (linLayW s.st.codes P.lin)).map _ = _
  rw [hrow, hr, rowOfClaim_member]
  rfl

/-- There "the record's (Eval) says its claim" is `WRow`. -/
theorem laidOf_says {P : Where} {s : S} (hL : EvalLaid P s) (m : Words GE) :
    (∃ D, laidOf P s = some D ∧ Says ρg D.st D.r m) ↔ WRow P s m := by
  obtain ⟨D, hD, hok, _, hst, l, hlin, hw, hlay, hcl⟩ := laidOf_ok hL
  constructor
  · rintro ⟨D', hD', hS⟩ l' r' hl' hr'
    rw [hD] at hD'
    obtain rfl := Option.some.inj hD'
    rw [hlin] at hl'
    obtain rfl := Option.some.inj hl'
    have e := hok.2.1
    rw [hw, hlay, ← hcl, hr'] at e
    rw [Option.some.inj e, ← hst]
    exact hS
  · intro H
    refine ⟨D, hD, ?_⟩
    rw [hst]
    refine H l D.r hlin ?_
    rw [hcl, ← hw, ← hlay]
    exact hok.2.1

/-- And "the record's row is true" is `RowsTrue`. -/
theorem laidOf_true {k : ℕ} {P : Where} {s : S} (hL : EvalLaid P s) (rw : W → Wit GE nR k) (w : W) :
    (∃ D, laidOf P s = some D ∧ Holds ρg (rw w) D.row) ↔ RowsTrue rw s w := by
  obtain ⟨D, hD, _, hrows, _⟩ := laidOf_ok hL
  constructor
  · rintro ⟨D', hD', hH⟩ r hr
    rw [hD] at hD'
    obtain rfl := Option.some.inj hD'
    rw [hrows] at hr
    rw [List.mem_singleton.1 hr]
    exact hH
  · intro H
    exact ⟨D, hD, H D.row (by rw [hrows]; exact List.mem_singleton.2 rfl)⟩

/-- **A try**: where no claim lies the reader gives nothing. -/
theorem laidOf_none {P : Where} {s : S} (h : linAt s = none) : laidOf P s = none := by
  unfold laidOf
  rw [h]
  rfl

end VerifiableInference.Desc.K13.Law
