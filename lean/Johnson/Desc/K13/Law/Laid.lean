-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Laid.lean: the law of kind K13's block behind W's commitment, cut in two: what
the block leaves in the public record, and what follows from that at ANY later record that still has
it. So the second half can be called where the claim on the weights is closed, on a later chain.
Statements with their proofs.
Main names:
  `EvalLaid P s`: a condition on the public record alone: the claim is made of a row; W's vector
    fits its table; the row (Eval), made of the claim at W's layout under the record's codes, is
    among the open rows of the own group; its summands lie within tables that the statement has.
  `rowsB_lays`: where the block says yes, from a record that is as promised, the record behind has
  it.
  `claim_of_laid`: **at any record that has it**: if all that the statement claims holds of the
    words, and W's message holds g^T M, all rows on the table are true. No chance, no pin.
  `atM4_goodIn_laid`: the law of the joined block with `EvalLaid P` as the promise behind it.
Used of `verify-on-bytes`: what Johnson/Desc/K13/Law/M4.lean names.

What is not claimed. That later blocks keep `EvalLaid`: they have to leave the claim, the codes, the
tables and the own group's open rows. `WIs`: see Johnson/Desc/K13/Law/Eval.lean.
`WIs` is given by no law yet. The number nR of the matrix's rows is a free letter: that it is the
plan's is said nowhere but in Johnson/Desc/K13/Law/Caller.lean.

-/
import Johnson.Desc.K13.Law.AtM4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice Iop Run
open OnBytes.Means (Words Says)
open VerifiableInference.Desc.First (S rowOfClaim)
open VerifiableInference.Desc.Sound (Frame Piece)

variable {Cl W : Type} {nR : ℕ}

/-- **What the block leaves in the public record.** -/
def EvalLaid (P : Where) (s : S) : Prop :=
  ∃ (l : LinFirst) (row : TensorRow) (r : OnBytes.Row) (G : Group),
    linAt s = some l ∧ l.claim = memberClaim row ∧
    P.lin.kCol ≤ (linLayW s.st.codes P.lin).bits ∧
    linEvalRow P.lin (memberClaim row) l.w (linLayW s.st.codes P.lin) = some r ∧
    s.st.groups[l.own]? = some G ∧ r ∈ G.rows.toList ∧
    EvalIn s.st l.w (linLayW s.st.codes P.lin) row.masks

/-- Where the block says yes, from a record that is as promised, the record behind has it. -/
theorem rowsB_lays {F : Frame} {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (rowsB (Cl := Cl) atS P).decide s rs gs = .ok s')
    (y : F.E.Str) (hon : FrontOk P ((s, y) : S × F.E.Str)) : EvalLaid P s' := by
  obtain ⟨m₀, l, o, owed, hs, hl, hrows, rfl⟩ := rowsB_at h
  have hlin : linAt s = some l := by
    unfold linAt
    rw [hs]
    exact hl
  obtain ⟨⟨row, hrow⟩, hbits⟩ := hon l hlin
  obtain ⟨d₃, r, G, hc, _, hr, hG, hin, hst, hcodes⟩ := rows_ok hrows
  rw [hrow] at hr
  have hr' : linEvalRow P.lin (memberClaim row) o.1.w (linLayW s.st.codes P.lin) = some r := hr
  obtain ⟨hlen, hform⟩ := linEvalRow_inv P.lin _ _ _ r hr'
  have hcodes' : o.2.st.codes = s.st.codes := hcodes
  have hE : EvalIn o.2.st o.1.w (linLayW s.st.codes P.lin) row.masks := by
    rw [hst]
    refine evalIn_withRow _ _ (evalIn_of_rowIn (G := G) ?_ ?_)
    · have : row.psi.length = P.lin.kCol := hlen
      rw [this]
      exact hbits
    · rw [← hform]
      exact hin
  obtain ⟨G', hG', hmem⟩ := mem_withRow r hG
  rw [← hst] at hG'
  refine ⟨o.1, row, r, G', rfl, by rw [hc, hrow], ?_, ?_, hG', hmem, ?_⟩
  · show P.lin.kCol ≤ (linLayW o.2.st.codes P.lin).bits
    rw [hcodes']
    exact hbits
  · show linEvalRow P.lin (memberClaim row) o.1.w (linLayW o.2.st.codes P.lin) = some r
    rw [hcodes']
    exact hr'
  · show EvalIn o.2.st o.1.w (linLayW o.2.st.codes P.lin) row.masks
    rw [hcodes']
    exact hE

/-- **At any record that has it**: all that the statement claims, and "W's message holds g^T M",
give that all rows on the table are true. -/
theorem claim_of_laid {P : Where} {s : S} (hL : EvalLaid P s) (m : Words GE)
    (mat : Fin nR → (Fin P.lin.kCol → Bool) → GE) (hH : OnBytes.Means.Holds ρg s.st m)
    (hW : ∀ l, linAt s = some l → WIs mat m l.claim.g l.w (linLayW s.st.codes P.lin)) :
    ∀ r ∈ s.rows, Holds ρg (witOf mat m) r := by
  obtain ⟨l, row, r, G, hlin, hrow, hbits, hr, hG, hmem, hE⟩ := hL
  have hS : Says ρg s.st r m := hH.rows _ G hG r hmem
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

/-- **The law of the joined block at the place of W's commitment, with the promise behind it.** -/
theorem atM4_goodIn_laid {F : Frame} (P : Where) (pcW : Piece (ckP .two) F S Cl W)
    (on : S × F.E.Str → Prop) (R : S × F.E.Str → W → Prop)
    (rwM : W → Fin nR → (Fin P.lin.kCol → Bool) → GE) (rwW : W → Words GE)
    (Pin : F.E.Str → W → Prop)
    (hW : pcW.GoodIn on (FrontOk P) R (RowsHold (fun w => witOf (rwM w) (rwW w)) Pin)) :
    (Piece.then pcW "W's commitment, the own group and (Eval)" (rowsB atS P)).GoodIn on
      (fun b => EvalLaid P b.1) R (Behind P rwM rwW Pin) :=
  goodIn_then pcW _ (rowsB atS P) rfl on (FrontOk P) (fun b => EvalLaid P b.1) R _ _ hW
    fun _ _ y hon hd => ⟨rowsB_lays hd y hon, fun w hw => rowsB_core hd rwM rwW Pin y hon w hw⟩

end VerifiableInference.Desc.K13.Law
