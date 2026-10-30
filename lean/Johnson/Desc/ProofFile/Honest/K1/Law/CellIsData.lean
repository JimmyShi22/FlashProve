-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/CellIsData.lean: THE SHARED "SENDING" (the kind K1) IN THE
FRAME FOR THE HONEST SIDE: A HELD WORD OF A MAIN TABLE, INSIDE THE MESSAGE's RANGES AND OFF THE
PLACES OF ITS SAMPLE's PAD, IS WHAT THE JOB's DATA SAYS THERE. One statement and its proof. No
definition.

  held_is_data   held w₀ J.first J.P (rowsLaid J own₀ c w h) (Johnson/Prover/Send/Core.lean's held:
                 written with its full name: another held is in sight) at the place's message n, in
                 its main table, at the index of (row, place) rp: the job's data at (n, rp.1, rp.2),
                 read in the extension field as main_data_e and main_data_f read it

It joins the sealed held_new and split_index (Johnson/Prover/Send/Held.lean) with main_data_e and
main_data_f (Johnson/Desc/ProofFile/Honest/K1/DataLaw.lean). c, the part's own cut, is a bound
variable: an equation between two terms at every c; the right side does not name c.

Limits. Its four premises on rp (hr, hj, ha, hp) are asked and not proved here. hp: rp is none of
padInMain's places (Johnson/Desc/ProofFile/Honest/RowData.lean). Over the base field an element of
the extension field counts as nothing, as in rowsR. Nothing holds these rows against any Script.
Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.ProofFile.Honest.K1.ScriptAt
import Johnson.Desc.ProofFile.Honest.K1.DataLaw
import Johnson.Prover.Send.Held
import Johnson.Desc.First.Att.K05CellAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt held_new split_index)
open VerifiableInference.Desc.First.Att.P (tableIndex)

variable {W X : Type}

/-- **A held word is the data.** c: any cut. -/
theorem held_is_data (J : SendJob W X) (own₀ : X) (c : Cs (dueR J.P J.ride)) (w : W)
    (h : List Fmt.Drawn) (w₀ : Words GE) (n : ℕ) (hn : n < J.P.sent.size) (rp : ℕ × ℕ)
    (hr : rp.1 < (shapeAt J.P n).mainRows)
    (hj : rp.2 < (J.P.codes.base.getD (shapeAt J.P n).code default).ell)
    (ha : (shapeAt J.P n).answers ≠ 0)
    (hp : rp ∉ padInMain (J.P.codes.base.getD (shapeAt J.P n).code default).ell (shapeAt J.P n)) :
    Johnson.Prover.Send.held w₀ J.first J.P (rowsLaid J own₀ c w h) (J.first + n) .main
        (tableIndex (K1.clog (shapeAt J.P n).mainRows) rp) =
      if (shapeAt J.P n).mainDeg == 3 then
        match J.data w { heard := h, own := own₀, seen := .bare [] } n rp.1 rp.2 with
        | some (.inr x) => x
        | some (.inl x) => algebraMap GF GE x
        | none => 0
      else
        algebraMap GF GE (match J.data w { heard := h, own := own₀, seen := .bare [] } n rp.1 rp.2 with
        | some (.inl x) => x
        | _ => 0) := by
  obtain ⟨e1, e2⟩ := split_index rp.1 rp.2 (shapeAt J.P n).mainRows hr
  rw [held_new w₀ J.first J.P _ n hn]
  unfold tableIndex
  rw [Nat.mul_comm (2 ^ K1.clog (shapeAt J.P n).mainRows) rp.2]
  show (if (rp.1 + rp.2 * 2 ^ K1.clog (shapeAt J.P n).mainRows) %
      2 ^ K1.clog (shapeAt J.P n).mainRows < (shapeAt J.P n).mainRows then
      Rows.main _ _ _ _ else 0) = _
  rw [e1, e2, if_pos hr]
  unfold Rows.main rowsLaid
  by_cases h3 : ((shapeAt J.P n).mainDeg == 3) = true
  · rw [if_pos h3, if_pos h3]
    exact main_data_e J.P J.ride _ c n rp.1 rp.2 h3 hr hj ha hp
  · have h3' : ((shapeAt J.P n).mainDeg == 3) = false := by simpa using h3
    rw [if_neg h3, if_neg h3]
    exact congrArg _ (main_data_f J.P J.ride _ c n rp.1 rp.2 h3' hr hj ha hp)

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.held_is_data
