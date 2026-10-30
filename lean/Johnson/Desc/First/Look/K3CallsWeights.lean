-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/First/Look/K3CallsWeights.lean: the lookup on a LAYERS' link's calls: THE NAMED READING
OF THE WEIGHTS (WeightsAre, Johnson/Desc/First/Look/K3CallerLay.lean) AT THE INDEX's OWN MATRIX: the
premise hW of lay_model_of (Johnson/Desc/First/Look/K3CallsModel.lean), PAID at the
terms for the committed table (Johnson/Desc/First/Look/K3StoredThree.lean: the message is the
witness's cells' entries; the matrix by numbers, 0 outside): from the item pinW (the witness's cells
are what the committed table decodes to), "the meaning's decoder is that one decoder" and "the
matrix holds the index" (Flat.Holds: its cells are the casts of the index's matrix, which is 0
outside the shape). An unfolding: no new mathematics. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: a sentence on a witness of the table of joints.
USER: K3CallsModelFits.lean (hW_conduit).
  Meant: lay_model_of, lay_model_hid at the composed meaning.
LETTERS: those of K3CallsModel.lean; decT: the one decoder of the committed table; rows, cols: the
  matrix's two sizes.

Main names:
  `weightsAre_of_cells`: general in oW, wOf, nr, nc: where the caller's reading of the weights is
    the cast of Wi at every (a, b), WeightsAre holds.
  `wOfE_conduit`: at these terms the caller's reading at (a, b) is the witness's cell
    inside the shape, 0 outside.
  `hW_conduit`: hW to the letter, at these terms.

THE PREMISES, BY NAME: hpw (Mg.pinW = pinWOf decT) · hdec (H.dec is decT at the strings' cells):
  both are equations on letters that the composed meaning meets by rfl (by its authors' word).

Limits. The terms of K3StoredThree.lean alone. Nothing on who pays pinW.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsModel
import Johnson.Desc.First.Look.K3StoredThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look.Stored (oWc wOfC msgWc CellsW wOf_msgW)
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.OnPublicFiles.Flat (Holds)

section
variable {x : Desc.First.Look.Place} {tl : HTailF2} {D : Desc.First.Look.Sent}
  {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E} {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc g : ℕ}

/-- Where the caller's reading of the weights is the cast of Wi, the named reading holds. -/
theorem weightsAre_of_cells (m : (laySg x D rad oW).Msg) (Wi : Mat)
    (h : ∀ a b, wOfE (msgLay x tl D rad oW wOf nr nc m) a b = ((Wi a b : ℤ) : Cb.Gl.E)) :
    WeightsAre x tl D rad oW wOf nr nc g m Wi := by
  intro l
  have e : wOfE (msgLay x tl D rad oW wOf nr nc m) = fun a b => ((Wi a b : ℤ) : Cb.Gl.E) := by
    funext a b
    exact h a b
  rw [e]

end

section
variable {Cells Tok : Type} {rows cols : ℕ} {x : Desc.First.Look.Place} {tl : HTailF2}
  {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)

/-- **The caller's reading of the weights, at K3StoredThree.lean's terms.** -/
theorem wOfE_conduit (w : Desc.Wit (CellsW rows cols) Tok MsgT) (a b : ℕ) :
    wOfE (msgLay x tl D rad (oWc rows cols) wOfC rows cols
      (layMs x D rad (oWc rows cols) seatT arr msgWc w)) a b =
      if h : a < rows ∧ b < cols then w.cells ⟨a, h.1⟩ ⟨b, h.2⟩ else 0 := by
  unfold wOfE lyW
  by_cases ha : a < rows
  · by_cases hb : b < cols
    · rw [finOf_some ha, finOf_some hb, dif_pos ⟨ha, hb⟩]
      show wOfC (layMs x D rad (oWc rows cols) seatT arr msgWc w none) a b = _
      rw [layMs_none]
      exact wOf_msgW w a b ha hb
    · rw [finOf_some ha, dif_neg (fun h => hb h.2)]
      have e : finOf cols b = none := dif_neg hb
      rw [e]
      rfl
  · rw [dif_neg (fun h => ha h.1)]
    have e : finOf rows a = none := dif_neg ha
    rw [e]
    rfl

variable {P : Type} {X : Verify.Public} {g : ℕ}
  {Mg : Meaning P (Desc.Wit (CellsW rows cols) Tok MsgT)}
  {H : P5J.HidAt X P (Desc.Wit (CellsW rows cols) Tok MsgT) rows cols}
  {decT : (ℕ → Option (ℕ × List UInt64)) → P × P5J.TS → Option (CellsW rows cols)}

/-- **hW, at K3StoredThree.lean's terms.** -/
theorem hW_conduit (hpw : Mg.pinW = pinWOf decT) (hdec : H.dec = fun a y => decT y.cell a)
    (z : P) :
    ∀ s y w M (i : Cm.Idx), Mg.pinW (z, s) y w → H.dec (z, s) y = some M → Holds M i →
      WeightsAre x tl D rad (oWc rows cols) wOfC rows cols g
        (layMs x D rad (oWc rows cols) seatT arr msgWc w) i.mat := by
  intro s y w M i hp hM hi
  rw [hpw] at hp
  rw [hdec] at hM
  have eM : M = w.cells := Option.some.inj (hM.symm.trans hp)
  subst eM
  refine weightsAre_of_cells _ _ fun a b => ?_
  rw [wOfE_conduit]
  by_cases h : a < rows ∧ b < cols
  · rw [dif_pos h]
    exact hi.1 ⟨a, h.1⟩ ⟨b, h.2⟩
  · rw [dif_neg h, hi.2 a b h]
    simp

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.weightsAre_of_cells
#print axioms VerifiableInference.OnPublicFiles.wOfE_conduit
#print axioms VerifiableInference.OnPublicFiles.hW_conduit
