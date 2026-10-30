-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Reader3.lean: OVER A STEP OF KIND K13's BLOCK THE READER THROUGH THE RECORD's
OWN BOOK (`rwBook`, Johnson/Desc/K13/Law/ReaderByBook.lean) IS THE SAME: the block leaves the
book, the code table and every message's shape. So `Others3.reader`
(Johnson/Desc/K13/Law/FillFromSentences.lean) is paid at that reader. Statements with their
proofs.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.ReaderByBook
import Johnson.Desc.K13.Law.RidersK12

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Ground (shapesIn)

section
variable {Pp Cl Cells Tok : Type} {nR k : ℕ} (arr : ℕ → ℕ → ℕ)
  (mat : Cells → Fin nR → (Fin k → Bool) → GE)

/-- The list of shapes gives each message's. -/
theorem shape_at_of_list {st st' : Statement} (h : shapesIn st' = shapesIn st) (o : ℕ) :
    (st'.oracles[o]?).map (·.shape) = (st.oracles[o]?).map (·.shape) := by
  have e : ∀ S : Statement, (shapesIn S)[o]? = (S.oracles[o]?).map (·.shape) := fun S => by
    unfold shapesIn
    rw [List.getElem?_map, Array.getElem?_toList]
  rw [← e st', ← e st, h]

/-- **`Others3.reader` at this reader.** -/
theorem reader3 {P : Where} (x x' : Pp × S) (w : Desc.Wit Cells Tok MsgT)
    (h : StepM3 Cl P x x') (h0 : RowsTrue (rwBook arr mat x') x'.2 w) :
    RowsTrue (rwBook arr mat x) x'.2 w := by
  intro r hr
  rw [← rwBook_same arr mat x x' (core_same_M3 h).1 (plan_same_M3 h).1
    (shape_at_of_list (shapes_same_M3 h)) w]
  exact h0 r hr

end

end VerifiableInference.Desc.K13.Law
