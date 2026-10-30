-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsLayNu.lean: `tupleW` AND `nuLay` (Johnson/Road/K4/K4PinsPlanes.lean) ARE THE
LOOKUP's CALLER's OWN `layMs` AND `layNu` (Johnson/Desc/First/Look/K3LayGoodIn.lean), at
msgW w := enc w.cells. Until here that was said by reading alone. Two equations, by unfolding, and
the three items worth at the caller's own names.

  `tupleW_layMs`: `tupleW x D rad seatT oW enc arr w = layMs x D rad oW seatT arr (enc ∘ cells) w`.
  `nuLay_layNu`: `nuLay … (matIx q.y).iB (tupleW … w) = layNu x q tl D rad oW wOf nr nc seatT arr
    (enc ∘ cells) w`.

OBJECT: none of its own. USER: none yet; meant: whoever holds the lines planes, keys, rider of
`K4Lines` against a meaning whose field worth is filled at `layNu`, `layMu`, `layMs`. LETTERS: those
of K4PinsPlanes.lean, and the caller's public letters q.

Limits. K04_law IS NOT PROVED BY THIS. Two names for one term each: nothing more. `layNu` reads the
number of the planes' matrix off the caller's layout q.y; the road's sentence off the plan's: they
are one where q.y is the plan's layout: not asked here.
-/
import Johnson.Road.K4.K4PinsPlanes
import Johnson.Desc.First.Look.K3LayGoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open OnBytes.Model (HTailF2)
open OnBytes.Model.Layer (matIx)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First.Look (Sent sigListCalls LayPub)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (layMs layNu)

variable (x : VerifiableInference.Desc.First.Look.Place) (q : LayPub) (D : Sent)
  (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (tl : HTailF2) (oW : Cb.OMsg Cb.Gl.E) {Cells Tok : Type} (enc : Cells → oW.Msg)
  (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ) (arr : ℕ → ℕ → ℕ)

/-- **`tupleW` is the caller's `layMs`.** -/
theorem tupleW_layMs (w : Wit Cells Tok MsgT) :
    tupleW x D rad seatT oW enc arr w =
      layMs x D rad oW seatT arr (fun w : Wit Cells Tok MsgT => enc w.cells) w := by
  funext a
  cases a <;> rfl

/-- **`nuLay` is the caller's `layNu`.** -/
theorem nuLay_layNu (w : Wit Cells Tok MsgT) :
    nuLay x D rad tl oW wOf nr nc (matIx q.y).iB (tupleW x D rad seatT oW enc arr w) =
      layNu x q tl D rad oW wOf nr nc seatT arr (fun w : Wit Cells Tok MsgT => enc w.cells) w := by
  funext pq
  unfold nuLay layNu VerifiableInference.OnPublicFiles.layMu
  rw [tupleW_layMs]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.tupleW_layMs
#print axioms OnBytes.Road.K4.nuLay_layNu
