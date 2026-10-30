-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/ShapeAtW.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME
FOR THE HONEST SIDE: AT W's SENDING, AT EVERY SIZE: MESSAGE NUMBER 0 OF THE PLAN K1.parW HAS THE
SHAPE LinShape.w, AND THE PLAN's CODES ARE THE PARAMETERS' OWN. Three theorems; no definition.
PUBLIC: shapes and codes. IT STANDS OVER Honest/K1/PlaceW.lean ALONE, so that another house's file
 the pair at W's place can call it.

  w_first        what linMessageW answers begins with ⟨S.w, S.wLeafClass⟩
  w_shape_zero   THE STATEMENT: shapeAt (K1.parW q gp piece msg) 0 = q.lin.w, where linMessageW
                 q.lin = some msg
  parW_codes     the plan's codes are q.codes: by the plan's text

By linMessageW's text (OnBytes/Iop/Lin.lean), parW_sent (Honest/K1/PlaceW.lean), shapeAt's text
(Johnson/Prover/Send/Core.lean). What follows for the seat's public test: ClearAtW.lean.

Kin in the library. A closed fact at the full size alone: (parWF.sent[0]?).map (·.shape) = some
qFull.lin.w stands inside a test of Johnson/Desc/K1/Law/TiesWritten.lean.

Limits. Of the messages that go with W (the split's; the first fold's mask message) nothing is
said. Nothing on what any entry holds. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.PlaceW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

/-- What linMessageW answers begins with W's notice. -/
theorem w_first (S : LinShape) (msg : Array OracleNotice) (h : linMessageW S = some msg) :
    msg[0]? = some ⟨S.w, S.wLeafClass⟩ := by
  unfold linMessageW at h
  by_cases hm : S.masksAhead = true
  · simp only [hm, if_true, linMaskNotice] at h
    cases hs : S.testOwn.head? with
    | none =>
      rw [hs] at h
      cases h
    | some s =>
      rw [hs] at h
      obtain rfl := Option.some.inj h
      by_cases ho : S.ownSplitNeeded = true
      · simp [ho]
      · simp [ho]
  · have hf : S.masksAhead = false := by simpa using hm
    simp only [hf, Bool.false_eq_true, if_false] at h
    obtain rfl := Option.some.inj h
    by_cases ho : S.ownSplitNeeded = true
    · simp [ho]
    · simp [ho]

/-- **MESSAGE NUMBER 0 OF W's PLAN HAS W's SHAPE**, at every size. -/
theorem w_shape_zero (q : Params.First) (gp : _root_.Desc.Plain.GPar) (piece : Nat)
    (msg : Array OracleNotice) (h : linMessageW q.lin = some msg) :
    shapeAt (K1.parW q gp piece msg) 0 = q.lin.w := by
  unfold shapeAt
  rw [parW_sent, Array.getD_eq_getD_getElem?, w_first q.lin msg h]
  rfl

/-- The plan's codes are the parameters' own. -/
theorem parW_codes (q : Params.First) (gp : _root_.Desc.Plain.GPar) (piece : Nat)
    (msg : Array OracleNotice) : (K1.parW q gp piece msg).codes = q.codes := rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.w_first
#print axioms ProofFile.Honest.K1.w_shape_zero
#print axioms ProofFile.Honest.K1.parW_codes
