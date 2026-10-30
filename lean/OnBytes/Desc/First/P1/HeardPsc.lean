-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/HeardPsc.lean: WHERE THE FLAT FUNCTION OF A PRODUCT LAYER OR OF A TOKEN
SUMCHECK RETURNS, ITS RECORD IS `Ended` (OnBytes/Tie/Pv/Psc/Run/PscSeam.lean) AT THE WORDS `pscT`
(TailTape.lean): the words that the chain's data read off the tape at the sumcheck's place.
Statements and proofs.

  `tapeMu_eq`, `tapeMu2_eq`: the first and the second word that the tape's first round sent.
  `level_pscT`: `level_ended` (LevelEnded.lean) at `pscT 0 mu t`.
  `tsc_pscT`: `tsc_ended` (TscEnded.lean) at `pscT 1 lt t`.

NO NEW ARGUMENT: the two lemmas named, with `pairs_congr` (TailTape.lean): the same words under two
names. One direction: from a return.
-/
import OnBytes.Desc.First.P1.TailTape
import OnBytes.Desc.First.P1.LevelEnded
import OnBytes.Desc.First.P1.TscEnded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Road (Ended)

theorem tapeMu_eq (t : Tape) : tapeMu t = (sentOf t).getD 0 zeroE := by
  cases t with
  | nil => rfl
  | cons r u => exact headD_eq_getD r.sent zeroE

theorem tapeMu2_eq (t : Tape) : tapeMu2 t = (sentOf t).getD 1 zeroE := by
  cases t with
  | nil => rfl
  | cons r u =>
    show r.sent.tail.headD zeroE = r.sent.getD 1 zeroE
    cases r.sent with
    | nil => rfl
    | cons a l => exact headD_eq_getD l zeroE

/-- **A product layer's record, at the words that the chain's data read.** -/
theorem level_pscT {mu : Nat} {rho : Array E} {C : Aff} {order : List Nat} {F G : Fork}
    {t u : Tape} {L : Level} (h : Fl.levelIn mu rho C order F t = some (L, G, u)) :
    Ended (levelRec mu rho C order F t) C (levelRec mu rho C order F t).target (pscT 0 mu t).mu
      (pscT 0 mu t).eps F.next (levelWs mu rho order) (pscT 0 mu t).rs 2 (pscT 0 mu t).sentY
      (pscT 0 mu t).beta := by
  have e := level_ended h
  have hw : (levelWs mu rho order).length = mu := by
    unfold levelWs
    rw [List.length_map]
    exact (levelIn_heard h).1
  have e3 := pairs_congr (levelWs mu rho order) (t.drop 1)
  rw [hw] at e3
  have e3' : levelRs mu rho order t = heardPairs mu (t.drop 1) := e3
  rw [tapeMu_eq, e3'] at e
  exact e

/-- **A token sumcheck's record, at the words that the chain's data read.** -/
theorem tsc_pscT {P : Array E} {lt n dY : Nat} {F G : Fork} {t u : Tape} {o : Tsc}
    (h : Fl.tscIn P lt n dY F t = some (o, G, u)) :
    Ended o.p (Aff.slot F.next) o.p.target (pscT 1 lt t).mu (pscT 1 lt t).eps o.p.first
      (tscWs (P.toList.take lt)) (pscT 1 lt t).rs dY (pscT 1 lt t).sentY (pscT 1 lt t).beta := by
  have e := tsc_ended h
  have hl : (P.toList.take lt).length = lt := by
    rw [List.length_take, Array.length_toList]
    exact Nat.min_eq_left (tscIn_heard h).1
  have hw : (tscWs (P.toList.take lt)).length = lt := by
    unfold tscWs
    rw [List.length_map, hl]
  have e3 := pairs_congr (tscWs (P.toList.take lt)) (t.drop 1)
  rw [hw] at e3
  have e3' : tscRs P lt t = heardPairs lt (t.drop 1) := e3
  have ey : tscY P lt dY t = roundAt (OnBytes.Psc.Weight.atZero (dY + 1)) (t.drop (lt + 1)) := by
    unfold tscY
    rw [hl]
  rw [tapeMu2_eq, e3', ey] at e
  exact e

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.level_pscT
#print axioms OnBytes.Desc.First.P1.tsc_pscT
