-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstPlain.lean: three of the named tests beside the shared table's
constant (Johnson/Desc/K14/Law/SharedConstTests.lean: hlinOk, fU9, fO10) read the codes and the
shape alone. HERE they are one test with code, and Lean's kernel evaluates it at the typed shape and
codes of a proof file and of a key file.
  ShPlain3 cs S: the three, in the words of the tests
  shPlainB, shPlainB_sound: one test with code, and what its yes gives
  shPlain_real, shPlain_key: the yes: decide +kernel
  shPlain_no: a negative test: at the typed codes and a shape whose o_u has no main row it says no

What is not claimed. That the parameters at a seat are the typed ones. Nothing on soundness, on an
honest prover or on hiding.

-/
import Johnson.Goal.Numbers.K14CondAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Johnson.G
open VerifiableInference.Desc.K1 (realSized)
open Lk6.AtPlan (keyFull)

/-- The three. -/
structure ShPlain3 (cs : Codes) (S : LinShape) : Prop where
  hlinOk : linOk cs S = true
  fU9 : 0 < S.fold.u.mainRows ∧ (S.fold.u.maskRows = 0 → cs.mask.size ≤ S.fold.u.maskCode)
  fO10 : 0 < S.omega.mainRows ∧ (S.omega.maskRows = 0 → cs.mask.size ≤ S.omega.maskCode)

/-- **The test.** -/
def shPlainB (cs : Codes) (S : LinShape) : Bool :=
  linOk cs S &&
    decide (0 < S.fold.u.mainRows ∧ (S.fold.u.maskRows = 0 → cs.mask.size ≤ S.fold.u.maskCode)) &&
    decide (0 < S.omega.mainRows ∧ (S.omega.maskRows = 0 → cs.mask.size ≤ S.omega.maskCode))

theorem shPlainB_sound {cs : Codes} {S : LinShape} (h : shPlainB cs S = true) : ShPlain3 cs S := by
  unfold shPlainB at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, of_decide_eq_true h.1.2, of_decide_eq_true h.2⟩

theorem shPlain_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧
    ShPlain3 codesFull2 x.shape := by
  obtain ⟨x, a1, -, -⟩ := k14_real
  have h : (realSized.any fun p => shPlainB p.2 p.1.shape) = true := by decide +kernel
  rw [a1, Option.any_some] at h
  exact ⟨x, a1, shPlainB_sound h⟩

theorem shPlain_key : ShPlain3 keyFull.codes keyFull.once.shape :=
  shPlainB_sound (by decide +kernel)

/-- **It can say no.** -/
theorem shPlain_no : shPlainB keyFull.codes
    { keyFull.once.shape with
      fold := { keyFull.once.shape.fold with
        u := { keyFull.once.shape.fold.u with mainRows := 0 } } } = false := by
  decide +kernel

end Desc.K14.Law

#print axioms Desc.K14.Law.shPlainB_sound
#print axioms Desc.K14.Law.shPlain_real
#print axioms Desc.K14.Law.shPlain_key
#print axioms Desc.K14.Law.shPlain_no
