-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Desc/Lots/K3RowPaid.lean: THE LOT OF THE KIND "LOOKUP" (K3Lot.lot): ITS ROW WHERE THE
PUBLIC DATA ARE `publicOf`'s VALUE: EVERY HYPOTHESIS LEFT IS AN EQUATION WITH A WRITTEN VALUE. A
joining.
  `ReadsEq Z`: the hypotheses `Reads Z` (K3Row.lean) without the one clause that is no equation
    ("every call of the place passes callOk", at the 25 lookups on the calls).
  `reads_of_public`: that clause is paid by `callOk_at` (K3CallOk.lean: a law by the make).
  `k3_row_public`, `k3_row_publicO`: **((K3Lot.lot Z).blocks G).map skel = k3RowsW**, from `ReadsEq
    Z` and the return of `publicOf`, or of the text with the second hash function as an argument at
    OnBytes.secondHashFunction.
WHERE THE WEIGHT GOES: the return is a premise: whoever shows it walks the calls' tables there, or
needs a law on them: their cost stands once, in the return.
Limits. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K3Row
import Johnson.AtFull.Desc.Lots.K3CallOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K3
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.Desc
open VerifiableInference.Desc.K3 (quietAt)
open VerifiableInference.Desc.First.Look (lookAt beforeAt laidAt padKeyAt)
open ProofFile.Sk (skel)

/-- **The hypotheses that are equations with written values.** -/
structure ReadsEq (Z : ProofFile.Pub) : Prop where
  links : Z.first.shape.link.length = 25
  p4 : Z.p.X.p4 = true
  groups : Z.p.X.NGr = 12
  setting : Params.settingOf Z.p.X.P.frame = setW
  calls : ∀ i < 25, ∃ x, lookAt Z.p.X i false = some x ∧ viewOf true x = viewW i false
  digits : ∀ i < 25, ∃ x, lookAt Z.p.X i true = some x ∧ viewOf false x = viewW i true
  before : ∀ i < 25, ∀ d, beforeAt Z.first.codes Z.first.shape i d = some (beforeW i d)
  laid : ∀ i < 25, ∀ d, laidAt Z.p.X i d = some (pubW (sortOf i) d)
  key : ∀ i < 25, ∀ d, padKeyAt Z.p.X i d = some true
  quiet : ∀ i < 25, ∀ d, (quietAt Z.p.X i d).isSome = quietW i d
  caller : ∀ i < 25, (K3Lot.readersAt Z.p.X i).isSome = callerW i

variable {Z : ProofFile.Pub} {pol KL : ByteArray} {lay : Option ByteArray}

theorem reads_of_public (h : publicOf pol KL lay = .ok Z.p.X) (R : ReadsEq Z) : Reads Z :=
  { links := R.links, p4 := R.p4, groups := R.groups, setting := R.setting
    calls := fun i hi => by
      obtain ⟨x, hx, hv⟩ := R.calls i hi
      exact ⟨x, hx, hv, callOk_at h hx⟩
    digits := R.digits, before := R.before, laid := R.laid, key := R.key, quiet := R.quiet
    caller := R.caller }

/-- **THE LOT's ROW, EVERY HYPOTHESIS AN EQUATION, WHERE `publicOf` RETURNED.** -/
theorem k3_row_public (h : publicOf pol KL lay = .ok Z.p.X) (R : ReadsEq Z) (G : ProofFile.Ground) :
    ((K3Lot.lot Z).blocks G).map skel = k3RowsW :=
  k3_row_at (reads_of_public h R) G

/-- The same off the text with the second hash function as an argument, at OnBytes.secondHashFunction. -/
theorem k3_row_publicO
    (h : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction pol KL lay = .ok Z.p.X)
    (R : ReadsEq Z) (G : ProofFile.Ground) : ((K3Lot.lot Z).blocks G).map skel = k3RowsW :=
  k3_row_public ((VerifiableInference.PlanWritten.publicOfO_older pol KL lay).symm.trans h) R G

end Johnson.AtFull.Lots.K3

#print axioms Johnson.AtFull.Lots.K3.reads_of_public
#print axioms Johnson.AtFull.Lots.K3.k3_row_public
#print axioms Johnson.AtFull.Lots.K3.k3_row_publicO
