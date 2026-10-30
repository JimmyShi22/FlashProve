-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttKeyPort.lean: the verifier's four key forms of an attention sub-proof, as one
family of sums of terms, with their values.

Main definition and theorem.
 - kfPort h u sd pad: the four sums of terms of Johnson/Road/Rows/AttKeyAll.lean as one family.
 - kfPort_value: under KeyPub the value of kfPort at call c is the library's key form KF at c, at
   the hidden values under the slots (kf0, kf1, kf2, kf3 at once).

What is not claimed. That the routines which put the terms together (callKR, callKFD, joinR16)
return these sums. Nothing is said about probabilities or about hiding. This file is not imported by
the program.


-/
import Johnson.Road.Rows.AttKeyAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open OnBytes.Model (Reading World Aff)
open OnBytes.Attention (Heard ShD keyKR keyKFD keyWL keyIX keyWH)
open Inst.Model (Scl)
open Inst.Model.AttSeg (Calls Pub KF)

variable {K : Type} [Field K] {ρ : Reading K} [scl : Scl] {h : Heard} {u : Units} {C : Calls}
  {p : Pub K} {sd : ShD} {pad : E} (W : World K)

/-- The verifier's four key forms, as sums of terms. -/
def kfPort (h : Heard) (u : Units) (sd : ShD) (pad : E) : Fin 4 → Aff
  | 0 => Aff.ofConst zeroE + keyKR u.pM + keyKR u.pD
  | 1 => Aff.ofConst pad + keyKFD sd u.kM + keyKFD sd u.kD
  | 2 => Aff.ofConst zeroE + keyWL h.d + keyIX h.S h.d
  | 3 => keyWH h.d

/-- The four at once. -/
theorem kfPort_value (P : KeyPub ρ h u C p sd pad) (c : Fin 4) :
    (kfPort h u sd pad c).value ρ W = KF (L5.dimOf h.S) C p (slotVal W h u) c := by
  match c with
  | 0 => exact kf0 W P
  | 1 => exact kf1 W P
  | 2 => exact kf2 W P
  | 3 => exact kf3 W P

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.kfPort_value
