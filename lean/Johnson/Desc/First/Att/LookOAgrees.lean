-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/LookOAgrees.lean: a yardstick beside Att/LookO.lean: its two records are
those of Att/SeatC.lean, as equalities of functions.

`lookOfO_eq`: lookOfO = lookOf. `padOfO_eq`: padOfO = padOf.
By Johnson/Desc/First/Look/ShapeOwnAgrees.lean's planesOk_eq, phiBOwn_eq and pubRunOwn_eq.
No running text imports this file.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.LookO
import Johnson.Desc.First.Att.SeatC
import Johnson.Desc.First.Look.ShapeOwnAgrees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model

theorem lookOfO_eq : lookOfO = lookOf := by
  funext lmb g
  unfold lookOfO lookOf
  rw [Look.planesOk_eq, Look.phiBOwn_eq, Look.phiBOwn_eq]

theorem padOfO_eq : padOfO = padOf := by
  funext h
  unfold padOfO padOf
  congr 1
  funext l q a b
  exact Look.pubRunOwn_eq h l q a b

end VerifiableInference.Desc.First.Att.P
