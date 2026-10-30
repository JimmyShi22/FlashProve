-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyFillSame.lean: ONE LINE: the filling's reader of the witness (kreadFam, Johnson/RunOne/KeyFillBaseAt.lean) has as its «same» the tables' own sameGl (Johnson/Desc/Key/KeyCoin.lean): «read as one element of the field». Used for the premise hsame of row 1.16.
OBJECT: KRead.same at kreadFam; sameGl · USER: r1_16_whole (hsame), Johnson/Top/Fire/Code/Row116Whole.lean · LETTERS: cs l num at_ tab. Nothing on soundness.
-/
import Johnson.RunOne.KeyFillBaseAt
import Johnson.Desc.Key.KeyCoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open VerifiableInference.Desc.Key

theorem kreadFam_same (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (num : Fin l.length → ℕ) (at_ : Where) {Cells : Type} (tab : Cells → ℕ → ℕ → OnBytes.F) :
    (kreadFam cs l num at_ tab).same = sameGl := rfl

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.kreadFam_same
