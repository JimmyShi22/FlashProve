-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Wired.lean: the two cases of `nat`.

`nat v`: a vector as a function on ℕ, 0 beyond its end (Blocks/Basic.lean). `nat_of_lt`: below the
length it is the vector's entry; `nat_of_not_lt`: from the length on it is 0.
-/
import Blocks.Decode
import Blocks.LevelDef
import Iop.InteractiveOracleProof
import Mathlib.Data.FinEnum

set_option autoImplicit false

namespace Blocks

open Iop Prob

theorem nat_of_lt {K : Type} [Zero K] {n : ℕ} (v : Fin n → K) {t : ℕ} (h : t < n) :
    nat v t = v ⟨t, h⟩ := dif_pos h

theorem nat_of_not_lt {K : Type} [Zero K] {n : ℕ} (v : Fin n → K) {t : ℕ} (h : ¬ t < n) :
    nat v t = 0 := dif_neg h

end Blocks
