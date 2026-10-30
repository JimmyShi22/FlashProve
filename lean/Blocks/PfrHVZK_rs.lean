-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/PfrHVZK_rs.lean: an encoding over F, mapped into E.

`encE_algebraMap_rs`: for a code C over F and a field E above F, the encoding `C.enc m ρ`, mapped
into E, is the generator over E (`C.GE E`) applied to the full input (`C.fm`) of the mapped message
and the mapped randomness (`Code.Enc`, Code/Iface.lean).
-/
import Blocks.ClaimsTrue
import Blocks.HvzkKit_rs
import Code.Facts
import Prob.Linear
import Mathlib.Data.FinEnum
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks

open Iop Prob

/-- An encoding over F, mapped into E, is the encoding over E of the same message under the same
randomness. -/
theorem encE_algebraMap_rs {F : Type} [Field F] (C : Code.Enc F) (E : Type) [Field E] [Algebra F E]
    (m : Fin C.msg → F) (ρ : Fin C.r → F) (j : Fin C.n) :
    algebraMap F E (C.enc m ρ j) =
      (C.GE E).mulVec (C.fm (fun s => algebraMap F E (m s)) (fun t => algebraMap F E (ρ t))) j := by
  unfold Code.Enc.enc
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [C.fm_map (algebraMap F E) (map_zero _) m ρ i]
  rfl

end Blocks
