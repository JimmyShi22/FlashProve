-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Order/TwWt.lean.
What the flat step (`TwV.takeSc`) is told of the variables of the closing and of the bit test.

Main names:
  `end_wt`: `Wt` (Cb/Pv/Lookup/Out/TwSc.lean) holds for the closing at the point behind the last
    table level, read in the closing's order A.oE.
  `bit_wt`: it holds for the bit test at the drawn point, read in the order A.oB, then 0 for the
    further variable (the library's dummy).
Limits: st and kAt enter through `numsOf` alone, of which only oE and oB are read here.
Not claimed: anything beyond these two lists of weights.

-/
import Cb.Pv.Lookup.Out.TwSc
import Cb.Pv.Lookup.Out.TwTraceOf
import Cb.Pv.Lookup.Alg.TwOrdL

set_option autoImplicit false

namespace Tw
open Cb Cb.Tw Cb.LdLkp TwV

section
variable {E : Type} [Field E] [Fintype E]

theorem end_wt (A : LkAsmH E) (st : A.St) (kAt : ℕ → A.J ⊕ E) (s : A.En.par.St) :
    Wt A.En.par.fmt (A.En.par.dat s)
      (inRounds (Tw3.numsOf A st kAt).oE (List.ofFn ((A.D.lv A.d).pnt s))) := by
  have e : inRounds (Tw3.numsOf A st kAt).oE (List.ofFn ((A.D.lv A.d).pnt s)) =
      List.ofFn fun j : Fin (A.w + A.d) => (A.D.lv A.d).pnt s (A.oE j) :=
    inRounds_ofFn (fun j => A.oE j) ((A.D.lv A.d).pnt s)
  rw [e]
  exact wt_mix (A.w + A.d) (dgEnd A.w A.d A.oE) fun j => (A.D.lv A.d).pnt s (A.oE j)

theorem bit_wt (A : LkAsmH E) (st : A.St) (kAt : ℕ → A.J ⊕ E) (s : A.Bt.zc.next.par.St) :
    Wt A.Bt.zc.next.par.fmt (A.Bt.zc.next.par.dat s)
      (inRounds (Tw3.numsOf A st kAt).oB (List.ofFn s.2.2) ++ [0]) := by
  have e : inRounds (Tw3.numsOf A st kAt).oB (List.ofFn s.2.2) =
      List.ofFn fun j : Fin (A.w + A.d) => s.2.2 (A.oB j) :=
    inRounds_ofFn (fun j => A.oB j) s.2.2
  rw [e]
  exact wt_snoc_dummy 2 _ _ _ (wt_eqs 2 (A.w + A.d) fun j => s.2.2 (A.oB j))

end
end Tw
