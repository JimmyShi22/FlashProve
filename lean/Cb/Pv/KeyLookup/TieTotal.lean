-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/TieTotal.lean: at the short sumcheck the verifier of the lookup's first two
sub-protocols (the draw of the first challenge and the fused tie: Cb/Pv/KeyLookup/TieM.lean) never
rejects.

Why it is wanted. Knowledge soundness holds idly of a reduction that rejects every transcript. Here:
at every state, every oracle string and every transcript the verifier puts out a new state.

It imports no file of the program (OnBytes/Iop, OnBytes/Params, ...).

Main names:
  `Tie.eq0`: at every step of the tie each variable's weights sum to 1; a step's one variable is the
  library's dummy variable Y. This is the condition under which the short sumcheck's verifier puts
  out a statement at every transcript.
  `Tie.step_total_short`, `Tie.tie_total_short`: one step; the steps 0, .., n in a row.
  `head_total_short`: `Total (A.headK L (SK₀ E Ex) n).R`, with no condition.
Limits: not claimed: the like at the library's own sumcheck, whose verifier tests a sum in each
round with a polynomial and can reject; what the state that is put out is, as a function of the
transcript.

-/
import Cb.Pv.KeyLookup.TieShort
import Cb.Pv.KeyLookup.AsmTotal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn

namespace Tie
variable {E : Type} [Field E] [Fintype E] (D : TieF E) (Ex : ExtSpec)

/-- Every variable's weights sum to 1: there is Y alone. -/
theorem eq0 (l : ℕ) : TWhole.Eq0 (D.lv l).T.par :=
  TWhole.our_eq0 (D.lv l).T fun st v hv => by
    have h : (D.lv l).T.vars st = [] := by
      cases l <;> rfl
    rw [h] at hv
    exact absurd hv List.not_mem_nil

theorem step_total_short (l : ℕ) : Total (D.stepK (SK₀ E Ex) l).R :=
  total_postM (D.nxt l) fun x y τ => ⟨_, SK₀_out Ex (D.lv l).T.par (eq0 D l) x y τ⟩

theorem tie_total_short (n : ℕ) : Total (D.tieK (SK₀ E Ex) n).R :=
  total_chain (fun l => E × (D.lv l).T.St) (D.stepK (SK₀ E Ex)) (step_total_short D Ex) n

end Tie

/-- The verifier of the draw and the tie, at the short sumcheck, never rejects. -/
theorem head_total_short {E : Type} [Field E] [Fintype E] (A : Dat E) (L : TiePl E A.J)
    (Ex : ExtSpec) (n : ℕ) : Total (A.headK L (SK₀ E Ex) n).R :=
  total_seq (total_drawK E A.ini (A.allKeys - 1))
    (total_postM (A.back L n)
      (total_preM (fun x : A.XS => ((0 : E), x)) (Tie.tie_total_short (A.tie L) Ex n)))

end Lk6

#print axioms Lk6.Tie.eq0
#print axioms Lk6.head_total_short
