-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/KeyLookup/CloseFm.lean: the formats of the rounds of the join point, the closing, the zero
point and the test of the bits are those of their shares of the list of rounds.

It imports CloseRun.lean (`fmClo`, `fmBits`, `Clo.fmM`) and Cb/Pv/KeyLookup/LamFm.lean (`rowFm`; the
shares `lamJoin`, `lamClo`, `lamZero`, `lamBits` are those of Cb/Pv/KeyLookup/Lam.lean); no file of
the port.
Main names:
  `Clo.fmM_eq`    the formats of k rounds with a degree for each variable, as a list.
  `join_fm`, `clo_fm`, `zero_fm`, `bits_fm`   each block's list of formats is `rowFm` along its
                  share, for every q.
Limits: no condition is asked. Nothing on the port's plan.

-/
import Cb.Pv.KeyLookup.CloseRun
import Cb.Pv.KeyLookup.LamFm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Cb Cb.LdLkp Flat

theorem Clo.fmM_eq : ∀ (k : ℕ) (dg : Fin k → ℕ),
    Clo.fmM k dg = (List.ofFn dg).map fun n => (⟨n, 1, false⟩ : Fm)
  | 0, _ => by simp [Clo.fmM]
  | k + 1, dg => by
    rw [List.ofFn_succ, List.map_cons, ← Clo.fmM_eq k fun i => dg i.succ]
    rfl

namespace Dat
variable {E : Type} [Field E] [Fintype E] (A : Dat E) (q : ℕ)

theorem join_fm :
    [(⟨0, A.mu, false⟩ : Fm)] = (lamJoin q A.toPub).map (rowFm A.toPub) := rfl

theorem zero_fm :
    [(⟨0, A.mu + A.d, false⟩ : Fm)] = (lamZero q A.toPub).map (rowFm A.toPub) := rfl

theorem clo_fm : A.fmClo = (lamClo q A.toPub).map (rowFm A.toPub) := by
  unfold fmClo
  rw [Clo.fmM_eq, dgEnd_rev]
  simp [lamClo, psc, rowFm, rowDraws, LRow.short, Function.comp_def]
  rfl

theorem bits_fm : A.fmBits = (lamBits q A.toPub).map (rowFm A.toPub) := by
  unfold fmBits
  simp [lamBits, psc, rowFm, rowDraws, LRow.short, Function.comp_def]
  rfl

end Dat
end Lk6

#print axioms Lk6.Dat.join_fm
#print axioms Lk6.Dat.zero_fm
#print axioms Lk6.Dat.clo_fm
#print axioms Lk6.Dat.bits_fm
