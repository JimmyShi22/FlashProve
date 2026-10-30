-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Out/TwOutEq.lean.
At the filling `V₀`, `V₀C` the typed lookup's verifier puts out the flat function's rows at the
transcript read as plain data.

Theorems with their proofs.
Main names:
  `run_b27`, `run_st`: the caller's state read off the last state of a run is the caller's.
  `run_rows`: `outA A kAt (A.rd (chnV (SV₀ E Ex) A st τ)) = (vOf (numsOf A st kAt) (flChn Ex A
    τ)).map toRow`.
  `one_out`: for every A, kAt, statement a and typed transcript τ: `(oneK A kAt V₀ V₀C Ex).R.red.out
    a τ = some ((vOf (numsOf A a.1 kAt) (flChn Ex A τ)).map toRow, a.2)`: it never refuses; each
    sparse row is spread (`toRow`); the oracles are copied.
  `o65R₀_flat`: the same of `o65R₀ Ex` at the record `o65N`.
Limits: at the filling `V₀`, `V₀C` (Cb/G6/Pick.lean) alone. The equation's meaning hangs on the
reading `flChn` (Cb/Pv/Lookup/Out/TwFlat.lean) and, for a general A, on the record
`numsOf A a.1 kAt` (Cb/Pv/Lookup/Out/TwTraceOf.lean), which is read off A; at `o65A` it is `o65N`
(`o65_nums`, OnBytes/Tie/Pv/Lookup/Value/TwNumsEq.lean). The verifier's side alone.

-/
import Cb.Pv.Lookup.Out.TwStateR
import OnBytes.Tie.Pv.Lookup.Out.TwRowsEq
import OnBytes.Tie.Pv.Lookup.Know.TwOneR
import OnBytes.Tie.Pv.Lookup.Value.TwNumsEq
import OnBytes.Tie.Pv.Lookup.Port.TwRun

set_option autoImplicit false

namespace Tw
open Iop IOR Hiop Prob Cb Cb.Tw Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3

section
variable {E : Type} [Field E] [Fintype E] (Ex : ExtSpec) (A : LkAsmH E)

/-- the caller's state and λ, read off the last state of a run -/
theorem run_b27 (st : A.St) (lam : E)
    (τT : Tr (A.H.tie.tieK (SK₀ E Ex) A.n).R.shape) (ϱ : Fin (A.w + 0) → E)
    (τF : Tr (A.forestK (SK₀ E Ex) A.d).R.shape) (τE : Tr (A.endK (SK₀ E Ex)).R.shape)
    (ζ : A.Bt.zc.toIn.ev.D) (τB : Tr ((SK₀ E Ex).full A.Bt.zc.next.par).R.shape) :
    A.b2 (A.oR (A.o4 (A.oldT ((SV₀ E Ex).full A.Bt.zc.next.par (A.Bt.zc.toIn.nxX
        ((SV₀ E Ex).core A.En.par (forestV (SV₀ E Ex) A A.d
          (A.R.toIn.nxX (tieV (SV₀ E Ex) A.H.tie A.n ((0 : E), (st, lam)) τT) ϱ) τF) τE) ζ) τB)))) =
      (st, lam) := by
  have h4 : A.o4 (x4Of Ex A (A.R.toIn.nxX (tieV (SV₀ E Ex) A.H.tie A.n ((0 : E), (st, lam)) τT) ϱ)
      (keyTr Ex A A.d τF)) = A.R.toIn.nxX (tieV (SV₀ E Ex) A.H.tie A.n ((0 : E), (st, lam)) τT) ϱ :=
    congrArg Prod.fst (tree_root Ex (A.IK.setV (A.v' + 1)).DK A.v' (enterK (A.IK.setV (A.v' + 1))
      (fun x => A.tK (A.oR x)) _) (keyTr Ex A A.d τF))
  have hold : A.oldT ((SV₀ E Ex).full A.Bt.zc.next.par (A.Bt.zc.toIn.nxX
        ((SV₀ E Ex).core A.En.par (forestV (SV₀ E Ex) A A.d
          (A.R.toIn.nxX (tieV (SV₀ E Ex) A.H.tie A.n ((0 : E), (st, lam)) τT) ϱ) τF) τE) ζ) τB) =
      x4Of Ex A (A.R.toIn.nxX (tieV (SV₀ E Ex) A.H.tie A.n ((0 : E), (st, lam)) τT) ϱ)
        (keyTr Ex A A.d τF) :=
    congrArg Prod.fst (forest_root Ex A A.d
      (A.R.toIn.nxX (tieV (SV₀ E Ex) A.H.tie A.n ((0 : E), (st, lam)) τT) ϱ) τF)
  rw [hold, h4]
  exact tie_base Ex A.H.tie A.n ((0 : E), (st, lam)) τT

theorem run_st (st : A.St) (τ : Tr (A.chnK (SK₀ E Ex)).R.shape) :
    (A.rd (chnV (SV₀ E Ex) A st τ)).1 = st :=
  congrArg Prod.fst (run_b27 Ex A st _ _ _ _ _ _ _)

/-- what the read-out and the last step give on a run: the flat function -/
theorem run_rows (kAt : ℕ → A.J ⊕ E) (st : A.St) (τ : Tr (A.chnK (SK₀ E Ex)).R.shape) :
    outA A kAt (A.rd (chnV (SV₀ E Ex) A st τ)) =
      (vOf (numsOf A st kAt) (flChn Ex A τ)).map toRow := by
  rw [rows_eq, run_st, state_eq Ex A st kAt τ]
  rfl

/-- The equation, for every A. -/
theorem one_out (kAt : ℕ → A.J ⊕ E) (a : A.St × Ex.Str) (τ : Tr (oneK A kAt V₀ V₀C Ex).R.shape) :
    (oneK A kAt V₀ V₀C Ex).R.red.out a τ =
      some ((vOf (numsOf A a.1 kAt) (flChn Ex A τ)).map toRow, a.2) := by
  show ((A.baseKS (SK₀ E Ex)).R.post (fun x => some (outA A kAt x)) (ExtMap.id Ex)).red.out a τ = _
  rw [red_post_out, baseK₀_out Ex A a τ]
  exact congrArg (fun r => some (r, a.2)) (run_rows Ex A kAt a.1 τ)

end

/-- The equation of `o65R₀`, for all inputs. -/
theorem o65R₀_flat (Ex : ExtSpec) (a : Unit × Ex.Str) (τ : Tr (o65R₀ Ex).shape) :
    (o65R₀ Ex).red.out a τ = some ((vOf o65N (flChn Ex o65A τ)).map toRow, a.2) := by
  have h := one_out Ex o65A (Cb.Tw.kAt Cb.Gl.E TwNums.o65S) a τ
  rw [show numsOf o65A a.1 (Cb.Tw.kAt Cb.Gl.E TwNums.o65S) = o65N from o65_nums] at h
  exact h

end Tw
#print axioms Tw.run_st
#print axioms Tw.run_rows
#print axioms Tw.one_out
#print axioms Tw.o65R₀_flat
