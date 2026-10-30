-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Run/OverOneFRun.lean: the third exit (`OComp.overOneF`, Rom/OverOneF.lean) under one fixed hash
function: its result (`det`), and its run in the syntax of ZKCP/Defs.lean: the twins of
`det_overOne` (Run/DetOverOne.lean) and of `run_exit` (Run/RunIsVProofs.lean).

Main names.
  `Rom.det_askFirst`    the result of `askFirst` is `valFirst`.
  `Rom.det_overOneF`    (c.overOneF m more).det g = c.det (readBlocks m g), where c factors.
  `Run.run_exitF`       a typed tree without coins that factors, by the third exit, in the syntax of
                        ZKCP/Defs.lean, runs to the point mass at its result at the typed oracles
                        read out.

Limits. The condition `FactorsBy (AgreeF m more)` is a premise. This file does not say which
encoding, which oracle, which test.

-/
import Rom.OverOneF
import Run.DetOverOne
import Run.RunIsVProofs

set_option autoImplicit false

namespace Rom

variable {S : OSpec} {lam : ℕ} {α : Type}

theorem det_askFirst (g : Fam (rom lam)) :
    ∀ (n : ℕ) (mr : (Fin lam → Bool) → Bool) (pts : Fin n → List Bool),
      (askFirst lam n mr pts).det g = valFirst g mr pts
  | 0, _, _ => funext fun j => j.elim0
  | n + 1, mr, pts => by
    unfold askFirst
    simp only [OComp.det]
    cases h : mr (g () (pts 0))
    · simp only [OComp.det]
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [valFirst]
      · simp [valFirst, h]
    · simp only [OComp.det_bind, det_askAll, OComp.det]
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [valFirst]
      · simp [valFirst, h]

/-- Over the one oracle, first blocks first: the result is that over `readBlocks m g`. -/
theorem det_overOneF (m : OracleCoding S lam) (more : More S lam) (g : Fam (rom lam)) :
    ∀ c : OComp S α, c.FactorsBy (AgreeF m more) →
      (c.overOneF m more).det g = c.det (readBlocks m g) := by
  intro c
  induction c with
  | pure a => intro _; rfl
  | sample n k ih => exact fun h => ih 0 (h 0)
  | query o q k ih =>
    intro h
    show ((askFirst lam (m.blocks o) (more o q) (m.code o q)).bind fun bs =>
        (k ((m.rng o).symm bs)).overOneF m more).det g = _
    rw [OComp.det_bind, det_askFirst, ih _ (h.2 _), h.1 _ _ (agreeF_first m more g o q)]
    rfl

end Rom

namespace Run
open ZKCP Rom

/-- `run_exit` at the third exit. -/
theorem run_exitF {S : OSpec} {lam : ℕ} {α : Type} (m : OracleCoding S lam) (more : More S lam)
    (f : Oracle lam) (c : Rom.OComp S α) (h : c.NoCoin) (hf : c.FactorsBy (AgreeF m more)) :
    (ofRom (c.overOneF m more)).run f = PMF.pure (c.det (readBlocks m (famOne f))) := by
  rw [ZKCP.OComp.run_of_noCoin f _
        ((run_draws lam α _).2 (drawsNoCoin_ofRom _ (noCoin_overOneF m more c h))),
    det_ofRom, det_overOneF m more _ c hf]

end Run

#print axioms Rom.det_askFirst
#print axioms Rom.det_overOneF
#print axioms Run.run_exitF
