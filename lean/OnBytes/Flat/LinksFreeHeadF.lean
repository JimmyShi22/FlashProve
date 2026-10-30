-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksFreeHeadF.lean: the tests of the verifier's own walk (`Head.selfTests`,
OnBytes/Model/Head.lean) at two requests: `SelfTestsFree` (OnBytes/Flat/LinksFreeHead.lean), from
one statement by name.

Main definition: `CoefficientsFree`: of `HTailF2.coefficientsF`, which sets the weights of the
virtual rows on the rows of their arrays and never the weights L. Main theorem: `selfTestsFree_of`.

Not claimed: `CoefficientsFree` (OnBytes/Flat/LinksFreeCoef.lean shows it). Nothing on a run on a
view. For proofs only; no module of the program imports this file.


-/
import OnBytes.Flat.LinksFreeHeadE

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model OnBytes.Model.Head

/-! ## The tests of the verifier's own walk -/

/-- Of the routine that sets the weights of the virtual rows on the rows of their arrays. -/
def CoefficientsFree : Prop :=
  ∀ (tl : HTailF2) (f' : Array HFun),
    cmpA.Rel Eq tl.coefficientsF (HTailF2.coefficientsF { tl with funs := f' })

theorem selfTestsFree_of (hC : CoefficientsFree) : SelfTestsFree := by
  intro R R' tl tl' wo wo' hR htl hwo
  have hf : FunsAlike R.t.funs R'.t.funs := hR.2.2.2.2
  obtain ⟨cov', w1, f', rfl⟩ := hR.open
  dsimp only at htl hf
  obtain ⟨h1, rfl⟩ := htl
  unfold selfTests
  dsimp only
  refine cmpLA.bind' (by keeps) fork_rel fun F F' hF => ?_
  obtain ⟨e, -⟩ := hF
  generalize F'.trees = T' at e
  generalize F'.c0 = c' at e
  subst e
  dsimp only
  have e1 : tl.funsHeld R.t.funs = tl.funClosed := by rw [← h1]; exact funsHeld_self tl
  have e2 : HTailF2.funsHeld { tl with funs := f' } f' = tl.funClosed :=
    funsHeld_self { tl with funs := f' }
  have e3 : wo'.sFv = wo.sFv := by rw [← hwo.1]
  rw [e1, e2, e3]
  iterate 5 (refine cmpLA_same (by resp) fun _ => ?_)
  refine cmpLA.bind' (by keeps) (liftS_cmpLA (by keeps) (selfTestF_rel tl f' _)) fun _ _ _ => ?_
  refine cmpLA.bind' (by keeps) (liftS_cmpLA (by keeps) (hC tl f')) fun _ _ _ => ?_
  exact liftS_cmpLA (by keeps) (tileSelfTestF_rel tl (h1 ▸ hf))

end OnBytes.Flat
