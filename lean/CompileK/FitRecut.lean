-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/FitRecut.lean: `FitK.recut`: under the hypotheses of its statement, the compiler's data
and side conditions (`DataK`, `FitK`, CompileK/Main.lean) are carried through any plan of cuts and
joins of an interface's rounds.

Definitions, statements and proofs; an assembly of what Iop/RecutData.lean, Iop/RecutDraws.lean and
Iop/BatchRecutProofs.lean have for plans.
A plan (`XPlan s`, Iop/Recut.lean) goes through the rounds of a shape s: it keeps the first round,
cuts a first piece off it, or joins it with the second.
Here: any plans XT, XL, XB of the three protocols of an interface L, with the annotation ZB of the
session's cuts. The new data are the kits of the cuts (`Iop.BatchProtocol.RecutKits`: for each piece of a cut
message: it is a string, numberings, serialisers); a plan without cuts has none.

Main names:
  `D.recut hK K : DataK (L.recut XT XL XB ZB hK) lam`: strings, numberings of positions, block
    samplers by the library's rules (a first piece draws no block; a joined round draws no block
    but those of its rounds); padding symbol, announced numbers, depth of the instance tree
    (`depthReq`), parameters, the simulator's index: unchanged.
  `FitK.recut`: FitK D M κ₀ n, `AXPlan.Kinds`, the laws of the annotated cuts (`AXPlan.OK`) and
    "the session's plan fits the format" (`AXPlan.Fit`) give FitK (D.recut hK K) M κ₀ n, with the
    same M, κ₀, n.

Limits: the bounds of the compiler's theorem are read at the
data after the pass: in them the factor κ₀^K has K = the largest number of blocks of a round after
the pass.

Terms: lean/GLOSSARY.md.
-/
import CompileK.KnowRecut
import CompileK.Main
import Iop.RecutData
import Iop.RecutDraws

set_option autoImplicit false

namespace Compile.Batch
open Iop Rom ZKCP Top.Batch Top.ProgDraw
open scoped ENNReal

variable {I X : Type} {L : BatchProtocol I X} {lam : ℕ} {XT : XPlan L.offline.shape} {XL : XPlan L.link.shape}
  {XB : XPlan L.onlineBatch.loc.shape} {ZB : AXPlan XB L.onlineBatch.ann}

/-- The data of the compilation, after the pass. -/
def DataK.recut (D : DataK L lam) (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB)
    (K : L.RecutKits XT XL XB ZB) :
    DataK (L.recut XT XL XB ZB hK) lam where
  pT := D.pT.recutK XT K.T
  pL := D.pL.recutK XL K.Lk
  pB := D.pB.recutK XB K.B
  z := D.z
  no := D.no
  dr := D.dr.recut XT XL XB ZB hK
  ax := D.ax.recut hK K
  p := D.p
  i₀ := D.i₀

/-- Under the hypotheses below, the side conditions are kept. -/
theorem FitK.recut {D : DataK L lam} {M : LH.Nums} {κ₀ : ℝ≥0∞} {n : ℕ} (h : FitK D M κ₀ n)
    (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB) (K : L.RecutKits XT XL XB ZB)
    (hZ : AXPlan.OK XB L.onlineBatch.ann ZB) (hFit : AXPlan.Fit XB L.onlineBatch.ann ZB .first) :
    FitK (D.recut hK K) M κ₀ n where
  one_le := h.one_le
  good := h.good.recut XT XL XB ZB hK
  totLe := h.totLe.recut XT XL XB ZB hK
  opens := h.opens.recut XT XL XB ZB hK
  slots := h.slots
  fmt := (recutFmtB X _ L.onlineBatch XB ZB).1 hZ hK h.fmt hFit
  budget := h.budget

end Compile.Batch
