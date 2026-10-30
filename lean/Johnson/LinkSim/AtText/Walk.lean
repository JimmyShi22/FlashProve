-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/Walk.lean: at one switch, under the premises AtSwitch, the shift of the
coins is the same whether it is computed along the honest run or along the other run.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. The pieces of the shift (Johnson/LinkSim/AtText/ShiftDefs.lean) read three
things of the run along which they are computed: the fold's point, the verifier's states and one
number (sBits, ShiftDefs.lean). Step.lean proves that these are the same at both runs. So, under
AtSwitch (Step.lean), each piece computed at the other run's coins, state and columns (Ks, Ps, cols)
equals the piece computed at the honest run's (Kr, Pr, colr):
  walk_dMu, walk_dTl, walk_sBits, walk_shFr, walk_dTab, walk_tNext, walk_shWAt, walk_dFresh,
  walk_shNew, walk_dNext   one equation each, for the piece that the name carries.
Each statement is an equation between the two runs.

How it fits. Induct.lean uses these lemmas once per stage to prove Spec.walkSame (SpecStage.lean):
along all stages, the shift computed along the other run is the shift computed along the honest
run. That is what lets the shift be recovered from the shifted coins.

Limits.
  - These lemmas are about one switch.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.Step

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)
open Johnson.Prover.Link

variable {p : P12} {last : Bool} {j : ℕ} {cur next : Fmt.M1.Stage} {l : Laid} {o : ℕ} {t : T12}
  {Kr Ks : BCoins} {Pr Ps d : PS} {colr cols : ℕ → List UInt64} {D : ℕ → Fmt.Drawn}

/-- The folded messages of d are the same along both runs. -/
theorem walk_dMu (h : AtSwitch p last j cur next l o t Kr Ks Pr Ps d colr cols D) :
    dMu Ks j cur o t Ps D d = dMu Kr j cur o t Pr D d := by
  unfold dMu
  rw [sGam_same h]

/-- The folded tails of d are the same along both runs. -/
theorem walk_dTl (h : AtSwitch p last j cur next l o t Kr Ks Pr Ps d colr cols D) :
    dTl Ks j cur o t Ps D d = dTl Kr j cur o t Pr D d := by
  unfold dTl
  rw [sGam_same h]

/-- The number sBits is the same along both runs. -/
theorem walk_sBits (h : AtSwitch p last j cur next l o t Kr Ks Pr Ps d colr cols D) :
    sBits p Ks j cur next l o t Ps D = sBits p Kr j cur next l o t Pr D := by
  unfold sBits
  rw [sT1_same h]

/-- The shift of the free entries of the new mask table is the same along both runs. -/
theorem walk_shFr (h : AtSwitch p last j cur next l o t Kr Ks Pr Ps d colr cols D) :
    shFr p Ks j cur next l o t Ps D d = shFr p Kr j cur next l o t Pr D d := by
  unfold shFr
  rw [walk_dMu h, walk_dTl h, walk_sBits h]

/-- The next difference's two tables are the same along both runs. -/
theorem walk_dTab (h : AtSwitch p last j cur next l o t Kr Ks Pr Ps d colr cols D) :
    dTab p Ks j cur next l o t Ps D d = dTab p Kr j cur next l o t Pr D d := by
  unfold dTab
  rw [walk_shFr h, sGam_same h]

/-- The verifier's state in front of the next stage is the same along both runs. -/
theorem walk_tNext (h : AtSwitch p last j cur next l o t Kr Ks Pr Ps d colr cols D) :
    tNext p Ks last j cur next l o t Ps cols D = tNext p Kr last j cur next l o t Pr colr D :=
  (sT3_same h).symm

/-- The shift of the next fold's coefficients is the same along both runs. -/
theorem walk_shWAt (h : AtSwitch p last j cur next l o t Kr Ks Pr Ps d colr cols D) (σ : Sg) :
    shWAt p Ks last j cur next l o t Ps cols D d σ =
      shWAt p Kr last j cur next l o t Pr colr D d σ := by
  unfold shWAt
  rw [walk_tNext h, walk_dTab h]

/-- The next difference's further table is the same along both runs. -/
theorem walk_dFresh (h : AtSwitch p last j cur next l o t Kr Ks Pr Ps d colr cols D) :
    dFresh p Ks last j cur next l o t Ps cols D d =
      dFresh p Kr last j cur next l o t Pr colr D d := by
  funext b i
  unfold dFresh
  rw [walk_shWAt h]

/-- The shift of the switch's new coins is the same along both runs. -/
theorem walk_shNew (h : AtSwitch p last j cur next l o t Kr Ks Pr Ps d colr cols D) :
    shNew p Ks last j cur next l o t Ps cols D d =
      shNew p Kr last j cur next l o t Pr colr D d := by
  unfold shNew
  rw [walk_dTab h, walk_dFresh h]

/-- The next difference is the same along both runs. -/
theorem walk_dNext (h : AtSwitch p last j cur next l o t Kr Ks Pr Ps d colr cols D) :
    dNext p Ks last j cur next l o t Ps cols D d =
      dNext p Kr last j cur next l o t Pr colr D d := by
  unfold dNext
  rw [walk_shNew h, walk_dTab h, walk_dFresh h]

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.walk_shFr
#print axioms OnBytes.LinkSim.AtText.walk_shNew
#print axioms OnBytes.LinkSim.AtText.walk_dNext
