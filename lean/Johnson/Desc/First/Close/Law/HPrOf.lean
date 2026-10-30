-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/HPrOf.lean (kind K10): THE FIELD hPr OF `K10Heavy` (K10Heavy.lean beside this file): «the kind's number of row variables is the typed stage's h + g»: FROM «it is the group in front's k», WHICH `AtMgA.K10HeavyAll` (Johnson/P5J/K10SeatedOfHeavy.lean) BEARS BESIDE `K10Heavy` (Q.k = gs.k).
A theorem: one call of `stage_k` (StageClosed.lean beside this file).

What is said. `hPr_of`: gs ∈ frontFull · Pr.k = gs.k ⊢ Pr.k = (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).s.h + (the same).s.g: THE FIELD's TEXT. General in cs, lo, kb.

Limits. gs ∈ frontFull is K10Heavy's own field hgs. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.StageClosed
import Johnson.Desc.First.Close.Law.CubeOfShapes
import Johnson.Desc.First.Close.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G Cb

/-- **THE FIELD hPr.** -/
theorem hPr_of (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ)) (gs : GroupSize)
    (hgs : gs ∈ frontFull) (kb : Fin lo.length → Bool)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 →
      cMain cs (lo.get i).1 = (stageOf gs 219).C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 →
      cMask cs (lo.get i).1 = (stageOf gs 219).Z) (Pr : Par) (hQ : Pr.k = gs.k) :
    Pr.k = (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).s.h +
      (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).s.g := by
  show Pr.k = (stageOf gs 219).h + (stageOf gs 219).g
  rw [stage_k gs hgs]
  exact hQ

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.hPr_of
