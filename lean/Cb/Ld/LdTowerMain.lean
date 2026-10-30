-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdTowerMain.lean: the proofs of the six statements of Cb/Ld/LdTower.lean that rest on the two
blocks' own theorems.

Cb/Ld/LdTower.lean puts a proximity test beyond unique decoding together from folds, code switches
and an end block (the base case is one). Cb/Ld/LdTowerProofs.lean proves each of the six from
`Spec.ldSwitch_goodT` or `Spec.ldBase_good` as a hypothesis; here these are put in
(Cb/Ld/LdSwitchTop.lean: `ldSwitch_goodT`; Cb/Ld/LdBaseProofs.lean: `ldBase_good`). Nothing is
defined here.

Main names, each under the hypotheses of its statement (Cb/Ld/LdTower.lean):
  `ldTower_switch`: under `D.Hyp e' L t'`, P and P' not empty, the code switch is a piece: from at
    most t' long positions of the new word to at most D.t of the input word.
  `ldTower_base`: under `a.BaseHyp d bad L2`, the base case is a tail: at most t long positions of
    the input word.
  `ldTower_stage`: fold, then code switch, as one block.
  `ldTower_tail`: under `T.OK`, a tower is a tail of a chain.
  `ldTower_end`: what the whole test has: see the row of `Spec.ldTower_end` in the head of
    Cb/Ld/LdTower.lean.
  `ldTower_run`: under `R.OK t'`, a run is a piece of a chain.
  Each proves the statement `Spec.` of its name.

Limits: the fold remains a parameter of a stage, a tower and a run (any block F with F.OK t t,
t = `D.t` of the stage's switch). So do the end block of a tower (any `Z` with `Z.OK t`) and the
last block of a run.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdTowerProofs
import Cb.Ld.LdSwitchTop
import Cb.Ld.LdBaseProofs

set_option autoImplicit false

namespace Cb

theorem ldTower_switch : Spec.ldTower_switch := ldTower_switch_of ldSwitch_goodT
theorem ldTower_base : Spec.ldTower_base := ldTower_base_of ldBase_good
theorem ldTower_stage : Spec.ldTower_stage := ldTower_stage_of ldSwitch_goodT
theorem ldTower_tail : Spec.ldTower_tail := ldTower_tail_of ldSwitch_goodT
theorem ldTower_end : Spec.ldTower_end := ldTower_end_of ldSwitch_goodT
theorem ldTower_run : Spec.ldTower_run := ldTower_run_of ldSwitch_goodT

end Cb
