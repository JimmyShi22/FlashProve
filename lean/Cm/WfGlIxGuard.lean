-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/WfGlIxGuard.lean: guards: some table of scales is lawful, and there is an index.


Theorems. Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as
proofs. A part of a guard against empty theorems.

Main names (in `Cm.WfGl.Guard`):
  `lawful`: some table of scales is lawful (`s.Lawful`; the guard of Cm/TargetPLangs.lean).

  `index`: there is an index (`Nonempty Idx`; the proof's index has all entries 0).








Limits: no index of interest is exhibited; no weights are in sight.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlThird
import Cb.Obj.LdObjectConfMore
import Alg.Mle
import Mathlib.Tactic.Ring
import Cm.TargetPLangs
import Cm.WfGlKeys
import Cm.TargetPLangsProofs
import Cm.IndexRefProofs
import Cb.Obj.LdObjectConfProofs

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.WfGl.Guard
open Inst.Model Inst.Model.All Iop Prob Hiop Cb Blocks.Rng
open Inst.Model.Layout (kRef hRef)

theorem lawful : ∃ s : Scales, s.Lawful := ⟨sRef, target_p_guards.1⟩

theorem index : Nonempty Idx := by
  obtain ⟨s, hs⟩ := lawful
  obtain ⟨i, _⟩ := target_p_guards.2.2.1 s hs
  exact ⟨i⟩

end Cm.WfGl.Guard
