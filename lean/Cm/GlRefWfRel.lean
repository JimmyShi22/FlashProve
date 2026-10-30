-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/GlRefWfRel.lean: the relations' side (cells, the two relations, the honest trace) of a model over
the integer model's indices and instances, as a parameter R (`RelSide`).



Definitions.





Why: a request that is built from a partition is over a configuration of the builder's own: the
model's configuration with five fields replaced: cells (the data as they go out, and the integer
cells), the two relations in the segments' parameters, trace, a fixed value (`cfB`,
Cb/Part/LdPartCf.lean). At the model's own pair the request's record cannot be met (by a reading).
The offline side reads of the model the index's side alone, and of the
relations only "narrow ⊆ wide"
and "a true instance's honest trace is a witness".

Main names:
  `RelSide`: the data. `RelSide.OK`: what the configuration's clause on the model asks of it.
  `RelSide.triv`: cells `Unit`; both relations "True".







Limits: this file does not say anything on a request.



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
import Cb.Gen.WfKeys
import Cb.Gen.LkpAlg
import Cb.Ld.LdLkpMultProofs
import Cb.Obj.LdObjectConfProofs
import Cm.WfGlCount
import Cb.Ld.LdBldPlan
import Cb.Ld.LdBldFoldProofs
import Cb.GlVal.GlJohn
import Cb.Ld.LdBldCode
import Cb.Gen.JohnsonList
import Cb.Ld.LdBldCodeProofs
import Cb.Ld.LdGroupStd
import Cb.Ld.LdKappaTowN
import Cb.Ref.GlRefNum
import Cb.Ld.LdKappaWorkRef
import Cb.Ld.LdKappaList
import Cb.Gl.GlObjMix
import Cb.Ld.LdBldMsgProofs
import Cb.Ld.LdBatShapeProofs
import Cb.Ref.GlRefCodeSplit
import Cb.Gl.GlFinalEvProofs
import Cb.Obj.LdObjectCtb
import Cb.Gen.JohnsonListProofs
import Cb.Ld.LdBldSwOrd
import Cb.Ld.LdBldSwOrdProofs
import Cb.Ld.LdBldCodeGrpProofs
import Cb.Ref.GlRefNumMca
import Cb.Ld.LdLinkClose
import Cb.Ld.LdBldObjProofs
import Cb.Gl.GlFinalPpP
import Cb.Ld.LdBldWfTwo
import Mathlib.Algebra.BigOperators.Fin
import Cb.Ld.LdBldSwBridge
import Cb.Ld.LdBldWfTwoProofs
import Cb.Ld.LdBldWfProofs
import Cb.Ld.LdWfFull
import Cb.Ld.LdBldWfWith
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.WfGlR
open Inst.Model Inst.Model.All Iop Prob Hiop Cb Cb.Gl.Ref Cb.Gl.Bld Cb.Lkp Cb.LdLkp Cm.WfGl
open Inst.Model.Layout (kRef hRef)
open scoped ENNReal

/-- The relations' side of a model over the integer model's indices and instances. -/
structure RelSide : Type 1 where
  Cells  : Type
  Ryes   : Idx → Instance ppref → Cells → Prop
  Rno    : Idx → Instance ppref → Cells → Prop
  trace  : Idx → Instance ppref → Cells
  cells0 : Cells

/-- what the configuration's clause on the model asks of it -/
structure RelSide.OK (R : RelSide) : Prop where
  sub    : ∀ i x w, R.Ryes i x w → R.Rno i x w
  admits : ∀ i x w, R.Ryes i x w → R.Ryes i x (R.trace i x)

/-- cells `Unit`; both relations "True" -/
def RelSide.triv : RelSide := ⟨Unit, fun _ _ _ => True, fun _ _ _ => True, fun _ _ => (), ()⟩

variable (R : RelSide)

end Cm.WfGlR
