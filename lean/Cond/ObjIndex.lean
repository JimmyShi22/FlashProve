-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cond/ObjIndex.lean: the hypothesis `IdxBelow` of CompileK/WideIndex.lean, from the lists of an object
with records (`Nums.IdxBelow`, `IdxBelowG`, `IdxBelowO`).

Definitions, statements and proofs.

Limits: this file says nothing on numerals.

Terms: lean/GLOSSARY.md.
-/
import Cond.ObjBitsProof
import CompileK.WideIndex

set_option autoImplicit false

namespace Hiop
open Iop
open scoped ENNReal

namespace SubsR
variable {C : ConfigurationWithOutOfDomainSample} {S : SubsR C}

/-- Every round of weights-formedness, of the offline test and of the link has error, as a
probability, at most c₀. These errors are numbers that `P` lists: the head. -/
structure Nums.IdxBelow (P : S.Nums) (c₀ : ℝ≥0∞) : Prop where
  wf     : Err.Below P.wf.err c₀
  linOff : Err.Below P.linOff.err c₀
  link   : Err.Below P.link.err c₀

/-- The same, counting the proof-of-work bits of these rounds. -/
structure Nums.IdxBelowG (P : S.Nums) (g : S.Bits) (c₀ : ℝ≥0∞) : Prop where
  wf     : Err.BelowG g.wf P.wf.err c₀
  linOff : Err.BelowG g.linOff P.linOff.err c₀
  link   : Err.BelowG g.link P.link.err c₀

def Nums.IdxBelowO {Nn : Type} (P : S.Nums) (c₀ : ℝ≥0∞) : Option (S.Wk Nn) → Prop
  | none => P.IdxBelow c₀
  | some w => P.IdxBelowG w.g c₀

end SubsR
end Hiop

noncomputable section

namespace TopC
open Iop Rom ZKCP Compile Compile.Batch Top.Batch Top.ProgDraw Hiop
open scoped ENNReal

namespace Spec

/-- States what "the index decoder answers" says at the target: the relaxed relation of
weights-formedness (`C.RwfR`, Hiop/RecConf.lean) holds of (record, word). -/
def target_index_wf : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (r : C.Rec) (y : (oneExternalString (S.obj r).wordLength (S.obj r).Symbol).Str) (i : C.I),
    (S.obj r).decodeIndex y = some i → C.RwfR (r, y) ()

end Spec

/-- The hypothesis `IdxBelow` of CompileK/WideIndex.lean, from the three lists. -/
theorem target_idxBelow {Nn : Type} {C : ConfigurationWithOutOfDomainSample} {S : SubsR C} (P : S.Nums) (r : C.Rec) (c₀ : ℝ≥0∞) :
    ∀ o : Option (S.Wk Nn), P.IdxBelowO c₀ o → IdxBelow (P.errT r) (P.errL r) c₀ (SubsR.wkAt r o)
  | none, h =>
    ⟨Err.Below.app (SubsR.Nums.IdxBelow.wf h) (SubsR.Nums.IdxBelow.linOff h),
      SubsR.Nums.IdxBelow.link h⟩
  | some w, h =>
    ⟨(belowG_app _ _ w.g.wf w.g.linOff P.wf.err P.linOff.err c₀).2
        ⟨SubsR.Nums.IdxBelowG.wf h, SubsR.Nums.IdxBelowG.linOff h⟩,
      SubsR.Nums.IdxBelowG.link h⟩

theorem target_index_wf : Spec.target_index_wf := by
  intro C S r y i h
  have h' : C.D y r = some i := h
  show (C.D y r).isSome
  rw [h']
  rfl

end TopC
