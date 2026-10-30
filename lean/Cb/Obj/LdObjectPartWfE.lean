-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPartWfE.lean: the first part of an object (weights-formedness) from the record "all
data" (`LdWfE`) of Cb/Ld/LdWfEnd.lean.

The object (`LdObj`, Cb/Obj/LdObject.lean) is one record with a configuration and, over it, the
sub-protocols of the proof system, as five terms. Cb/Obj/LdObjectParts.lean cuts the record `LdObjP`
(Cb/Obj/LdObjectPlan.lean), from which an object is made, and its hypotheses into five parts. The
first is for weights-formedness, the relation `ConfigurationWithOutOfDomainSample.Rwf` (Hiop/RecConf.lean): the oracle is the
encoding of a message that holds an index of the index set, and the record (`ConfigurationWithOutOfDomainSample.Rec`) is the one
kept with that message and has its answers (`ConfigurationWithOutOfDomainSample.Enc`).
A definition, one theorem. Generic; no protocol is given.
Cb/Obj/LdObjectParts.lean asks of the first part a record `PWf` (the data of the preamble and of the
test that follows; the blocks) and a bundle `A.Hyp`. Cb/Ld/LdWfEnd.lean has weights-formedness as
one record of data `Zw : LdWfE F E` with conditions `Zw.OK p L`: on data, and six on the sender.
Here the one is made from the other, so that a toy given as an `LdWfE` can be put into the frame of
Cb/Obj/LdObjectParts.lean.

Main names:
  `pWfE_hyp`: for E of characteristic p (`CharP E p`) and `Nonempty (Fin Zw.W.Cf.C₀.n)`:
    `Zw.OK p L`, and every place of the layout `Zw.W.lay` of the test that follows is a place of the
    configuration's (`hl`) ⇒ `(PWf.ofE Zw).Hyp`, and `Zw.W.Cf.OK L`.

Limits: this file does not say that `Zw.OK` can be met.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectData
import Cb.Obj.LdObjectParts
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The first part, from all data of weights-formedness. -/
@[reducible] def PWf.ofE {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] (Zw : LdWfE F E) [ne : Nonempty (Fin Zw.W.Cf.C₀.n)] : PWf F E :=
  { W := Zw.W, ne := ne, Bw := Zw.G.B }

theorem pWfE_hyp {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (p : ℕ)
    [CharP E p] (Zw : LdWfE F E) [Nonempty (Fin Zw.W.Cf.C₀.n)] (L : ℕ) (h : Zw.OK p L)
    (hl : ∀ a, ∃ l, Zw.W.lay a = Zw.W.Cf.lay l) :
    (PWf.ofE Zw).Hyp ∧ Zw.W.Cf.OK L := by
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := ldObjZ_wf p Zw L h ⟨Zw.W, Zw.G.B⟩ rfl
  exact ⟨⟨hl, w2, w3, w4, w5, w6⟩, w1⟩

end Cb
