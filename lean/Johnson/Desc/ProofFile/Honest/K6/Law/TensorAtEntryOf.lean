--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Law/TensorAtEntryOf.lean: WHERE THE VERIFIER's LAYOUT OF THE
WEIGHTS' MATRIX IS LAID AS THE LIBRARY's (WeightsLaid, Honest/K6/Cells/TensorLaid.lean), AT THE FULL
SIZE: THE HEAD's WEIGHTS AS THE HONEST SIDE READS THEM (headTensorOf, Honest/K6/Wit.lean) THROUGH
THE LIBRARY's FIRST READER OF AN INDEX (entryOf, Johnson/HonestTrace/IndexReaders.lean) ARE, INSIDE
THE WIDTH AND THE VOCABULARY, THE OUTPUT MATRIX THAT THE LIBRARY's LAYOUT READS IN THAT INDEX's
MATRIX OF DIGITS. Over the integers. And WeightsLaid is proved at all public files in the goals'
scope at which publicOf returns.

What it is for. A premise "the head's weights off the prover's input are the index's" can be taken
from here where the weights' reader is entryOf at that index.

What it is not. TWO READINGS OF ONE MATRIX AGREE: no news on any model. That a prover's reader of
weights is entryOf at the index of its own input is not said here. Nothing is said beyond the width
(5,120) and the vocabulary (202,048). The full size alone. Nothing on soundness, on completeness or
on what a proof hides.
IT IMPORTS A MODULE UNDER Johnson/Goal/ BY NAME (Meaning/ScopeCore) AND ONE THROUGH WeightsAtHead
(Meaning/EmbScope). It defines nothing.

  valMinAbs_entryOf      inside the matrix's shape, the least residue in absolute value of the
                         reader's entry is the integer entry.
  headTensor_entryOf     the main statement.
  weightsLaid_in_scope   WeightsLaid in scope.
  headTensor_entryOf_in_scope   the main statement in scope.
CALLED: tensor_of_laid (Honest/K6/Cells/TensorLaid.lean); Hof_weightsOf
(Inst/Model/Head/Trace.lean); entryZ_byte (Johnson/HonestTrace/IndexReaders.lean); valMinAbs_cast
(Johnson/HonestTrace/Packed.lean); emb_public_in_scope (Johnson/Goal/Meaning/EmbScope.lean);
last_unit (Honest/K6/Law/FitsOf.lean); public_of_core (Johnson/Meaning/PublicCore.lean);
core_of_scope (Johnson/Goal/Meaning/ScopeCore.lean).
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.WeightsAtHead
import Johnson.HonestTrace.IndexReaders
import Johnson.HonestTrace.Packed
import Johnson.Meaning.PublicCore
import Johnson.Goal.Meaning.ScopeCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6

open OnBytes.Model.Verify (Public publicOf)
open OnBytes.HonestTrace (entryOf entryZ entryZ_byte valMinAbs_cast)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef hRef)
open Inst.Model.Head (oH Hof Hof_weightsOf)

/-- Inside the matrix's shape, the least residue in absolute value of the reader's entry is the
integer entry. -/
theorem valMinAbs_entryOf (i : Cm.Idx) {r c : ℕ} (hr : r < hRef) (hc : c < 2 ^ kRef) :
    (ZMod.valMinAbs (entryOf i r c) : ℤ) = i.mat r c := by
  obtain ⟨b1, b2⟩ := entryZ_byte i hr hc
  have hz : |entryZ i r c| < 2 ^ 60 :=
    abs_lt.2 ⟨by linarith [b1, (by norm_num : (-(2 : ℤ) ^ 60) < -2 ^ 7)],
      by linarith [b2, (by norm_num : ((2 : ℤ) ^ 7) < 2 ^ 60)]⟩
  exact valMinAbs_cast hz

/-- **THE HEAD's WEIGHTS THROUGH THE LIBRARY's FIRST READER OF AN INDEX ARE THE OUTPUT MATRIX THAT
THE LIBRARY READS IN THAT INDEX.** CONDITIONAL: on WeightsLaid and the full size's two numbers;
inside the width and the vocabulary. -/
theorem headTensor_entryOf {X : Public} (L : WeightsLaid X) (hd5 : X.hS.d = 5120)
    (hV2 : X.hS.V = 202048) (i : Cm.Idx) (k v : ℕ) (hk : k < 5120) (hv : v < 202048) :
    headTensorOf X.layers.wsLay ⟨entryOf i⟩ k v =
      (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef i.mat).H k v := by
  have hc : v < 2 ^ kRef := by
    have e : (2 : ℕ) ^ kRef = 262144 := by decide
    omega
  have r1 : oH + k < hRef := by
    have e1 : oH = 3065840 := rfl
    have e2 : hRef = 3076096 := rfl
    omega
  have r2 : oH + (5120 + k) < hRef := by
    have e1 : oH = 3065840 := rfl
    have e2 : hRef = 3076096 := rfl
    omega
  rw [tensor_of_laid L hd5 hV2 ⟨entryOf i⟩ k v hk hv, Hof_weightsOf i.mat hk hv]
  show (ZMod.valMinAbs (entryOf i (oH + k) v) : ℤ) +
      256 * (ZMod.valMinAbs (entryOf i (oH + (5120 + k)) v) : ℤ) =
    i.mat (oH + k) v + 256 * i.mat (oH + 5120 + k) v
  rw [valMinAbs_entryOf i r1 hc, valMinAbs_entryOf i r2 hc, Nat.add_assoc]

/-- **WeightsLaid AT ALL PUBLIC FILES IN THE GOALS' SCOPE AT WHICH publicOf RETURNS.** -/
theorem weightsLaid_in_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : WeightsLaid X := by
  obtain ⟨-, hs, hl, -⟩ := Meaning.Emb.emb_public_in_scope hZ hR h
  obtain ⟨u, hu, h13, -, hg⟩ := last_unit h
  exact ⟨hs, hl, u, hu, h13, hg⟩

/-- **THE SAME IN SCOPE**: at every index, inside the width and the vocabulary. CONDITIONAL: on the
three premises on the public files. -/
theorem headTensor_entryOf_in_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (i : Cm.Idx) (k v : ℕ) (hk : k < 5120)
    (hv : v < 202048) :
    headTensorOf X.layers.wsLay ⟨entryOf i⟩ k v =
      (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef i.mat).H k v :=
  have B := OnBytes.Road.Hd.public_of_core h (OnBytes.Road.Hd.core_of_scope hZ hR h)
  headTensor_entryOf (weightsLaid_in_scope hZ hR h) B.full.d B.full.V i k v hk hv

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.valMinAbs_entryOf
#print axioms ProofFile.Honest.K6.headTensor_entryOf
#print axioms ProofFile.Honest.K6.weightsLaid_in_scope
#print axioms ProofFile.Honest.K6.headTensor_entryOf_in_scope
