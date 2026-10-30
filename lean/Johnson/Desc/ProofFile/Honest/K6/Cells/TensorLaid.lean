-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Cells/TensorLaid.lean: the head's weight that the honest side of
the sub-protocol "the output head's own rounds" (K6) reads off the reader of the committed digits
(`headTensorOf`, Honest/K6/Wit.lean) is two entries of that reader, at the library's own rows. One
structure of premises and two lemmas. No goal is stated.

WHAT IT IS NOT. TWO LAYOUTS OF ONE MATRIX ARE HELD AGAINST EACH OTHER: nothing on what the reader's
entries are. CONDITIONAL: `tensor_of_laid` on `WeightsLaid` X, a structure of premises on public
data alone (five facts in three fields), and on the full size's two numbers (hd5, hV2): to meet that
structure is no property of the protocol, and THAT ANY PUBLIC PART MEETS IT IS NOT SHOWN HERE. The
reader w is a letter. No frame, no thread, no scope, no run. `place_uH` is a closed fact on the
library's reference parameters.

  `place_uH`        the library's place of digit jj of the output matrix's entry (v, k): row oH +
                    (5120 jj + k), column v
  `WeightsLaid`     FIVE FACTS ON THE PUBLIC PART's LAYOUT OF THE COMMITTED WEIGHTS, as one
                    structure: sized, laid, unit
  `tensor_of_laid`  **headTensorOf X.layers.wsLay w k v = the entry at row oH + k plus 256 times the
                    entry at row oH + (5120 + k), each as the integer of least absolute value**, at
                    k < 5120 and v < 202048

WHO MIGHT PAY THE STRUCTURE. sized and laid: the second and third parts of the library's
`emb_public_in_scope` (Johnson/Goal/Meaning/EmbScope.lean), in scope; unit: `last_unit`
(Honest/K6/Law/FitsOf.lean), from `publicOf`'s return alone, without its clause on the number of
digits. Neither is called or imported here. HOW IT GOES. `layout_eq`
(Johnson/Road/FormsKeysWLay.lean) at unit number 385 (`units_head`, Johnson/Road/HeadWeight.lean)
gives the unit's two digits and its cell's place; the last unit is number 385 by the layout's size;
the two groups' names and sizes make the index [v, k]. `place_uH` is the lines "hp" inside the
proofs of `Hof_weightsOf` (Inst/Model/Head/Trace.lean) and `entryW_Hof`
(Johnson/Road/HeadWeight.lean), which are no lemma there.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K6.Wit
import Johnson.Road.HeadWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes.Model (wsLayOf)
open OnBytes.Model.Verify (Public weightShape)
open OnBytes.Road (SizedW)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef units uH place)
open Inst.Model.Head (oH)

/-- The library's place of digit jj of the output matrix's entry (v, k): the lines "hp" inside the
proofs of `Hof_weightsOf` (Inst/Model/Head/Trace.lean) and `entryW_Hof`
(Johnson/Road/HeadWeight.lean), which are no lemma there. -/
theorem place_uH (jj v k : Nat) :
    place kRef (units ppref) 385 (uH ppref) jj [v, k] = (oH + (5120 * jj + k), v) := by
  simp only [place, Inst.Model.Head.oH_eq, Inst.Model.Head.bits_uH]
  simp [uH, Inst.Model.Layout.row, Inst.Model.Layout.col, Inst.Model.Layout.split,
    Inst.Model.Layout.lOf, ppref]
  omega

/-- **FIVE FACTS ON THE PUBLIC PART's LAYOUT OF THE COMMITTED WEIGHTS**: the shape of the weights
agrees with the library's reference parameters; the layout is what the verifier's own function
returns on that shape, at the switch true and the library's number of column bits; its last unit is
of kind 13, with the groups "x" over the vocabulary and "kk" over the coordinates, in this order. A
definition: a premise's form. Nothing is claimed of it. On public data alone. -/
structure WeightsLaid (X : Public) : Prop where
  sized : SizedW (weightShape X.P X.y) ppref
  laid : wsLayOf (weightShape X.P X.y) true kRef = .ok X.layers.wsLay
  unit : ∃ u, X.layers.wsLay.U.back? = some u ∧ u.X = 13 ∧
    u.g.map (fun g => (g.name, g.R)) = [("x", X.hS.V), ("kk", X.hS.d)]

/-- **THE HEAD's WEIGHT OFF THE READER OF THE COMMITTED DIGITS IS TWO ENTRIES OF THAT READER, AT THE
LIBRARY's OWN ROWS**: under `WeightsLaid` and the full size's two numbers. No frame, no thread, no
scope. -/
theorem tensor_of_laid {X : Public} (L : WeightsLaid X) (hd5 : X.hS.d = 5120)
    (hV2 : X.hS.V = 202048) (w : Weights) (k v : Nat) (hk : k < 5120) (hv : v < 202048) :
    headTensorOf X.layers.wsLay w k v =
      (ZMod.valMinAbs (w.entry (oH + k) v) : Int) +
        256 * (ZMod.valMinAbs (w.entry (oH + (5120 + k)) v) : Int) := by
  obtain ⟨Zs, hws, u, hu, h13, hg⟩ := L
  obtain ⟨-, hsz, -, hall⟩ := OnBytes.Road.layout_eq Zs hws
  obtain ⟨u', hu', -, hn, -, -, -, -, -, hcell⟩ := hall 385 (uH ppref) OnBytes.Road.Hd.units_head.2
  have hsz' : X.layers.wsLay.U.size = 386 := hsz.trans OnBytes.Road.Hd.units_head.1
  have hb : X.layers.wsLay.U.back? = X.layers.wsLay.U[385]? := by
    show X.layers.wsLay.U[X.layers.wsLay.U.size - 1]? = _
    rw [hsz']
  obtain rfl : u' = u := by
    rw [hb, hu'] at hu
    exact Option.some.inj hu
  rw [hd5, hV2] at hg
  obtain ⟨g1, r1, e1, p1, q1⟩ := List.map_eq_cons_iff.1 hg
  obtain ⟨g2, r2, e2, p2, q2⟩ := List.map_eq_cons_iff.1 q1
  obtain rfl := List.map_eq_nil_iff.1 q2
  subst e2
  have n1 : g1.name = "x" := congrArg Prod.fst p1
  have R1 : g1.R = 202048 := congrArg Prod.snd p1
  have n2 : g2.name = "kk" := congrArg Prod.fst p2
  have R2 : g2.R = 5120 := congrArg Prod.snd p2
  have hidx : headWeightIdx u' k v = [v, k] := by
    unfold headWeightIdx
    rw [e1]
    simp [n1, n2]
  have hin : headWeightIn u' k v = true := by
    unfold headWeightIn
    rw [e1]
    simp [n1, n2, R1, R2, hk, hv]
  have hn2 : u'.nlw = 2 := hn
  unfold headTensorOf
  rw [hu]
  simp only [h13, hin, beq_self_eq_true, Bool.and_self, if_true, hidx, hcell, place_uH, hn2]
  simp [VerifiableInference.Desc.Kinds.Head.Law.sumZ, List.range_succ]

#print axioms place_uH
#print axioms tensor_of_laid

end ProofFile.Honest.K6
