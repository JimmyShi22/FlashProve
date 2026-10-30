-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Att/OwnAt.lean: knowledge soundness of an attention sub-proof's own rounds at the value of
Cb/Pv/Att/OwnSteps.lean, without a premise.

Cb/Pv/Att/OwnSteps.lean leaves four equations on the description's sums as the fields of a record
`Means`. They are theorems of Cb/Pv/Att/Mean/: valueMean, scoreMeanG, keyMean and bitSum_meanT.
This file fills the record with them.

Main names:
  `pubOfZ`: challenges of which the lookup's end point alone is set.
  `theMeans E D C kap`: aV is the rule value of the accumulator (`AttSeg.rv` at acc); cV is the
    batch of the reads of the sums of the softmax weights; d1 is minus the identities at2 on the
    cube (g | i) (`scoreIdnG`); d2 is the identities at1 on the cube (k | g | i) (`bitIdnT`).
  `ownAt_knowAt`: `KnowAt` for the chain `(P.own (theMeans ..)).ch`, for all parameters P.
  `ownAt_todo`: what is claimed at the chain's start, with these families.

Limits: those of Cb/Pv/Att/OwnSteps.lean. Nothing is said on an honest prover or on hiding.
-/
import Cb.Pv.Att.OwnSteps
import Cb.Pv.Att.Mean.Turned
import Cb.Pv.Att.Mean.ValueBelow
import Cb.Pv.Att.Mean.Key

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb IOR TWhole Inst.Model

section
variable (E : Type) [Field E] (D : AttSeg.Dim) (C : AttSeg.Calls) (kap : ℕ)

/-- Challenges of which the lookup's end point alone is set. -/
def pubOfZ (z : ℕ → E) : AttSeg.Pub E :=
  ⟨z, 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
    fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- The four equations on the description's sums. -/
def theMeans : Means E D C kap where
  aV := fun z t => AttSeg.rv D C (pubOfZ E z) t .acc
  cV := fun z t => ∑ b ∈ Finset.range D.nb, AttSeg.wp D C z .w3 b *
    AttSeg.rd2 D (AttSeg.yg D C z) (AttSeg.eqT D (AttSeg.yi D C z)) (AttSeg.EF D t b)
  hV := fun p t => valueMean E D C p t
  d1 := fun t b Y => - scoreIdnG D t b Y
  hF := fun p t => by
    have h := scoreMeanG D t C p
    have e : ∀ b, Blocks.ext (D.lg + D.lT) (fun Y => - scoreIdnG D t b Y)
        (AttSeg.cat D.lg p.tg p.ti) =
        - Blocks.ext (D.lg + D.lT) (scoreIdnG D t b) (AttSeg.cat D.lg p.tg p.ti) := fun b => by
      have := Blocks.ext_smul (D.lg + D.lT) (-1 : E) (scoreIdnG D t b) (AttSeg.cat D.lg p.tg p.ti)
      simpa using this
    simp only [e, mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    linear_combination -h
  hD := fun p t => keyMean E D C p t
  d2 := fun t b => bitIdnT D t b
  hH := fun p t => bitSum_meanT D t kap p

end

/-- Knowledge soundness of an attention sub-proof's own rounds at the value, without a premise. -/
theorem ownAt_knowAt {E M X Kc X0 Wp : Type} [Field E] [Fintype E] (P : OwnPar E M X)
    (Ex : ExtSpec) (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0) (Dn : X → M → Prop) :
    KnowAt ((P.own (theMeans E P.D P.C P.kap)).ch.R Ex)
      (jt A0 pr fun x m => Dn x m ∧ (P.own (theMeans E P.D P.C P.kap)).ch.Todo x m)
      (jt A0 (fun e => pr ((P.own (theMeans E P.D P.C P.kap)).ch.back e))
        ((P.own (theMeans E P.D P.C P.kap)).ch.Last Dn))
      (fun _ _ _ wp => wp) ((P.own (theMeans E P.D P.C P.kap)).ch.eps Ex) :=
  ownSteps_knowAt P (theMeans E P.D P.C P.kap) Ex A0 pr Dn

/-- What is claimed at the chain's start. -/
theorem ownAt_todo {E M X : Type} [Field E] [Fintype E] (P : OwnPar E M X) (x : X) (m : M) :
    (P.own (theMeans E P.D P.C P.kap)).ch.Todo x m ↔
    ∃ rM, P.LM (x, []) rM m ∧
      AttSeg.sumPhi P.D P.C (P.pub0 (x, [])) (P.tOf m) .s6b =
        rM (Fin.last _) - P.msg m (P.kM (Fin.last _)) ∧
      ∃ _ : P.uM.T.our.par.Out,
    ∃ rD, P.LD (x, [List.ofFn rM]) rD m ∧
      AttSeg.sumPhi P.D P.C (P.pub0 (x, [List.ofFn rM])) (P.tOf m) .s6d =
        rD (Fin.last _) - P.msg m (P.kD (Fin.last _)) ∧
      ∃ _ : P.uD.T.our.par.Out,
    ∃ rE, P.LE (x, [List.ofFn rM, List.ofFn rD]) rE m ∧
      AttSeg.sumPhi P.D P.C (P.pub0 (x, [List.ofFn rM, List.ofFn rD])) (P.tOf m) .s8 =
        rE P.iZO - P.msg m (P.kE P.iZO) ∧
      ∃ _ : P.sE.T.our.par.Out,
        (AttSeg.rv P.D P.C (pubOfZ E (P.zOf x)) (P.tOf m) .acc =
            rE P.iACC - P.msg m (P.kE P.iACC) ∧
          ∑ b ∈ Finset.range P.D.nb, AttSeg.wp P.D P.C (P.zOf x) .w3 b *
              AttSeg.rd2 P.D (AttSeg.yg P.D P.C (P.zOf x))
                (AttSeg.eqT P.D (AttSeg.yi P.D P.C (P.zOf x))) (AttSeg.EF P.D (P.tOf m) b) =
            rE P.iZC - P.msg m (P.kE P.iZC)) ∧
        (∀ i : Fin P.D.nb, ∀ Y < 2 ^ P.g1, scoreIdnG P.D (P.tOf m) i Y = 0) ∧
        ∀ i : Fin P.D.nb, ∀ Y < 2 ^ P.g2, bitIdnT P.D (P.tOf m) i Y = 0 := by
  rw [OwnPar.own_todo]
  simp only [theMeans, neg_eq_zero]

end Cb.Pv.Att

#print axioms Cb.Pv.Att.ownAt_knowAt
#print axioms Cb.Pv.Att.ownAt_todo
