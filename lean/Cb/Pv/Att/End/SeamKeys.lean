-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/SeamKeys.lean: what the chain of an attention sub-proof's own rounds claims at its
start gives the join at the calls' vectors of looked-up values.

Statement and proof. att_seam (Cb/Pv/Att/End/Seam.lean) ends at the join with the key forms at the
rule values. kfExt (Inst/Model/Att/KeyFormsExt/All.lean) says that a key form at the rule values is
the multilinear extension of its call's vector of looked-up values at the call's key point.

Main name:
  att_seam_keys: the chain's claim at its start gives: the identities of the own rounds (OwnM); the
    join, with the extension of keyVec D tb t c at zC c z in the place of key form c, t the cells of
    m and z the lookup's end point; and that the test of the denominators has the value 0.

Limits: it stands under kfExt's three hypotheses on sizes. The letters of the join (alpha, theta,
the calls' weights, the padding trees' term, the hidden value at the end of the key side) are the
lookup's. Nothing on an honest prover or on hiding.


-/
import Cb.Pv.Att.End.Seam
import Inst.Model.Att.KeyFormsExt.All

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open Finset Blocks
open Inst.Model Inst.Model.AttSeg

section Own
variable {E M X : Type} [Field E] [Fintype E] {P : OwnPar E M X}

/-- The chain's claim at its start gives the join at the calls' vectors of looked-up values. -/
theorem att_seam_keys (Q : JoinLay P) (tb : Tables) (hn : P.npl = 2) (hK : P.D.lT ≤ 2 ^ P.kap)
    (hC : Calls.OK (scl := Q.scl) P.C P.D) (hdeep : ∀ u : Inst.Model.AttSeg.Fam, u.l P.D ≤ P.C.Dk)
    (hs : P.C.a 0 = P.C.a 1)
    (hLM : ∀ x r m, P.LM x r m ↔ LMat P x r m) (hLD : ∀ x r m, P.LD x r m ↔ LDat P x r m)
    (hLE : ∀ x r m, P.LE x r m ↔ LEat P Q x r m) (x : X) (m : M)
    (h : (P.own (theMeans E P.D P.C P.kap)).ch.Todo x m) :
    OwnM P m ∧
      joinVal (Q.q x)
        (fun c => Blocks.ext (P.C.a c) (keyVec (scl := Q.scl) P.D tb (P.tOf m) c)
          (P.C.zC c (P.zOf x))) ((Q.ce x).val (P.msg m)) = 0 ∧
      denOut P.D P.C (P.zOf x) (P.tOf m) = 0 := by
  obtain ⟨h1, h2, h3⟩ := att_seam Q hn hK hLM hLD hLE x m h
  refine ⟨h1, ?_, h3⟩
  have e : (fun c => Blocks.ext (P.C.a c) (keyVec (scl := Q.scl) P.D tb (P.tOf m) c)
      (P.C.zC c (P.zOf x))) =
      KF (scl := Q.scl) P.D P.C (pubOfZ E (P.zOf x))
        (rv P.D P.C (pubOfZ E (P.zOf x)) (P.tOf m)) :=
    funext fun c => (KeyFormsExt.kfExt (scl := Q.scl) P.D P.C tb (pubOfZ E (P.zOf x)) (P.tOf m)
      hC hdeep hs c).symm
  rw [e]
  exact h2

end Own

end Cb.Pv.Att.End

#print axioms Cb.Pv.Att.End.att_seam_keys
