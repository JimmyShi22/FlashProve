-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectReqEndProofs.lean: the proofs of the statements of Cb/Obj/LdObjectReqEnd.lean.

Main names (statements and hypotheses: Cb/Obj/LdObjectReqEnd.lean):
  `ldORE_holds`: under `R.Tie`, what the final batching leaves holds if and only if `R.O.holds`.
The mathematics is that of Cb/Obj/LdObjectWfKit.lean (a tensor row written in two ways); the moves'
hypotheses are those of Cb/Req1/LdSegRefTenProofs.lean; the last step is by `ldStepF_hyp`
(Cb/Req1/LdSegCloseProofs.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectReqEnd
import Cb.Req1.LdSegRefTenProofs
import Cb.Req1.LdSegFrontProofs
import Cb.Ld.LdBattProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain Cb.RngPk

section
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The mask terms do not read the entries of the matrix. -/
theorem LdORE.maskPart_msg (R : LdORE F E Kc) (cl : R.X.bt.par.Mid)
    (U : R.Cf.conf.Msg) (m : R.S.Msg) :
    R.X.bt.maskPart cl (R.X.msg (U, m)) =
      R.X.bt.maskPart cl (Sum.elim (fun _ => 0) (R.S.ents m)) := by
  unfold BattPar.maskPart
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  cases j with
  | inl j =>
      show (0 : E) * _ = (0 : E) * _
      rw [zero_mul, zero_mul]
  | inr j => rfl

end

theorem ldORE_holds (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldORE_holds F E Kc := by
  intro R hT cl rec U m
  have hten : R.X.bt.ten (R.X.bt.rowVec cl) (R.X.bt.outPt cl) (R.X.msg (U, m)) =
      ∑ y, ∑ c, R.X.bt.rowVec cl y * Alg.eqk (R.O.D.pt (R.O.ψ cl)) c * R.O.D.mat (R.Cf.upM U) y c :=
    ldOWk_ten R.Rw (Fin R.k) (Fin R.Cf.X.v) (Fin R.klo) R.e (R.X.bt.rowVec cl) (R.mat U)
      (R.O.D.mat (R.Cf.upM U)) (R.X.bt.outPt cl) (hT U)
  have hA : cl.eps * R.X.bt.ten (R.X.bt.rowVec cl) (R.X.bt.outPt cl) (R.X.msg (U, m)) =
      ∑ y, ∑ c, R.O.g cl y * Alg.eqk (R.O.D.pt (R.O.ψ cl)) c * R.O.D.mat (R.Cf.upM U) y c := by
    rw [hten, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    show _ = cl.eps * R.X.bt.rowVec cl y * _ * _
    ring
  have hrow : R.X.bt.RowHolds cl (R.X.msg (U, m)) ↔
      R.O.D.Claim (R.Cf.upM U) (R.O.g cl) (R.O.ψ cl) (R.O.restM cl m) (R.O.τ cl) := by
    show cl.eps * R.X.bt.ten (R.X.bt.rowVec cl) (R.X.bt.outPt cl) (R.X.msg (U, m)) + _ + _ =
        cl.fin ↔
      _ + R.X.bt.maskPart cl (Sum.elim (fun _ => 0) (R.S.ents m)) = cl.fin
    rw [hA, ← R.maskPart_msg cl U m, add_assoc]
    rfl
  exact and_congr hrow Iff.rfl

section
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The hypotheses of the last step `R.endStep`, under `hn` and `hT`. -/
theorem LdORE.endStep_hyp (R : LdORE F E Kc) (hn : 1 ≤ R.n) (hT : R.Tie) : R.endStep.Hyp := by
  refine ldStepF_hyp R.S R.X.m1.A R.bEnd _ ?_ ?_ ?_ ?_
  · rintro z y w ⟨hE, ⟨hr, -⟩, hM⟩
    exact ⟨hE, (ldORE_holds F E Kc R hT z _ _ _).1 ⟨(batt_row E R.X.bt hn z _).1 hM, hr⟩⟩
  · intro z y h
    exact h.1
  · intro w
    rfl
  · rintro z y w _ ⟨U, hU, hh⟩
    obtain ⟨h1, h2⟩ := (ldORE_holds F E Kc R hT z _ _ _).2 hh
    exact ⟨U, hU, ⟨h2, trivial⟩, (batt_row E R.X.bt hn z _).2 h1⟩

end

theorem ldORE_hyp (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldORE_hyp F E Kc := by
  intro R hn hZ hT
  unfold LdORE.lastP
  rw [LdProg.hyp_snoc, LdProg.hyp_snoc, LdProg.hyp_snoc]
  exact ⟨⟨⟨LdProg.hyp_nilK _, R.X.stepIn_hyp⟩,
      (allB_one R.X.link).2 (ldSeg_lift E Kc R.X.m0 _ _ _ R.X.m1.A _ _ _ _ (R.X.goodAt hn hZ)).1⟩,
    R.endStep_hyp (le_trans (by norm_num) hn) hT⟩

theorem ldORE_zk (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldORE_zk F E Kc := by
  intro R base hn hZ hO hf
  unfold LdORE.lastP
  rw [LdProg.zk_snoc, LdProg.zk_snoc, LdProg.zk_snoc, LdProg.after_snoc, LdProg.after_nil]
  refine ⟨⟨⟨(LdProg.zk_nil _ _).2 trivial, ?_⟩, ?_⟩, ldStepF_zk _ _ _ _ _⟩
  · unfold LdTenD.stepIn
    rw [LdMv.Zk]
    trivial
  · rw [LdMv.Zk]
    exact (okGiven_one R.X.link _).2 (Or.inr ⟨R.X.mask, ldSegRef_tn_goodM E Kc R.X hn hZ hO, hf⟩)

theorem ldORE_more (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldORE_more F E Kc :=
  fun _ _ _ => Iff.rfl

theorem ldORE_kinds (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldORE_kinds F E Kc := by
  intro R
  obtain ⟨_, _, _, _, _, hp⟩ := ldSeg_rounds E Kc
  have a1 := hp R.X.src R.X.m0 (sideF R.X.S fun x => (x.2.1, (x.1, x.2.2)))
    (sideG R.X.S (ExtMap.id R.X.C.E0))
    (sideM R.X.S (fun x => (x.2.1, (x.1, x.2.2))) fun _ w => w.2) (sideB R.X.S fun _ w => w.2)
  obtain ⟨e1, -, e3, e4⟩ := ldStepF_nums R.S R.X.m1.A R.bEnd fun z => (z, R.recOf z)
  have c2 : (LdMv.sub R.X.m0 R.X.m1 (.one R.X.link)).chain = .one R.X.link := by rw [LdMv.chain]
  have l2 : R.X.link.R.shape.nAll = R.k + 2 := batt_len E R.X.bt R.X.C.E0
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold LdORE.lastP
    rw [LdProg.all_snoc, LdProg.all_snoc, LdProg.all_snoc]
    exact ⟨⟨⟨LdProg.all_nilK _ _, Or.inr rfl⟩, Or.inl rfl⟩, Or.inr rfl⟩
  · unfold LdORE.lastP LdTenD.stepIn
    rw [LdProg.nAll_snoc, LdProg.nAll_snoc, LdProg.nAll_snoc, LdProg.nAll_nil, a1.1, c2, nAll_one,
      l2, show R.endStep.chain.nAll = 0 from e1]
    omega
  · unfold LdORE.lastP LdTenD.stepIn
    rw [LdProg.pBad_snoc, LdProg.pBad_snoc, LdProg.pBad_snoc, LdProg.pBad_nil, a1.2.2.1, c2,
      pBad_one, show R.endStep.chain.pBad = 0 from e3]
    show (0 : ENNReal) + 0 + (0 + 0) + 0 = 0
    simp
  · unfold LdORE.lastP LdTenD.stepIn
    rw [LdProg.pHid_snoc, LdProg.pHid_snoc, LdProg.pHid_snoc, LdProg.pHid_nil, a1.2.2.2, c2,
      pHid_one, show R.endStep.chain.pHid = 0 from e4]
    show (0 : ENNReal) + 0 + (0 + 0) + 0 = 0
    simp

theorem ldORE_rest (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldORE_rest F E Kc := by
  intro R
  refine ⟨fun z m => ?_, fun z n hw hμ => ?_⟩
  · show R.X.bt.maskPart z (Sum.elim (fun _ => 0) (R.S.ents m)) = _
    unfold BattPar.maskPart LdORE.restC
    simp only [add_mul, Finset.sum_add_distrib]
    congr 1
    · simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rfl
    · simp only [mul_assoc, ← Finset.mul_sum]
      congr 2
      simp only [Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← Finset.mul_sum]
      congr 1
      refine (Fintype.sum_sum_type (fun x : (R.Rw × (Fin R.k → Bool)) ⊕ R.S.Ent =>
        (Sum.elim (fun _ => (0 : E)) (placed R.μAt (R.mf (R.X.stOf z).2 q)) x) *
          Sum.elim (fun _ => (0 : E)) (R.S.ents m) x)).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, zero_add]
  · unfold LdORE.restC
    have h1 : (∑ i, if R.wAt (pIx R.X.bt.fmt (pdPlains E R.n R.k) i) = n then
            hSl (R.X.bt.par.vars z.st) (R.X.bt.par.hp z.st z.pt) i
          else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => if_neg fun h => hw _ h.symm
    have h2 : ∀ q, placed R.μAt (R.mf (R.X.stOf z).2 q) n = 0 := fun q =>
      Finset.sum_eq_zero fun a _ => if_neg fun h => hμ _ h.symm
    rw [h1]
    simp only [h2, mul_zero, Finset.sum_const_zero, add_zero]

end Cb
