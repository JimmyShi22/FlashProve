-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefPartBatProofs.lean: the statements of Cb/Req1/LdSegRefPartBat.lean, proved.

The block follows by the theorems on the named moves (Cb/Req1/LdSegProofs.lean; for carry, format
and errors Cb/Req1/LdSegCarry.lean, Cb/Req1/LdSegFormatMoves.lean, Cb/Req1/LdReqBelow.lean), the
two steps by the rule for a step that only maps the explicit part.
What each statement says: the head of Cb/Req1/LdSegRefPartBat.lean.
-/
import Cb.Req1.LdSegRefPartBat
import Cb.Req1.LdSegFrontTabZk

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR IOR.Chain
open scoped ENNReal

namespace LdPbD
variable {E Kc : Type} [Field E] (D : LdPbD E Kc)

/-- under `h`, all rows of the old family hold iff those that are batched and those that are copied
hold -/
theorem all_iff (h : D.Part) (x : (D.B → E) × (∀ b, D.Sb b)) (m : D.S.Ent → E) :
    Slf.All D.sl x m ↔
    Slf.All (fun b => D.sl (D.i₁ b)) (fun b => x.1 (D.i₁ b), fun b => x.2 (D.i₁ b)) m ∧
    Slf.All (fun b => D.sl (D.i₂ b)) (fun b => x.1 (D.i₂ b), fun b => x.2 (D.i₂ b)) m := by
  refine ⟨fun hx => ⟨fun b => hx _, fun b => hx _⟩, fun hx b => ?_⟩
  rcases h b with ⟨b₁, rfl⟩ | ⟨b₂, rfl⟩
  · exact hx.1 b₁
  · exact hx.2 b₂

/-- all rows of the new family hold iff the one row and the copied rows hold -/
theorem all'_iff (x : D.bat.tgt.St) (m : D.S.Ent → E) :
    Slf.All D.sl' (D.fOut x).1 m ↔
    (Slf.bat D.Z.ze fun b => D.sl (D.i₁ b)).Holds x.1 m ∧
    Slf.All (fun b => D.sl (D.i₂ b)) x.2.1 m :=
  ⟨fun h => ⟨h (.inl ()), fun b => h (.inr b)⟩,
    fun h b => match b with | .inl _ => h.1 | .inr b => h.2 b⟩

theorem okIn (h : D.Part) : LdStepOK D.S D.src.A D.bat.src.A D.fIn :=
  ⟨fun st _ _ hw => ⟨((D.all_iff h st.1 _).1 hw.1).1, ((D.all_iff h st.1 _).1 hw.1).2, hw.2⟩,
    fun _ _ ho => ho, fun _ => rfl,
    fun st _ _ _ hw => ⟨(D.all_iff h st.1 _).2 ⟨hw.1, hw.2.1⟩, hw.2.2⟩⟩

theorem okOut : LdStepOK D.S D.bat.tgt.A D.tgt.A D.fOut :=
  ⟨fun st _ _ hw => ⟨(D.all'_iff st _).2 ⟨hw.1, hw.2.1⟩, hw.2.2⟩, fun _ _ ho => ho, fun _ => rfl,
    fun st _ _ _ hw => ⟨((D.all'_iff st _).1 hw.1).1, ((D.all'_iff st _).1 hw.1).2, hw.2⟩⟩

end LdPbD

theorem ldPartBat_hyp : Spec.ldPartBat_hyp := by
  intro E Kc _ _ D hP hZ
  unfold LdPbD.prog
  rw [LdProg.hyp_snoc, LdProg.hyp_snoc, LdProg.hyp_snoc]
  have hb : (LdMv.bat D.bat).chain.AllB := ldSeg_mv E Kc _ _ (.bat D.bat) hZ
  have cb : (LdMv.bat D.bat).chain = .one D.bat.link := by rw [LdMv.chain]
  rw [cb] at hb
  exact ⟨⟨⟨LdProg.hyp_nilK _, (D.okIn hP).hyp⟩, hb⟩, D.okOut.hyp⟩

theorem ldPartBat_kinds : Spec.ldPartBat_kinds := by
  intro E Kc _ _ D
  unfold LdPbD.prog
  rw [LdProg.all_snoc, LdProg.all_snoc, LdProg.all_snoc]
  exact ⟨⟨⟨LdProg.all_nilK _ _, Or.inr (Or.inr rfl)⟩, Or.inr (Or.inl rfl)⟩, Or.inr (Or.inr rfl)⟩

theorem ldPartBat_zk : Spec.ldPartBat_zk := by
  intro E Kc _ _ D base hZ
  have ht : (LdMv.bat D.bat).chain.AllT :=
    ldSeg_mvT E Kc _ _ (.bat D.bat) hZ (fun h => LdTag.noConfusion h) (fun h => LdTag.noConfusion h)
  have cb : (LdMv.bat D.bat).chain = .one D.bat.link := by rw [LdMv.chain]
  rw [cb] at ht
  unfold LdPbD.prog
  rw [LdProg.zk_snoc, LdProg.zk_snoc, LdProg.zk_snoc]
  refine ⟨⟨⟨(LdProg.zk_nil _ _).2 trivial, ?_⟩, ?_⟩, ?_⟩
  · unfold LdPbD.stepIn ldStepF
    rw [LdMv.Zk]
    trivial
  · rw [LdMv.Zk]
    exact okGiven_of_allT Kc _ _ _ _ ht
  · unfold LdPbD.stepOut ldStepF
    rw [LdMv.Zk]
    trivial

theorem ldPartBat_carry : Spec.ldPartBat_carry := by
  intro E Kc _ _ D base Rd Rr own Mk _ _ val hb
  unfold LdPbD.prog
  rw [LdProg.after_snoc, LdProg.after_snoc, LdProg.after_snoc, LdProg.after_nil]
  have h1 : D.stepIn.After base (D.bat.src.wideFact Rd Rr own Mk val) :=
    ldStepF_carry D.S D.src.A D.bat.src.A D.fIn base _ hb
  have h2 : (LdMv.bat D.bat).After (D.stepIn.After base) (D.bat.tgt.wideFact Rd Rr own Mk val) :=
    segWide_bat D.bat _ Rd Rr own Mk val h1
  have h2' : (LdMv.sub D.bat.src D.bat.tgt (.one D.bat.link)).After
      (D.stepIn.After base) (D.bat.tgt.wideFact Rd Rr own Mk val) := by
    have cb : (LdMv.bat D.bat).chain = .one D.bat.link := by rw [LdMv.chain]
    have c2 : (LdMv.sub D.bat.src D.bat.tgt (.one D.bat.link)).chain = .one D.bat.link := by
      rw [LdMv.chain]
    unfold LdMv.After at h2 ⊢
    rw [cb] at h2
    rw [c2]
    exact h2
  exact ldStepF_carry D.S D.bat.tgt.A D.tgt.A D.fOut _ _ h2'

theorem ldPartBat_fmt : Spec.ldPartBat_fmt := by
  intro E Kc _ _ E0 Rc Pw D i rc px q
  obtain ⟨_, mU, _⟩ := ldFmt_mv E Kc E0 Rc Pw
  unfold LdPbD.prog
  refine (LdProg.fmt_snoc _ _ _ _).2
    ⟨D.bat.tgt.fmt i (fun st => rc st.2.2) px q,
      (LdProg.fmt_snoc _ _ _ _).2
        ⟨D.bat.src.fmt i (fun st => rc st.2.2) px q,
          (LdProg.fmt_snoc _ _ _ _).2
            ⟨D.src.fmt i (fun x => rc x.2) px q, (LdProg.fmt_nil _ _ _).2 rfl, ?_⟩,
          ?_⟩,
      ?_⟩
  · exact ldStepF_fmt D.S D.src.A D.bat.src.A D.fIn i (fun x => rc x.2)
      (fun st => rc st.2.2) px q fun _ => rfl
  · exact mU _ _ _ _ _
      ((Chain.fmt_one _ _ _).2 (ldFmt_bat E Kc E0 Rc Pw D.bat i (fun s => rc s.2) px q))
  · exact ldStepF_fmt D.S D.bat.tgt.A D.tgt.A D.fOut i (fun st => rc st.2.2)
      (fun x => rc x.2) px q fun _ => rfl

theorem ldPartBat_below : Spec.ldPartBat_below := by
  intro E Kc _ _ D κ h
  obtain ⟨_, hb, _⟩ := ldSeg_below_named E Kc κ
  have c2 : (LdMv.sub D.bat.src D.bat.tgt (.one D.bat.link)).chain = .one D.bat.link := by
    rw [LdMv.chain]
  unfold LdPbD.prog
  rw [LdProg.below_snoc, LdProg.below_snoc, LdProg.below_snoc, c2, errBelow_one]
  exact ⟨⟨⟨LdProg.below_nil _ κ, ldStepF_below D.S _ _ _ κ⟩, (hb D.bat).2 h⟩,
    ldStepF_below D.S _ _ _ κ⟩

theorem ldPartBat_nums : Spec.ldPartBat_nums := by
  intro E Kc _ _ D
  obtain ⟨_, _, _, _, _, hp⟩ := ldSeg_rounds E Kc
  have a1 := hp D.src D.bat.src (sideF D.S D.fIn) (sideG D.S (ExtMap.id D.E₀))
    (sideM D.S D.fIn fun _ w => w.2) (sideB D.S fun _ w => w.2)
  have a3 := hp D.bat.tgt D.tgt (sideF D.S D.fOut) (sideG D.S (ExtMap.id D.E₀))
    (sideM D.S D.fOut fun _ w => w.2) (sideB D.S fun _ w => w.2)
  have c2 : (LdMv.sub D.bat.src D.bat.tgt (.one D.bat.link)).chain = .one D.bat.link := by
    rw [LdMv.chain]
  unfold LdPbD.prog LdPbD.stepIn LdPbD.stepOut ldStepF
  refine ⟨?_, ?_, ?_⟩
  · rw [LdProg.nAll_snoc, LdProg.nAll_snoc, LdProg.nAll_snoc, LdProg.nAll_nil,
      a1.1, a3.1, c2, nAll_one]
    rfl
  · rw [LdProg.pBad_snoc, LdProg.pBad_snoc, LdProg.pBad_snoc, LdProg.pBad_nil,
      a1.2.2.1, a3.2.2.1, c2, pBad_one]
    show (0 : ℝ≥0∞) + 0 + 0 + 0 = 0
    simp
  · rw [LdProg.pHid_snoc, LdProg.pHid_snoc, LdProg.pHid_snoc, LdProg.pHid_nil,
      a1.2.2.2, a3.2.2.2, c2, pHid_one]
    show (0 : ℝ≥0∞) + 0 + 0 + 0 = 0
    simp

theorem ldPartBat_supp : Spec.ldPartBat_supp := by
  intro E Kc _ D n h b st
  rcases b with ⟨⟩ | b
  · show (Slf.bat D.Z.ze fun b => D.sl (D.i₁ b)) st n = 0
    unfold Slf.bat
    exact Finset.sum_eq_zero fun b _ => by
      show D.sl (D.i₁ b) (st.1 b) n * D.Z.ze st.2 b = 0
      rw [h, zero_mul]
  · exact h _ st

end Cb
