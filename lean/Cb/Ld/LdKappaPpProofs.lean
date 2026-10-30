-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaPpProofs.lean: the proofs of the four statements of Cb/Ld/LdKappaPp.lean, level by
level, on the theorem of Cb/Ld/LdKappaWorkRef.lean over `LdObjT` (`ldKappaW_objT`).

This file's own part: the front of a closing at the technical report's plan ("split ; a step without
rounds") has one round, with error 0, for one instance's chain and for a batch's. Then come the two
closings with three tests and a rest (`LdObjPp`), and with "the rest" a fourth test (`LdObjRp`).
The five lists are the errors of the protocol's sub-protocols: weights-formedness, the test for
linear constraints at one instance, the link, a request's preamble, the test at N instances. These
errors, and the front's error 0, are numbers that the object and the splitting's link list
(`obj.nums`, Cb/Obj/LdObject.lean; `D.link.P.err`): that a sub-protocol or that link is sound at
them is no statement of this file either: see the head of Cb/Ld/LdKappaPp.lean.

The four theorems (statements and hypotheses: Cb/Ld/LdKappaPp.lean):
  `ldKappaPp_any`: round by round, with the bits `Z.bitsP ws`; the request a parameter.
  `ldKappaPp`: round by round, with these bits: the request `ldReqRef`.
  `ldKappaPp_bits`, `ldKappaPp_work`: the work vectors with these bits.

Main names:
  `ldKappaPp_split`: the splitting's one round: bits [0], at every κ.
  `ldKappaPp_frontC`, `ldKappaPp_frontA`: the front as a chain; as a chain for a batch, run once by
    the shared part: at most κ with the bits [0], at every κ.
  `ldKappaPp_objP`, `ldKappaPp_objR`: the object, level by level: under the hypotheses of their
    statements (`Bw.Kap κ`; the records of Cb/Ld/LdKappaWorkObj.lean at the cores; `BelowBT` of each
    whole test; in `ldKappaPp_objP` `BelowB` of the two rests; `r.BelowW wIn κ`), `BelowB` of the
    object's five lists at the bits of the statement.
  `ldKappaPp_of`: the same for `Z : LdObjZp` at `Z.bitsP ws`, from `Z.KapW ws κ`,
    `Z.R.r.BelowW ws.ins κ` and the nine records on the whole tests.
    Which class of bits each whole test has: the row of `Z.KapW` in the head of
    Cb/Ld/LdKappaPp.lean.

Limits: what is said and what is not: the head of Cb/Ld/LdKappaPp.lean.

Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import Cb.Ld.LdKappaPp
import Cb.Ld.LdKappaWProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain IOR.ChainA
open scoped ENNReal

section
variable {E : Type} [Field E] [Fintype E]

theorem ldKappaPp_split {Kc : Type} (D : LdSplD E Kc) (κ : ℝ≥0∞) : Err.BelowB D.link.P.err [0] κ :=
  belowB_none D.link.P.err κ ((ldSeg_below_named E Kc κ).2.2.1 D)

variable {S : Sig E} {E₀ : ExtSpec} {Wp : Type}

theorem ldKappaPp_frontC (G₁ G₂ : Grp S) (k : SplitAt G₁ G₂) (St₁ St₂ : Type)
    (sl₁ : Slf E St₁ G₁.C.J) (sl₂ : Slf E St₂ G₂.C.J) (St₀ : Type)
    (A₀ : IOR.Rels Unit St₀ E₀ (S.Msg × Wp)) (Rs : S.Ent → Prop) (dRs : DecidablePred Rs)
    (z : FSt S E₀ Wp Unit) f g m back (κ : ℝ≥0∞) :
    (LdTc.frontC
        (Front.step
          (Front.split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs
            (Front.nil ⟨_, claimRels (splitIn sl₁ sl₂) A₀⟩))
          z f g m back)).BelowB
      [0] κ := by
  unfold LdTc.frontC
  rw [Front.prog_step, Front.prog_split, Front.prog_nil, LdProg.onto_snoc,
    LdProg.onto_snoc, LdProg.onto_nil]
  exact Chain.belowB_app _ _ [0] [] κ
    (Chain.belowB_app _ _ [] [0] κ ((Chain.belowB_one _ _ κ).2 rfl)
      ((Chain.belowB_one _ _ κ).2 (ldKappaPp_split _ κ)))
    ((Chain.belowB_one _ _ κ).2 rfl)

theorem ldKappaPp_frontA (G₁ G₂ : Grp S) (k : SplitAt G₁ G₂) (St₁ St₂ : Type)
    (sl₁ : Slf E St₁ G₁.C.J) (sl₂ : Slf E St₂ G₂.C.J) (St₀ : Type)
    (A₀ : IOR.Rels Unit St₀ E₀ (S.Msg × Wp)) (Rs : S.Ent → Prop) (dRs : DecidablePred Rs)
    (z : FSt S E₀ Wp Unit) f g m back (κ : ℝ≥0∞) :
    ((Front.step (Front.split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs
            (Front.nil ⟨_, claimRels (splitIn sl₁ sl₂) A₀⟩))
          z f g m back).cA true).BelowB
      [0] κ := by
  rw [Front.cA_step, Front.cA_split, Front.cA_nil]
  exact ChainA.belowB_mk _ _ [0] [] κ
    (ChainA.belowB_mk _ _ [] [0] κ ((ChainA.belowB_one _ _ κ).2 rfl)
      (ldKappaPp_split (Front.splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs) κ)) rfl

end

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldKappaPp_objP (P : LdObjPp F E) (κ : ℝ≥0∞) (wOff wLk wSh wIn : ℕ)
    (L₁ L₂ L₃ LQ LK L₁B L₂B L₃B LQB : List ℕ) (hW : P.Bw.Kap κ)
    (hL : P.W.O.toC.P.KapCW P.D.Sn P.εf wOff κ) (h₁ : P.TP.D₁.BelowBT L₁ κ)
    (h₂ : P.TP.D₂.BelowBT L₂ κ) (h₃ : P.TP.D₃.BelowBT L₃ κ) (hQ : P.TP.Q'.c.BelowB LQ κ)
    (hK : P.K.P.KapCW P.D.Sl P.ε₀ P.ε₁ wLk κ) (hKc : P.Kc.run.BelowBT LK κ) (hR : P.r.BelowW wIn κ)
    (hB : P.on.ol.toC.P.KapCBW P.D.SnB P.εfB P.N wSh κ) (h₁B : P.TB.D₁.BelowBT L₁B κ)
    (h₂B : P.TB.D₂.BelowBT L₂B κ) (h₃B : P.TB.D₃.BelowBT L₃B κ) (hQB : P.cA'.BelowB LQB κ) :
    P.toT.obj.nums.BelowB
      ⟨List.replicate P.Bw.link.R.shape.nAll 0,
        linBits wOff ++ ([0] ++ ((0 :: L₁) ++ ((0 :: L₂) ++ ((0 :: L₃) ++ LQ)))),
        lkBits wLk ++ ((0 :: LK) ++ []),
        P.r.bits wIn,
        linBits wSh ++ ([0] ++ ((0 :: L₁B) ++ ((0 :: L₂B) ++ ((0 :: L₃B) ++ LQB))))⟩ κ := by
  refine ldKappaW_objT P.toT κ wOff wLk wSh wIn _ LK _ hW hL ?_ hK hKc hR hB ?_
  · show ((LdTc.frontC P.TP.front).append P.TP.Q.c).BelowB _ κ
    exact Chain.belowB_app _ _ [0] _ κ (ldKappaPp_frontC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ κ)
      (ldKappaW_cons P.TP.D₁ _ _ _ κ L₁ _ h₁
        (ldKappaW_cons P.TP.D₂ _ _ _ κ L₂ _ h₂ (ldKappaW_cons P.TP.D₃ _ _ _ κ L₃ LQ h₃ hQ)))
  · show P.cZ.forget.BelowB _ κ
    unfold LdObjPp.cZ LdLinPpT.cZV
    have e := (ldLinV_cZ_same E _ _ _ _ P.on.ol.toC P.N (P.TB.QA P.cA' P.same')
      (P.on.ol.toC.fqP P.TB.fa) (P.on.ol.toC.P.V6 P.D.SnB P.qaB P.N) (P.TB.tieF P.tie' P.x₀ P.y₀)
      (P.TB.qB₀ P.N P.q₀B P.bB')
      (P.TB.QV P.N P.q₀B P.bB' P.tie' P.x₀ P.y₀ P.cA' P.same' P.xB P.xC P.QV')).1
    refine belowBA_of_eq e _ κ
      (ldKappaW_linZA P.on.ol.toC (P.TB.QA P.cA' P.same') (P.on.ol.toC.fqP P.TB.fa) κ _ ?_)
    show ((P.TB.front.cA true).append (P.TB.QAt P.cA' P.same').cA).BelowB _ κ
    exact ChainA.belowB_app _ _ [0] _ κ (ldKappaPp_frontA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ κ)
      (ldKappaW_consSh P.TB.D₁ _ _ _ κ L₁B _ h₁B
        (ldKappaW_consSh P.TB.D₂ _ _ _ κ L₂B _ h₂B
          (ldKappaW_consLo P.TB.D₃ ⟨P.TB.Q', P.cA', P.same'⟩ _ _ κ L₃B LQB h₃B hQB)))

theorem ldKappaPp_objR (R : LdObjRp F E) (κ : ℝ≥0∞) (wOff wLk wSh wIn : ℕ)
    (L₁ L₂ L₃ L₄ LK L₁B L₂B L₃B L₄B : List ℕ) (hW : R.Bw.Kap κ)
    (hL : R.W.O.toC.P.KapCW (R.toLdObjD.std R.Y).Sn R.εf wOff κ) (h₁ : R.TP₀.D₁.BelowBT L₁ κ)
    (h₂ : R.TP₀.D₂.BelowBT L₂ κ) (h₃ : R.TP₀.D₃.BelowBT L₃ κ) (h₄ : R.X.run.BelowBT L₄ κ)
    (hK : R.K.P.KapCW (R.toLdObjD.std R.Y).Sl R.ε₀ R.ε₁ wLk κ) (hKc : R.Kc.run.BelowBT LK κ)
    (hR : R.r.BelowW wIn κ) (hB : R.on.ol.toC.P.KapCBW (R.toLdObjD.std R.Y).SnB R.εfB R.N wSh κ)
    (h₁B : R.TB₀.D₁.BelowBT L₁B κ) (h₂B : R.TB₀.D₂.BelowBT L₂B κ) (h₃B : R.TB₀.D₃.BelowBT L₃B κ)
    (h₄B : R.XB.run.BelowBT L₄B κ) :
    R.toPp.toT.obj.nums.BelowB
      ⟨List.replicate R.Bw.link.R.shape.nAll 0,
        linBits wOff ++ ([0] ++ ((0 :: L₁) ++ ((0 :: L₂) ++ ((0 :: L₃) ++ ((0 :: L₄) ++ []))))),
        lkBits wLk ++ ((0 :: LK) ++ []),
        R.r.bits wIn,
        linBits wSh ++ ([0] ++ ((0 :: L₁B) ++ ((0 :: L₂B) ++ ((0 :: L₃B) ++ ((0 :: L₄B) ++ [])))))⟩
      κ :=
  ldKappaPp_objP R.toPp κ wOff wLk wSh wIn L₁ L₂ L₃ _ LK L₁B L₂B L₃B _ hW hL h₁ h₂ h₃
    (ldKappaW_cons R.X.run _ _ _ κ L₄ [] h₄ (ldKappaW_nil _ _ _ κ)) hK hKc hR hB h₁B h₂B h₃B
    (ldKappaW_consLo R.XB.run _ _ _ κ L₄B [] h₄B (ldKappaW_nilA _ _ _ κ))

end

/-- from `Z.KapW ws κ` (`hK`), `Z.R.r.BelowW ws.ins κ` (`hR`) and the nine records on the whole
tests: of each of the nine only the equation "the whole test is its tower" is used -/
theorem ldKappaPp_of {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (Z : LdObjZp F E) (ws : LdWk4) (κ : ℝ≥0∞) (pK : Z.R.Kc.run.Pre3 Z.twK Z.dK)
    (p₁ : Z.R.TP₀.D₁.Pre3 Z.tw₁ Z.d₁) (p₂ : Z.R.TP₀.D₂.Pre3 Z.tw₂ Z.d₂)
    (p₃ : Z.R.TP₀.D₃.Pre3 Z.tw₃ Z.d₃) (p₄ : Z.R.X.run.Pre3 Z.tw₄ Z.d₄)
    (p₁B : Z.R.TB₀.D₁.PreJ Z.tw₁B Z.d₁B) (p₂B : Z.R.TB₀.D₂.PreJ Z.tw₂B Z.d₂B)
    (p₃B : Z.R.TB₀.D₃.PreJ Z.tw₃B Z.d₃B) (p₄B : Z.R.XB.run.PreJ Z.tw₄B Z.d₄B)
    (hK : Z.KapW ws κ) (hR : Z.R.r.BelowW ws.ins κ) :
    Z.R.toPp.toT.obj.nums.BelowB (Z.bitsP ws) κ :=
  ldKappaPp_objR Z.R κ ws.off ws.lk ws.sh ws.ins _ _ _ _ _ _ _ _ _ hK.wf hK.lin
    (ldKappaW_pre _ (Z.R.TP₀.D₁.up3 Z.tw₁) ws.off κ p₁.isT hK.t₁.bridge hK.t₁.tow)
    (ldKappaW_pre _ (Z.R.TP₀.D₂.up3 Z.tw₂) ws.off κ p₂.isT hK.t₂.bridge hK.t₂.tow)
    (ldKappaW_pre _ (Z.R.TP₀.D₃.up3 Z.tw₃) ws.off κ p₃.isT hK.t₃.bridge hK.t₃.tow)
    (ldKappaW_pre _ (Z.R.X.run.up3 Z.tw₄) ws.off κ p₄.isT hK.t₄.bridge hK.t₄.tow) hK.link
    (ldKappaW_pre _ (Z.R.Kc.run.up3 Z.twK) ws.lk κ pK.isT hK.tK.bridge hK.tK.tow) hR hK.linB
    (ldKappaW_pre _ (Z.R.TB₀.D₁.upJ Z.tw₁B) ws.sh κ p₁B.isT hK.t₁B.bridge hK.t₁B.tow)
    (ldKappaW_pre _ (Z.R.TB₀.D₂.upJ Z.tw₂B) ws.sh κ p₂B.isT hK.t₂B.bridge hK.t₂B.tow)
    (ldKappaW_pre _ (Z.R.TB₀.D₃.upJ Z.tw₃B) ws.ins κ p₃B.isT hK.t₃B.bridge hK.t₃B.tow)
    (ldKappaW_pre _ (Z.R.XB.run.upJ Z.tw₄B) ws.ins κ p₄B.isT hK.t₄B.bridge hK.t₄B.tow)

theorem ldKappaPp_any :
    Spec.ldKappaPp_any := fun _ _ _ _ _ _ _ _ _ _ _ _ _ Z _ P _ _ _ _ κ ws h hK hP =>
  ldKappaPp_of Z ws κ h.pK h.p₁ h.p₂ h.p₃ h.p₄ h.p₁B h.p₂B h.p₃B h.p₄B hK
    (ldKappaW_pack Z.R.toLdObjD.pack P h.core.reqIs ws.ins κ hP)

theorem ldKappaPp : Spec.ldKappaPp := fun _ _ _ _ _ _ _ _ _ _ _ _ _ Z _ Rq _ first b Ls T _ _ _ κ _ _ _ ws h hK hQ =>
  ldKappaPp_of Z ws κ h.pK h.p₁ h.p₂ h.p₃ h.p₄ h.p₁B h.p₂B h.p₃B h.p₄B hK
    (ldKappaW_pack Z.R.toLdObjD.pack _ h.core.reqIs ws.ins κ
      (ldKappaW_req Rq _ first first.tgt (.nil first.tgt) (LdProg.all_nilK _ _)
        b Ls T ws.ins κ hQ.bFirst hQ.bMore hQ.bSegs hQ.bTail hQ.bLast))

theorem ldKappaPp_bits : Spec.ldKappaPp_bits := by
  intro F E _ _ _ _ _ Z κ ws hB
  have o1 : ws.off ≤ ws.top := le_trans (le_max_left _ _) (le_max_left _ _)
  have o2 : ws.lk ≤ ws.top := le_trans (le_max_right _ _) (le_max_left _ _)
  have o3 : ws.sh ≤ ws.top := le_trans (le_max_left _ _) (le_max_right _ _)
  have o4 : ws.ins ≤ ws.top := le_trans (le_max_right _ _) (le_max_right _ _)
  have z0 : (0 : ℕ) ≤ ws.top := Nat.zero_le _
  refine ⟨fun g hg => SubsR.nums_belowB_of_is _ _ κ hB g hg,
    (SubsR.nums_belowB_exists _ _ κ hB).imp fun _ hg => hg.1,
    fun g hg =>
      ⟨belowB_allLe _ _ ?_, belowB_allLe _ _ ?_, belowB_allLe _ _ ?_,
        belowB_allLe _ _ ?_, belowB_allLe _ _ ?_⟩⟩
  · rw [hg.wf]; exact leAll_rep z0 _
  · rw [hg.linOff]
    exact leAll_app (linBits_le o1)
      (leAll_app (leAll_cons z0 (leAll_nil _))
        (leAll_app (leAll_cons z0 (LdRunD.bitsT_le _ _ o1))
          (leAll_app (leAll_cons z0 (LdRunD.bitsT_le _ _ o1))
            (leAll_app (leAll_cons z0 (LdRunD.bitsT_le _ _ o1))
              (leAll_app (leAll_cons z0 (LdRunD.bitsT_le _ _ o1)) (leAll_nil _))))))
  · rw [hg.link]
    exact leAll_app (lkBits_le o2)
      (leAll_app (leAll_cons z0 (LdRunD.bitsT_le _ _ o2)) (leAll_nil _))
  · rw [hg.req]; exact Z.R.r.bits_le o4
  · rw [hg.linOn]
    exact leAll_app (linBits_le o3)
      (leAll_app (leAll_cons z0 (leAll_nil _))
        (leAll_app (leAll_cons z0 (LdRunD.bitsT_le _ _ o3))
          (leAll_app (leAll_cons z0 (LdRunD.bitsT_le _ _ o3))
            (leAll_app (leAll_cons z0 (LdRunD.bitsT_le _ _ o4))
              (leAll_app (leAll_cons z0 (LdRunD.bitsT_le _ _ o4)) (leAll_nil _))))))

theorem ldKappaPp_work :
    Spec.ldKappaPp_work := fun F E Fp _ _ _ _ _ _ _ _ Kc p Z _ Rq core first b Ls T qφ q κ' κ V p₀ plR ws h hK hQ =>
  ldKappaPp_bits F E Z κ ws
    (ldKappaPp F E Fp Kc p Z Rq core first b Ls T qφ q κ' κ V p₀ plR ws h hK hQ)

end Cb
