-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaWorkRef.lean: "every round's error, counting its proof-of-work bits, is at most κ":
the reference request (`ldReqRef`, Cb/Req1/LdReqRef.lean), w bits at each closing's round
"locations"; the object's five lists, level by level.

Definitions and theorems: glue on Cb/Ld/LdKappaWork.lean, Cb/Ld/LdKappaWorkObj.lean; nothing is
evaluated. "At most κ with the bits B" is `Err.BelowB` (Cb/Ld/LdKappaBits.lean): B has one entry for
each round, and in each round e ≤ κ · (2^b · v), with e the error (a count: `Err`, Iop/Rbr.lean), b
the round's entry of B, v the number of all values of the round's verifier message.
The five lists are the errors of the protocol's sub-protocols: weights-formedness, the test for
linear constraints at one instance, the link, a request's preamble, the test at N instances (in
Lean: wf, linOff, link, req, linOn). These errors are numbers that a link or the object lists (the
data field `Link.P.err`; `obj.nums`, Cb/Obj/LdObject.lean: a `SubsR.Nums`, Hiop/RecBuild.lean, whose
five entries each have the data field `err`): that a link or a sub-protocol is sound at the numbers
that are listed for it is no statement of this file; for the object that tie is `Spec.ldObj_hyp`
(Cb/Obj/LdObject.lean), under `Obj.OK L`, in the sense of `SubsR.HypK` (Hiop/RecBuild.lean), for the
test at N instances with a closing `Spec.ldLinCB_know` (Cb/Ld/LdLinChainB.lean: `KnowB` for the
vectors that share the encoded index and its record (`SameKey P.k0`), on the statements with the
condition `(P.j0 on0).on`), for weights-formedness `Spec.ldWf` (Cb/Ld/LdWf.lean), each under its
hypotheses (that condition itself asks soundness of some of the parts one level down: for these the
tie carries soundness, it does not found it).

Main names:
  `ldKappaW_req`: for `more` all of whose moves are sendings or steps (`hm`): first sending's number
    (`h1`), further first moves (`more.Below κ`), `L.NumsW w κ`, the last body's `T.A.Nums κ`, the
    final batching's list (`h5`) → `(ldReqRef R first a₁ more hm b L T).BelowW w κ`.
  `nums_belowB_exists`: `P.BelowB B κ` (`SubsR.Nums.BelowB`; B a `Bits5`) → there is a vector g of
    proof-of-work bits with exactly these bits, and `P.BelowG g κ`.
  `ldKappaW_objT`: for the object `T : LdObjT` (Cb/Obj/LdObjectTerms.lean), with four numbers of
    bits wOff, wLk, wSh, wIn by the class of the round that draws locations (`LdWk4`,
    Cb/Ld/LdKappaW.lean). Its premises are the records of Cb/Ld/LdKappaWorkObj.lean at its cores,
    the closings `T.Qt.c`, `T.cZ.forget` at most κ with bits LQ, LZ, the whole test of the link's
    closing with `T.Kc.run.BelowBT LK κ`, `T.Bw.Kap κ` and `T.r.BelowW wIn κ`. It concludes
    `T.obj.nums.BelowB` at the five lists of bits of its statement.
  `ldKappaW_objP`: both closings at the plan (`LdObjP`): the two tests of each plan, and "the rest"
    of each as a chain. (not all hypotheses are named here: see its statement)
  `ldKappaW_objR`: "the rest" of each plan one more test (`LdObjR`): seven tests. (not all
    hypotheses are named here: see its statement)

Limits: this file says nothing on the way back. This file says nothing on the value of any number.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdKappaWorkObj
import Cb.Ld.LdKappaObj
import Cb.Req1.LdReqRefFinal
import Cond.ObjBits

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain IOR.ChainA
open scoped ENNReal

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- the numbers of a reference segment, with w bits at the locations: the record `LdRefS.NumsAt`
(Cb/Req1/LdReqRefFinal.lean), with w at the clause "loc" -/
structure LdRefS.NumsAtW {I : LdRefIx E} {a : LdStage E Kc}
    (S : LdRefS E Kc I a) (w : ℕ) (κ : ℝ≥0∞) : Prop where
  body : S.A.Nums κ
  bat  : (S.K.Z.err : ℝ≥0∞) ≤ κ * (Fintype.card S.K.Z.D : ℝ≥0∞)
  fold : Err.Below S.l.P.err κ
  snd  : (ldSendFamErr S.Qc.N S.Qc.Sd S.Qc.L : ℝ≥0∞) ≤ κ * (Fintype.card S.Qc.Sd.D : ℝ≥0∞)
  loc  : (((Fintype.card S.K.Pf - S.K.e - 1) ^ S.Qc.t : ℕ) : ℝ≥0∞) ≤
    κ * ((2 : ℝ≥0∞) ^ w * (Fintype.card (Fin S.Qc.t → S.K.Pf) : ℝ≥0∞))

def LdRefL.NumsW {I : LdRefIx E} {a : LdStage E Kc} (w : ℕ) (κ : ℝ≥0∞) :
    {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S => L.NumsW w κ ∧ S.NumsAtW w κ

/-- a segment with one group, with work at the locations -/
theorem ldKappaW_one (a : LdStage E Kc) (D : LdCl1 E Kc) (body : LdProg a D.bat.src)
    (hT : body.All fun t => t = .send ∨ t = .sub ∨ t = .step) (l : Link Kc D.fold.src.J D.fold.mid)
    (Q : LdCloseD D.fold) (w : ℕ) (κ : ℝ≥0∞) (hb : body.Below κ)
    (hZ : (D.Z.err : ℝ≥0∞) ≤ κ * (Fintype.card D.Z.D : ℝ≥0∞)) (hl : Err.Below l.P.err κ)
    (hs : (ldSendFamErr Q.N Q.Sd Q.L : ℝ≥0∞) ≤ κ * (Fintype.card Q.Sd.D : ℝ≥0∞))
    (hc : (((Fintype.card D.Pf - D.e - 1) ^ Q.t : ℕ) : ℝ≥0∞) ≤
      κ * ((2 : ℝ≥0∞) ^ w * (Fintype.card (Fin Q.t → D.Pf) : ℝ≥0∞))) :
    (segOne D body hT l Q).BelowW w κ := by
  obtain ⟨n1, n2, -, -, n5, -⟩ := ldSeg_below_named E Kc κ
  obtain ⟨-, -, -, n4, -, -⟩ := ldSeg_below_named E Kc (κ * 2 ^ w)
  refine ⟨hb, ?_, ?_, (n1 D.fold.tgt Q.snd).2 hs, ?_⟩
  · show D.batP.Below κ
    unfold LdCl1.batP
    exact (LdProg.below_snoc _ _ _).2
      ⟨(LdProg.below_snoc _ _ _).2 ⟨LdProg.below_nil _ κ, (errBelow_one _ κ).2 ((n2 D.bat).2 hZ)⟩,
        ldStepF_below _ _ _ _ κ⟩
  · show (Q.foldP l).Below κ
    unfold LdCloseD.foldP
    exact (LdProg.below_snoc _ _ _).2
      ⟨LdProg.below_nil _ κ, (errBelow_one _ κ).2 ((n5 D.fold l).2 hl)⟩
  · show Q.locP.Below (κ * 2 ^ w)
    unfold LdCloseD.locP
    exact (LdProg.below_snoc _ _ _).2
      ⟨LdProg.below_nil _ _, (errBelow_one _ _).2 ((n4 Q.loc).2 (by rw [mul_assoc]; exact hc))⟩

theorem ldKappaW_segs {I : LdRefIx E} {a b : LdStage E Kc}
    (L : LdRefL E Kc I a b) (w : ℕ) (κ : ℝ≥0∞) :
    L.NumsW w κ → L.segs.BelowW w κ := by
  induction L with
  | nil => intro _; rw [LdRefL.segs, LdSegs.BelowW]; trivial
  | snoc L S ih =>
      intro h
      rw [LdRefL.NumsW] at h
      rw [LdRefL.segs, LdSegs.BelowW]
      have hs := ldKappaW_one S.A.V.Fp.s0 S.K.R.c1 (S.K.R.Y.body S.K.R.c1.bat.src S.K.tensor)
        S.K.kinds S.l S.Qc w κ (ldSegRefAll_below E Kc _ S.A S.K.St₁ S.K.fz S.K.Az κ h.2.body)
        h.2.bat h.2.fold h.2.snd h.2.loc
      exact ⟨ih h.1,
        ⟨LdProg.below_app _ _ κ
            ((LdProg.below_snoc _ _ _).2 ⟨LdProg.below_nil _ κ, (errBelow_one _ κ).2 trivial⟩)
            hs.body,
          hs.bat, hs.fold, hs.snd, hs.loc⟩⟩

end

/-- The reference request with work at its closings' locations. -/
theorem ldKappaW_req {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (R : LdORE F E Kc) (a : LdStage E Kc) (first : LdSendD a) (a₁ : LdStage E Kc)
    (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
    (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b) (w : ℕ) (κ : ℝ≥0∞)
    (h1 : (ldSendFamErr first.N first.Sd first.L : ℝ≥0∞) ≤ κ * (Fintype.card first.Sd.D : ℝ≥0∞))
    (h2 : more.Below κ) (h3 : L.NumsW w κ) (h4 : T.A.Nums κ)
    (h5 : Err.Below (R.X.bt.nums R.Cf.conf.E0 Kc).err κ) :
    (ldReqRef R first a₁ more hm b L T).BelowW w κ := by
  refine ⟨((ldSeg_below_named E Kc κ).1 _ first).2 h1,
    h2,
    ldKappaW_segs L w κ h3,
    LdProg.asSub_below _ κ (LdProg.below_app _ _ κ ?_ ?_)⟩
  · unfold LdRefT.tail
    exact (LdProg.below_snoc _ _ _).2
      ⟨LdProg.below_app _ _ κ
          ((LdProg.below_snoc _ _ _).2 ⟨LdProg.below_nil _ κ, (errBelow_one _ κ).2 trivial⟩)
          (ldSegRefAll_below E Kc _ T.A T.St₁ T.fz T.Az κ h4),
        (errBelow_one _ κ).2 trivial⟩
  · unfold LdORE.lastP
    exact (LdProg.below_snoc _ _ _).2
      ⟨(LdProg.below_snoc _ _ _).2
          ⟨(LdProg.below_snoc _ _ _).2 ⟨LdProg.below_nil _ κ, (errBelow_one _ κ).2 trivial⟩,
            (errBelow_one _ κ).2 h5⟩,
        (errBelow_one _ κ).2 trivial⟩

end Cb

namespace Hiop
open Iop
open scoped ENNReal

/-- five plain lists of bits -/
structure Bits5 where
  wf     : List ℕ
  linOff : List ℕ
  link   : List ℕ
  req    : List ℕ
  linOn  : List ℕ

namespace SubsR
variable {C : ConfigurationWithOutOfDomainSample} {S : SubsR C}

/-- the five lists of errors, each with its list of bits -/
structure Nums.BelowB (P : S.Nums) (B : Bits5) (κ : ℝ≥0∞) : Prop where
  wf     : Err.BelowB P.wf.err B.wf κ
  linOff : Err.BelowB P.linOff.err B.linOff κ
  link   : Err.BelowB P.link.err B.link κ
  req    : Err.BelowB P.req.err B.req κ
  linOn  : Err.BelowB P.linOn.err B.linOn κ

/-- a vector of proof-of-work bits has exactly these bits -/
structure Bits.Is (g : S.Bits) (B : Bits5) : Prop where
  wf     : g.wf.toList = B.wf
  linOff : g.linOff.toList = B.linOff
  link   : g.link.toList = B.link
  req    : g.req.toList = B.req
  linOn  : g.linOn.toList = B.linOn

theorem nums_belowB_of_is (P : S.Nums) (B : Bits5) (κ : ℝ≥0∞) (h : P.BelowB B κ)
    (g : S.Bits) (hg : g.Is B) : P.BelowG g κ :=
  ⟨(belowB_iff_G _ _ κ).2 (by rw [hg.wf]; exact h.wf),
    (belowB_iff_G _ _ κ).2 (by rw [hg.linOff]; exact h.linOff),
    (belowB_iff_G _ _ κ).2 (by rw [hg.link]; exact h.link),
    (belowB_iff_G _ _ κ).2 (by rw [hg.req]; exact h.req),
    (belowB_iff_G _ _ κ).2 (by rw [hg.linOn]; exact h.linOn)⟩

theorem nums_belowB_exists (P : S.Nums) (B : Bits5) (κ : ℝ≥0∞) (h : P.BelowB B κ) :
    ∃ g : S.Bits, g.Is B ∧ P.BelowG g κ := by
  obtain ⟨g1, e1⟩ := belowB_exists _ _ κ h.wf
  obtain ⟨g2, e2⟩ := belowB_exists _ _ κ h.linOff
  obtain ⟨g3, e3⟩ := belowB_exists _ _ κ h.link
  obtain ⟨g4, e4⟩ := belowB_exists _ _ κ h.req
  obtain ⟨g5, e5⟩ := belowB_exists _ _ κ h.linOn
  exact ⟨⟨g1, g2, g3, g4, g5⟩,
    ⟨e1, e2, e3, e4, e5⟩,
    nums_belowB_of_is P B κ h _ ⟨e1, e2, e3, e4, e5⟩⟩

end SubsR
end Hiop

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain IOR.ChainA
open scoped ENNReal

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem belowBA_of_eq {K : Type} {A B : Joint K} {c c' : ChainA K A B} (e : c = c') (L : List ℕ)
    (κ : ℝ≥0∞) (h : c'.BelowB L κ) : c.BelowB L κ := e ▸ h

theorem ldKappaW_objT (T : LdObjT F E) (κ : ℝ≥0∞) (wOff wLk wSh wIn : ℕ) (LQ LK LZ : List ℕ)
    (hW : T.Bw.Kap κ) (hL : T.W.O.toC.P.KapCW T.Sn T.εf wOff κ) (hQ : T.Qt.c.BelowB LQ κ)
    (hK : T.K.P.KapCW T.Sl T.ε₀ T.ε₁ wLk κ) (hKc : T.Kc.run.BelowBT LK κ) (hR : T.r.BelowW wIn κ)
    (hB : T.on.ol.toC.P.KapCBW T.SnB T.εfB T.N wSh κ) (hZ : T.cZ.forget.BelowB LZ κ) :
    T.obj.nums.BelowB
      ⟨List.replicate T.Bw.link.R.shape.nAll 0, linBits wOff ++ LQ, lkBits wLk ++ ((0 :: LK) ++ []),
        T.r.bits wIn, linBits wSh ++ LZ⟩ κ := by
  refine ⟨belowB_none (s := T.Bw.link.R.shape) T.Bw.link.P.err κ (ldKappa_wf T.Bw κ hW), ?_, ?_,
    ldReq_belowW _ _ T.r T.w₀ wIn κ hR, ?_⟩
  · exact (ldKappaW_linC T.W.O.toC.P T.W.O.on0 T.Sn T.εf wOff (T.W.O.toC.cZ T.Qt T.fq) T.dT κ LQ hL
      (ldKappaW_linZ T.W.O.toC T.Qt T.fq κ LQ hQ))
  · exact (ldKappaW_linkC T.K.P T.on0K T.on1K T.Sl T.ε₀ T.ε₁ wLk T.Kc T.dK₂ T.dK κ LK hK hKc)
  · show Err.BelowB (T.on.ol.termV T.onB T.SnB T.qaB T.εfB T.N T.cZ T.dB T.dB₀).a.err _ κ
    rw [(ldOnT_same F E T.on.ol T.onB T.SnB T.qaB T.εfB T.N T.VT T.cZ T.dB T.dB₀).1]
    exact (ldKappaW_linCA T.on.ol.toC.P T.onB T.SnB T.εfB T.N wSh T.cZ.forget T.dB κ LZ hB hZ)

theorem ldKappaW_objP (P : LdObjP F E) (κ : ℝ≥0∞) (wOff wLk wSh wIn : ℕ)
    (L₁ L₂ LQ LK L₁B L₂B LQB : List ℕ) (hW : P.Bw.Kap κ) (hL : P.W.O.toC.P.KapCW P.Sn P.εf wOff κ)
    (h₁ : P.TP.D₁.BelowBT L₁ κ) (h₂ : P.TP.D₂.BelowBT L₂ κ) (hQ : P.TP.Q'.c.BelowB LQ κ)
    (hK : P.K.P.KapCW P.Sl P.ε₀ P.ε₁ wLk κ) (hKc : P.Kc.run.BelowBT LK κ) (hR : P.r.BelowW wIn κ)
    (hB : P.on.ol.toC.P.KapCBW P.SnB P.εfB P.N wSh κ) (h₁B : P.TB.D₁.BelowBT L₁B κ)
    (h₂B : P.TB.D₂.BelowBT L₂B κ) (hQB : P.cA'.BelowB LQB κ) :
    P.toT.obj.nums.BelowB
      ⟨List.replicate P.Bw.link.R.shape.nAll 0,
        linBits wOff ++ ((0 :: L₁) ++ ((0 :: L₂) ++ LQ)),
        lkBits wLk ++ ((0 :: LK) ++ []),
        P.r.bits wIn,
        linBits wSh ++ ((0 :: L₁B) ++ ((0 :: L₂B) ++ LQB))⟩ κ := by
  refine ldKappaW_objT P.toT κ wOff wLk wSh wIn _ LK _ hW hL ?_ hK hKc hR hB ?_
  · exact ldKappaW_cons P.TP.D₁ _ _ _ κ L₁ _ h₁ (ldKappaW_cons P.TP.D₂ _ _ _ κ L₂ LQ h₂ hQ)
  · show P.cZ.forget.BelowB _ κ
    unfold LdObjP.cZ LdLinPlT.cZV
    have e := (ldLinV_cZ_same E _ _ _ _ P.on.ol.toC P.N (P.TB.QA P.cA' P.same') P.TB.fq
      (P.on.ol.toC.P.V6 P.SnB P.qaB P.N) (P.TB.tie₀ P.tie') (P.TB.qB₀ P.N P.q₀B P.bB')
      (P.TB.QV P.N P.q₀B P.bB' P.tie' P.cA' P.same' P.x₀ P.QV')).1
    refine belowBA_of_eq e _ κ (ldKappaW_linZA P.on.ol.toC (P.TB.QA P.cA' P.same') P.TB.fq κ _ ?_)
    exact (ldKappaW_consSh P.TB.D₁ _ _ _ κ L₁B _ h₁B
      (ldKappaW_consLo P.TB.D₂ ⟨P.TB.Q', P.cA', P.same'⟩ _ _ κ L₂B LQB h₂B hQB))

theorem ldKappaW_objR (R : LdObjR F E) (κ : ℝ≥0∞) (wOff wLk wSh wIn : ℕ)
    (L₁ L₂ L₃ LK L₁B L₂B L₃B : List ℕ) (hW : R.Bw.Kap κ) (hL : R.W.O.toC.P.KapCW R.Sn R.εf wOff κ)
    (h₁ : R.TP₀.D₁.BelowBT L₁ κ) (h₂ : R.TP₀.D₂.BelowBT L₂ κ) (h₃ : R.X.run.BelowBT L₃ κ)
    (hK : R.K.P.KapCW R.Sl R.ε₀ R.ε₁ wLk κ) (hKc : R.Kc.run.BelowBT LK κ) (hR : R.r.BelowW wIn κ)
    (hB : R.on.ol.toC.P.KapCBW R.SnB R.εfB R.N wSh κ) (h₁B : R.TB₀.D₁.BelowBT L₁B κ)
    (h₂B : R.TB₀.D₂.BelowBT L₂B κ) (h₃B : R.XB.run.BelowBT L₃B κ) :
    R.toP.toT.obj.nums.BelowB
      ⟨List.replicate R.Bw.link.R.shape.nAll 0,
        linBits wOff ++ ((0 :: L₁) ++ ((0 :: L₂) ++ ((0 :: L₃) ++ []))),
        lkBits wLk ++ ((0 :: LK) ++ []),
        R.r.bits wIn,
        linBits wSh ++ ((0 :: L₁B) ++ ((0 :: L₂B) ++ ((0 :: L₃B) ++ [])))⟩ κ :=
  ldKappaW_objP R.toP κ wOff wLk wSh wIn L₁ L₂ _ LK L₁B L₂B _ hW hL h₁ h₂
    (ldKappaW_cons R.X.run _ _ _ κ L₃ [] h₃ (ldKappaW_nil _ _ _ κ)) hK hKc hR hB h₁B h₂B
    (ldKappaW_consLo R.XB.run _ _ _ κ L₃B [] h₃B (ldKappaW_nilA _ _ _ κ))

end
end Cb
