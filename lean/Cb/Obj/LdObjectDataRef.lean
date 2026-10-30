-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectDataRef.lean: book-keeping for the hypotheses of a holographic IOP: hypotheses on the
object's data at the reference request.

Its statements are implications between records of hypotheses.
Definitions, statements and proofs: an assembly.
The object, "on data" and the request's program: the head of Cb/Obj/LdObjectData.lean.
Cb/Obj/LdObjectData.lean has the object with the hypotheses of `Z.Hyp p L`, among them properties of
the request's program r, a parameter with four properties: `r.Hyp` (its moves), `r.ZkS` (its masks),
`r.Fmt` (its formats), `EndOK` (its last base joint is tied to what the test starts from); and of
the sender `Zw.D` of weights-formedness. Cb/Req1/LdReqRefFinal.lean has the reference request as a
term (`ldReqRef`, Cb/Req1/LdReqRef.lean) with one record of conditions (`LdReqRefD`: the model's
side; the protocol's side; where the masks come from; readers and demands; numbers). Here the term
is put in. `R : LdORE F E Kc` (Cb/Obj/LdObjectReqEnd.lean) is the data of a request's end and of the
test that follows.

Main names:
  `LdReqPack F E`: the configuration; what a request leaves and the test's data ("on"); the core's
    type and the core at the first stage; the last stage's further witness, where the prover encoded
    index stands in it, its base joint; the program r; the demands at the two ends.
  `ldRefPack R ..`: the same for the reference request: on := the datum `R.O` read off the final
    batching.
  `Spec.ldObjRef_good`: for pp the characteristic of E, `LdReqRefD ..` → `(ldRefPack ..).Good`.
  `Spec.ldObjRef_own`: for pp the characteristic of E, one equation that says which terms are in D
    (`D.pack = ldRefPack ..`: whoever builds D from R has it by definition; it is a hypothesis here,
    as the two equations of Cb/Obj/LdObjectData.lean), `D.HypOwn₀` and `LdReqRefD ..` give
    `D.HypOwn`.
  `Z.HypRef ..`: `Z.Hyp` with `own` replaced by these three.
  `Spec.ldObjRef_hyp`: for p the characteristic of E, `Z.HypRef ..` → `Z.Hyp p L`. So `Z.R.Hyp L`
    (`Cb.ldObjZ_hyp`) and all that follows from it.

Notation: `L` in `Z.HypRef p L ..`, `Z.Hyp p L`: a natural number (`LdCf.OK L`,
Cb/Obj/LdObjectConf.lean, says that it bounds the lists at the radius of decoding); `core`: the core
at the first stage, a map to the core's type `Kc`; `first`: the first sending: the data (`LdSendD`,
Cb/Req1/LdSegKit.lean); `more`: a list of moves behind the first sending, up to the stage `a₁`
(`LdProg`, Cb/Req1/LdSeg.lean); `hm`: a proof that each move of `more` is a sending or a step; `Ls`
(`L` in `ldRefPack`, `LdReqRefD ..`): a list of reference segments, up to the stage `b` (`LdRefL`,
Cb/Req1/LdReqRef.lean); `T`: the last segment: the data (`LdRefT`, the same file); `κ`: a number in
`ℝ≥0∞` (the request's record `LdReqRefD ..` asks, in `bFirst` to `bLast`, that its errors are below
it, in the sense of `Err.Below`, Iop/InteractiveOracleProof.lean).

Limits: beside `LdReqRefD` this is still asked of the request: in `Z.R.HypPl`
(Cb/Obj/LdObjectPlanRows.lean) the clauses that tie the plan of the batch test to the request's last
claims (conditions on the datum `R.O`: Cb/Obj/LdObjectReqEnd.lean: `ldORE_rest`, `ldORE_more` say
what it is); countability of the program's shapes, where a top asks it.
`LdReqRefD` is not all on data: what in it is still a property of terms is listed in the heads of
Cb/Obj/LdObjectData.lean (Limits) and Cb/Req1/LdReqRefFinal.lean.
Six clauses on the sender `Zw.D` of weights-formedness are not on data: it is a free value with laws
(Cb/Ld/LdWfEnd.lean: `Rest0`, `Rest1`).
No instance that meets the hypotheses of `ldObjRef_hyp` is part of this library; as far as the
library shows, this theorem may hold of nothing.
On `rZk`. What honest-verifier zero knowledge asks of the request's program is `r.ZkS`
(Cb/Req1/LdReqS.lean), beside its hypotheses (`r.Hyp`): `r.Zk` with the set of fresh facts closed,
at each segment's entry and before the last part, under join at one reading, a coarser reading,
another type for the same masks. `r.Zk` gives `r.ZkS` (`ldReqS_of_zk`). Why: in
this protocol's technical report (lean/CREDITS.md) a later segment's sumcheck that ends at a map of
the index has own masks from two sendings; by our reading `r.Zk` cannot be met by that layout.
Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectData
import Cb.Req1.LdReqRefFinal
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

/-- What the object's data hold of a request. -/
structure LdReqPack (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Type 1 where
  Cf  : LdCf F E
  on  : LdOLd Cf
  Kr  : Type
  cr  : Cf.conf.PIdx × Cf.conf.Cells → Kr
  Wz  : Type
  piz : Wz → Cf.conf.PIdx
  Bz  : Rels Kr (on.ol.Cl × Cf.conf.Rec) Cf.conf.E0 (on.ol.S.Msg × Wz)
  r   : on.ol.ReqAt cr Wz Bz
  qφ  : Finset (LdStage.start E Kr (on.ol.jReq cr)).J.E.Pos → Prop
  qi  : Finset on.ol.left.El.Pos → Prop

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The four properties. -/
structure LdReqPack.Good (P : LdReqPack F E) : Prop where
  rHyp : P.r.Hyp
  rZk  : P.r.ZkS
  rFmt : P.r.Fmt (P.on.ol.fmtA P.cr P.qφ) (P.on.ol.fmtZAt P.Bz P.piz P.qi)
  rEnd : P.on.ol.EndOK P.piz P.Bz

/-- that part of the object's data -/
@[reducible] def LdObjD.pack (T : LdObjD F E) : LdReqPack F E :=
  ⟨T.W.Cf, T.on, T.Kr, T.cr, T.Wz, T.piz, T.Bz, T.r, T.qφ, T.qiB⟩

/-- The reference request's. -/
@[reducible] def ldRefPack {Kc : Type} (R : LdORE F E Kc)
    (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (a₁ : LdStage E Kc)
    (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
    (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b)
    (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
    (q : Finset R.z.J.E.Pos → Prop) : LdReqPack F E :=
  ⟨R.Cf, R.O.d, Kc, core, R.Cf.conf.PIdx × R.G, Prod.fst, R.bEnd,
    ldReqRef R first a₁ more hm b L T, qφ, q⟩

/-- the clauses of `HypOwn` that are not the request's -/
structure LdObjD.HypOwn₀ (T : LdObjD F E) : Prop where
  lay    : T.LayOK
  q₀e    : T.q₀ ∅
  fold   : T.W.O.toC.P.FoldErr T.W.O.on0 T.εf
  pyInj  : Function.Injective T.W.O.py
  fitsK  : T.K.FitsK T.on0K T.on1K
  foldK  : T.K.P.FoldErr T.on0K T.on1K T.ε₀ T.ε₁
  plInj  : Function.Injective T.K.pl
  bearK  : ∀ a, T.Kc.t ≤ T.Sl.t a
  fitsB  : T.on.ol.Fits T.onB
  foldB  : T.on.ol.toC.P.FoldErr T.onB T.εfB
  pyInjB : Function.Injective T.on.ol.py
  monoB  : ∀ U V, V ⊆ U → T.qaB U → T.qaB V

/-- `Z.Hyp` at the reference request. -/
structure LdObjZ.HypRef (Z : LdObjZ F E) (p L : ℕ) {Kc : Type} (R : LdORE F E Kc)
    (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (a₁ : LdStage E Kc)
    (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
    (Ls : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b)
    (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
    (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) : Prop where
  /-- which terms are in `Z.R` -/
  wfIs  : (⟨Z.R.W, Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Z.Zw.W, Z.Zw.G.B⟩
  sndIs : Z.R.toLdObjD = Z.R.toLdObjD.std Z.Y
  reqIs : Z.R.toLdObjD.pack = ldRefPack R core first a₁ more hm b Ls T qφ q
  /-- conditions: weights-formedness, the standard senders, the object's own clauses that are not
  the request's -/
  wfOK  : Z.Zw.OK p L
  sndOK : Z.Y.Hyp
  own₀  : Z.R.toLdObjD.HypOwn₀
  /-- the request: the model's side, the protocol's side, the masks, readers and demands, numbers -/
  req   : LdReqRefD p R core first a₁ more hm b Ls T qφ q κ
  pl    : Z.R.HypPl
  /-- the seven tests -/
  pK    : Z.R.Kc.run.Pre Z.twK
  p₁    : Z.R.TP₀.D₁.Pre Z.tw₁
  p₂    : Z.R.TP₀.D₂.Pre Z.tw₂
  p₃    : Z.R.X.run.Pre Z.tw₃
  p₁B   : Z.R.TB₀.D₁.Pre Z.tw₁B
  p₂B   : Z.R.TB₀.D₂.Pre Z.tw₂B
  p₃B   : Z.R.XB.run.Pre Z.tw₃B

end

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldObjRef_good : Prop :=
  ∀ (Kc : Type) (pp : ℕ) [CharP E pp] (R : LdORE F E Kc)
      (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (a₁ : LdStage E Kc)
      (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞),
    LdReqRefD pp R core first a₁ more hm b L T qφ q κ →
    (ldRefPack R core first a₁ more hm b L T qφ q).Good

def ldObjRef_own : Prop :=
  ∀ (Kc : Type) (pp : ℕ) [CharP E pp] (D : LdObjD F E) (R : LdORE F E Kc)
      (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (a₁ : LdStage E Kc)
      (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞),
    D.pack = ldRefPack R core first a₁ more hm b L T qφ q → D.HypOwn₀ →
    LdReqRefD pp R core first a₁ more hm b L T qφ q κ → D.HypOwn

def ldObjRef_hyp : Prop :=
  ∀ (Kc : Type) (p : ℕ) [CharP E p] (Z : LdObjZ F E) (L : ℕ) (R : LdORE F E Kc)
      (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (a₁ : LdStage E Kc)
      (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞),
    Z.HypRef p L R core first a₁ more hm b Ls T qφ q κ → Z.Hyp p L

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldObjRef_good : Spec.ldObjRef_good F E := by
  intro Kc pp _ R core first a₁ more hm b L T qφ q κ h
  have hL : L.OK pp := (ldReqModel_list E Kc _ _ _ L pp).2 ⟨h.model.segs, h.proto.segs⟩
  have hT : T.OK pp := (ldReqModel_tail F E Kc R b T pp).2 ⟨h.model.tail, h.proto.tail⟩
  obtain ⟨Rd, Rr, hRd, hB⟩ := h.layB
  obtain ⟨px', φ₁, φb, f1, f2, f3, ρ, r₁, q₀, e1, -, e2, e3, e4⟩ := h.fmt
  refine ⟨ldReqModel_hyp F E Kc pp R _ first a₁ more hm b L T h.model h.proto,
    ldReqRefLayJ F E Kc pp R _ first a₁ more hm b L T Rd Rr hL hT h.proto.deg h.proto.ev h.proto.tie
      h.own hRd h.lay h.layT hB,
    ?_,
    ldOREAt_end F E Kc R⟩
  refine ⟨_, φ₁, φb,
    ldFmt_send E Kc _ _ _ (LdStage.start E Kc (R.O.jReq core)) first ⟨id, id⟩
      Prod.snd Prod.fst px' qφ h.proto.hFirst f1,
    f2,
    ldReqRefK_segsFmt E Kc _ _ _ _ _ _ L φ₁ φb (ldReqRefFmtL_segs E Kc pp _ _ _ L φ₁ φb hL f3),
    ?_⟩
  refine ldReqRefK_asSub E Kc _ _ _ _ _ (T.tail.app R.lastP) φb _
    (ldProg_app_fmt E Kc _ _ _ _ _ _ _ _ φb _ _ ?_ (ldOREFmt_last F E Kc R q))
  exact ldReqRefFmtP_tail F E Kc pp _ _ _ R b T φb _ ⟨id, id⟩ ρ r₁ Prod.fst q₀ hT.body e1 e2 e3 e4

/-- `Good` carried along an equation of packs; used at the reference request's pack -/
theorem ldObjRef_at {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (P P' : LdReqPack F E) (e : P = P') (h : P'.Good) : P.Good := e ▸ h

theorem ldObjRef_own : Spec.ldObjRef_own F E := by
  intro Kc pp _ D R core first a₁ more hm b L T qφ q κ e h₀ h
  have g : D.pack.Good :=
    ldObjRef_at _ _ e (ldObjRef_good F E Kc pp R core first a₁ more hm b L T qφ q κ h)
  exact { lay := h₀.lay, q₀e := h₀.q₀e, fold := h₀.fold, pyInj := h₀.pyInj, fitsK := h₀.fitsK,
          foldK := h₀.foldK, plInj := h₀.plInj, bearK := h₀.bearK, rHyp := g.rHyp, rZk := g.rZk,
          rFmt := g.rFmt, rEnd := g.rEnd, fitsB := h₀.fitsB, foldB := h₀.foldB,
          pyInjB := h₀.pyInjB, monoB := h₀.monoB }

theorem ldObjRef_hyp :
    Spec.ldObjRef_hyp F E := fun Kc p _ Z _ R core first a₁ more hm b Ls T qφ q κ h =>
  { wfIs := h.wfIs, sndIs := h.sndIs, wfOK := h.wfOK, sndOK := h.sndOK,
    own := ldObjRef_own F E Kc p Z.R.toLdObjD R core first a₁ more hm b Ls T qφ
        q κ h.reqIs h.own₀ h.req,
    pl := h.pl, pK := h.pK, p₁ := h.p₁, p₂ := h.p₂, p₃ := h.p₃, p₁B := h.p₁B,
    p₂B := h.p₂B, p₃B := h.p₃B }

end
end Cb
