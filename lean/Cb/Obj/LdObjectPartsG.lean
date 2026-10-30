-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPartsG.lean: the frame for an instance of the object with the terms that the library
builds for its sub-protocols, the request's last stage with any further witness (a ghost).

The object (`LdObj`, Cb/Obj/LdObject.lean) is one record with a configuration and, over it, the
sub-protocols of the proof system, as five terms.
Definitions, statements (`Cb.Spec.ldPartsG_hyp`, `Cb.Spec.ldPartsG_old`) and proofs. Generic; no
protocol is given.
Cb/Obj/LdObjectParts.lean cuts the record `LdObjP` and `P.Hyp L` into five parts. Its fourth part,
`PReq`, has a request that ends at the stage whose further witness is the prover encoded index
alone. A request that ends with the final batching of pending tensor rows carries more (a ghost
beside the prover encoded index; a base joint of its own). Here the fourth part is widened; the
other four are those of Cb/Obj/LdObjectParts.lean, unchanged.

Main names:
  `PReqG Cf`; `Rq.Hyp qa`: Wz, piz : Wz → PIdx, Bz: any further witness and last base joint; asked:
    `lay`, `rHyp`, `rZk`, `rFmt` (the formats end at the batch test's bound qa),
    `rEnd : on.ol.EndOK piz Bz` (the last base joint is tied to what the batch test starts from).
  `ldPartsG A Ln Lk Rq Bt z0 r0 dOff dOn : LdObjP F E` (z0 : `Rq.Wz`).
  `Spec.ldPartsG_hyp`: `Cf.OK L` and the five bundles ⇒ `(ldPartsG ..).Hyp L`.
  `Spec.ldPartsG_old`: `ldParts ..` is `ldPartsG ..` at `Rq.toG` (the case without a ghost), by
    definition.

On `rZk`: what honest-verifier zero knowledge asks of the request's program, beside its hypotheses,
is `r.ZkS` (Cb/Req1/LdReqS.lean): `r.Zk` with the set of fresh facts closed, at each segment's entry
and before the last part, under join at one reading, a coarser reading, another type for the same
masks. `r.Zk`
gives `r.ZkS` (`ldReqS_of_zk`). Why: in this protocol's technical report (lean/CREDITS.md) a later
segment's sumcheck that ends at a map of the index has own masks from two sendings; by our reading
`r.Zk` cannot be met by that layout.

Notation: `L`: a natural number (`LdCf.OK L`, Cb/Obj/LdObjectConf.lean, says that it bounds the
lists at the radius of decoding).

Limits: this file does not say that any bundle can be met.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectParts
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- A request whose last stage has any further witness, and what it leaves: the data. -/
structure PReqG (Cf : LdCf F E) where
  on  : LdOLd Cf
  Kr  : Type
  cr  : Cf.conf.PIdx × Cf.conf.Cells → Kr
  Wz  : Type
  piz : Wz → Cf.conf.PIdx
  Bz  : Rels Kr (on.ol.Cl × Cf.conf.Rec) Cf.conf.E0 (on.ol.S.Msg × Wz)
  r   : on.ol.ReqAt cr Wz Bz
  w₀  : Cf.conf.PIdx × Cf.conf.Cells
  qφ  : Finset (LdStage.start E Kr (on.ol.jReq cr)).J.E.Pos → Prop

structure PReqG.Hyp {Cf : LdCf F E} (Rq : PReqG Cf) (qa : Finset Rq.on.ol.toC.P.Ea.Pos → Prop) :
    Prop where
  lay    : ∀ a, ∃ l, Rq.on.lay a = Cf.lay l
  rHyp   : Rq.r.Hyp
  rZk    : Rq.r.ZkS
  rFmt   : Rq.r.Fmt (Rq.on.ol.fmtA Rq.cr Rq.qφ)
    (Rq.on.ol.fmtZAt Rq.Bz Rq.piz (Rq.on.ol.P.q0 (Rq.on.ol.qaIn qa)))
  rEnd   : Rq.on.ol.EndOK Rq.piz Rq.Bz

/-- The case without a ghost. -/
@[reducible] def PReq.toG {Cf : LdCf F E} (Rq : PReq Cf) : PReqG Cf :=
  ⟨Rq.on, Rq.Kr, Rq.cr, Cf.conf.PIdx, id, Rq.on.ol.bEnd Rq.cr', Rq.r, Rq.w₀, Rq.qφ⟩

/-- The five parts put together. -/
@[reducible] def ldPartsG (A : PWf F E) (Ln : PLin A) (Lk : PLink A.W.Cf)
    (Rq : PReqG A.W.Cf) (Bt : PBat A.W.Cf Rq.on) (z0 : Rq.Wz) (r0 : Rq.on.S.Rnd)
    (dOff : A.W.O.left.AMsg) (dOn : Rq.on.ol.left.AMsg) : LdObjP F E where
  W := A.W
  Bw := A.Bw
  εf := Ln.εf
  Sn := Ln.Sn
  q₀ := Ln.q₀
  dT := Ln.dT
  dT₀ := Ln.dT₀
  K := Lk.K
  on0K := Lk.on0
  on1K := Lk.on1
  Sl := Lk.Sl
  ε₀ := Lk.ε₀
  ε₁ := Lk.ε₁
  Kc := Lk.Kc
  dK₂ := Lk.dK₂
  dK := Lk.dK
  on := Rq.on
  N := Bt.N
  Kr := Rq.Kr
  cr := Rq.cr
  Wz := Rq.Wz
  piz := Rq.piz
  Bz := Rq.Bz
  r := Rq.r
  w₀ := Rq.w₀
  qφ := Rq.qφ
  onB := Bt.onB
  SnB := Bt.SnB
  qaB := Bt.qaB
  εfB := Bt.εfB
  dB := Bt.dB
  dB₀ := Bt.dB₀
  yB := Bt.yB
  z0 := z0
  r0 := r0
  dOff := dOff
  dOn := dOn
  p := Ln.p
  TP := Ln.TP
  b' := Ln.b'
  pB := Bt.pB
  TB := Bt.TB
  q₀B := Bt.q₀B
  bB' := Bt.bB'
  baB := Bt.baB
  tie' := Bt.tie'
  cA' := Bt.cA'
  same' := Bt.same'
  x₀ := Bt.x₀
  y₀ := Bt.y₀
  QV' := Bt.QV'

end

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldPartsG_hyp : Prop :=
  ∀ (A : PWf F E) (Ln : PLin A) (Lk : PLink A.W.Cf) (Rq : PReqG A.W.Cf) (Bt : PBat A.W.Cf Rq.on)
      (z0 : Rq.Wz) (r0 : Rq.on.S.Rnd) (dOff : A.W.O.left.AMsg) (dOn : Rq.on.ol.left.AMsg) (L : ℕ),
    A.W.Cf.OK L → A.Hyp → Ln.Hyp → Lk.Hyp → Rq.Hyp Bt.qaB → Bt.Hyp →
    (ldPartsG A Ln Lk Rq Bt z0 r0 dOff dOn).Hyp L

def ldPartsG_old : Prop :=
  ∀ (A : PWf F E) (Ln : PLin A) (Lk : PLink A.W.Cf) (Rq : PReq A.W.Cf)
      (Bt : PBat A.W.Cf Rq.on) (z0 : A.W.Cf.conf.PIdx) (r0 : Rq.on.S.Rnd)
      (dOff : A.W.O.left.AMsg) (dOn : Rq.on.ol.left.AMsg),
    ldParts A Ln Lk Rq Bt z0 r0 dOff dOn = ldPartsG A Ln Lk Rq.toG Bt z0 r0 dOff dOn

end
end Spec

theorem ldPartsG_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldPartsG_hyp F E :=
  fun _ _ _ _ _ _ _ _ _ _ hC hA hn hk hr hb =>
    { r :=
        { base :=
            { rest :=
                { conf := hC, lay := ⟨hA.lay, hr.lay⟩, tie := hA.tie, wfLaws := hA.wfLaws,
                  wfHyp := hA.wfHyp, wfBud := hA.wfBud, wfNeed := hA.wfNeed, q₀e := hn.q₀e,
                  fold := hn.fold, pyInj := hn.pyInj
                  fitsK := hk.fitsK, foldK := hk.foldK, plInj := hk.plInj, bearK := hk.bearK,
                    rHyp := hr.rHyp, rZk := hr.rZk, rFmt := hr.rFmt, rEnd := hr.rEnd,
                    fitsB := hb.fitsB, foldB := hb.foldB, pyInjB := hb.pyInjB, monoB := hb.monoB }
              snds := ⟨hn.snd, hk.sndK, hb.sndB, hb.apartB⟩ }
          rest := hn.rest, saysA := hn.saysA, left := hn.left, leftQ := hn.leftQ, needA := hn.needA,
            needW := hn.needW, needU := hn.needU, needO := hn.needO
          shared := hb.shared, restB := hb.restB, saysAB := hb.saysAB, leftB := hb.leftB,
            leftQB := hb.leftQB, leftKB := hb.leftKB, leftV := hb.leftV, tieC := hb.tieC,
            qaOK := hb.qaOK, oneN := hb.oneN
          needNA := hb.needNA, needNW := hb.needNW, needNU := hb.needNU, needNO := hb.needNO }
      close := hk.close, test₁ := hn.test₁, test₂ := hn.test₂,
        test₁B := hb.test₁B, test₂B := hb.test₂B }

theorem ldPartsG_old (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldPartsG_old F E :=
  fun _ _ _ _ _ _ _ _ _ => rfl

end Cb
