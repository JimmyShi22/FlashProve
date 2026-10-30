-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectParts.lean: the frame for an instance of the object with the terms that the library
builds for its sub-protocols: five parts, each with its own data and its own bundle of hypotheses;
the seams between them stated in the definitions' Lean types.

The object (`LdObj`, Cb/Obj/LdObject.lean) is one record with a configuration and, over it, the
sub-protocols of the proof system, as five terms.
Definitions, one statement (`Cb.Spec.ldParts_hyp`) and its proof. Generic; no protocol is given.
Why: the record `LdObjP` of Cb/Obj/LdObjectPlan.lean (the object with a plan for each of its two
tests) has dozens of fields, and `P.Hyp L` dozens of clauses, of five parts. Here record and
hypotheses are cut along the parts, so that each part can be built and proved by itself, and what
one part has to take from another is in its type. The parts follow the five fields `wf`, `linOff`,
`link`, `req`, `linOn` of `SubsR` (Hiop/RecSubs.lean).

The parts (data; bundle of hypotheses):
  `PWf F E`; `A.Hyp`: weights-formedness: the configuration, the preamble's parameters and the
    offline test's families (`W : LdOWf F E`), its blocks Bw. What the preamble leaves is
    `A.W.O.left`; `A.Bw.t a`: the long positions that the oracle message a, which it leaves, bears.
  `PLin A`; `Ln.Hyp`: the test for linear constraints at one instance over `A.W.O`: senders, the
    plan without a splitting with its tests, "the rest". Seam: it closes what weights-formedness
    left, within `A.Bw.t` (`needA`).
  `PLink Cf`; `Lk.Hyp`: the link with its closing, over the configuration alone.
  `PReq Cf`; `Rq.Hyp qa`: a request of segments; "on": what it leaves and the batch test's data.
    Seam: its formats end at the bound of the batch test (qa := `Bt.qaB`).
  `PBat Cf on`; `Bt.Hyp`: the test at N instances over `on.ol`: senders, the plan, the rest with its
    batch side.

Main names:
  `ldParts A Ln Lk Rq Bt z0 r0 dOff dOn : LdObjP F E`.
  `Spec.ldParts_hyp`: `Cf.OK L` and the five bundles ⇒ `(ldParts ..).Hyp L`. So `Cb.ldObjP_hyp`
    and `Cb.ldObjT_ok` apply, each under its
    other premises.

On `rZk`: what honest-verifier zero knowledge asks of the request's program, beside its hypotheses,
is `r.ZkS` (Cb/Req1/LdReqS.lean): `r.Zk` with the set of fresh facts closed, at each segment's entry
and before the last part, under join at one reading, a coarser reading, another type for the same
masks. `r.Zk`
gives `r.ZkS` (`ldReqS_of_zk`). Why: in this protocol's technical report (lean/CREDITS.md) a later
segment's sumcheck that ends at a map of the index has own masks from two sendings; by our reading
`r.Zk` cannot be met by that layout.
On the link's pair (`on0`, `on1`): two data fields of `PLink`, (`K.free`, `K.free`) where nothing is
said; `Lk.Hyp` asks `fitsK` and `foldK` at the pair. See the head of Cb/Obj/LdObject.lean.

Notation: `L`: a natural number (`LdCf.OK L`, Cb/Obj/LdObjectConf.lean, says that it bounds the
lists at the radius of decoding).

Limits: this file does not say that any bundle can be met. It says nothing on the compiler's own
conditions.

Terms: lean/GLOSSARY.md.
-/
/- Limits: no theorem of this library states that the hypotheses of `ldParts_hyp` can be met
   together. -/
import Cb.Obj.LdObjectPlan
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- Weights-formedness: the data. -/
structure PWf where
  W   : LdOWf F E
  [ne : Nonempty (Fin W.Cf.C₀.n)]
  Bw  : W.P.Blk

attribute [instance] PWf.ne

end

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- What is asked of weights-formedness. -/
structure PWf.Hyp (A : PWf F E) : Prop where
  lay    : ∀ a, ∃ l, A.W.lay a = A.W.Cf.lay l
  tie    : A.W.Tie
  wfLaws : A.W.P.Laws
  wfHyp  : A.Bw.Hyp
  wfBud  : ∀ l, l ≤ A.W.P.n → ∀ ρ, (A.Bw.sub l).P.bud ρ ∅
  wfNeed : ∀ l, l ≤ A.W.P.n → ∀ ρ U, (A.Bw.sub l).R.need ρ U = U

/-- The test at one instance, over what weights-formedness leaves: the data. -/
structure PLin (A : PWf F E) where
  εf  : ℕ
  Sn  : A.W.O.toC.P.Snd
  q₀  : Finset extNone.Pos → Prop
  dT  : A.W.O.toC.P.W0
  dT₀ : A.W.O.P.W0
  p   : LdLinPl A.W.O.toC
  TP  : LdLinPlT p
  b'  : p.S₂.O → ℕ

structure PLin.Hyp {A : PWf F E} (Ln : PLin A) : Prop where
  snd    : Ln.Sn.OK
  q₀e    : Ln.q₀ ∅
  fold   : A.W.O.toC.P.FoldErr A.W.O.on0 Ln.εf
  pyInj  : Function.Injective A.W.O.py
  rest   : ∀ sa m, Ln.p.restG.val sa (Ln.p.G₂.msg (A.W.O.toC.S.res (T := OMsg.Msg) Ln.p.kp₁ m)) =
    A.W.O.toC.rest sa (A.W.O.toC.aM m)
  saysA  : Ln.p.SaysA Ln.TP.Q'.base Ln.TP.fa
  left   : Ln.TP.Q'.OK
  leftQ  : ∀ V, Ln.TP.Q'.q V → Ln.p.S₂.qFam Ln.q₀ Ln.b' V
  /-- the seam: what the tests need of an oracle message that weights-formedness left, against what
  its encoding bears -/
  needA  : ∀ a, Ln.TP.D₁.need (Ln.TP.D₂.need Ln.b') (.inl (.inl (.inl a))) ≤ A.Bw.t a
  needW  : ∀ a, Ln.TP.D₁.need (Ln.TP.D₂.need Ln.b') (.inl (.inl (.inr a))) ≤ Ln.Sn.tW a
  needU  : ∀ a, Ln.TP.D₁.need (Ln.TP.D₂.need Ln.b') (.inl (.inr a)) ≤ Ln.Sn.tU a
  needO  : ∀ a, Ln.TP.D₁.need (Ln.TP.D₂.need Ln.b') (.inr a) ≤ Ln.Sn.tO a
  test₁  : Ln.TP.D₁.OK
  test₂  : Ln.TP.D₂.OK

/-- The link: the data. -/
structure PLink (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] where
  K   : Cf.LinkPar
  /-- the conditions on the two encoded indices at the link's first joint; if nothing is said:
  neither has a collision at its record's seed -/
  on0 : (K.P.D.X.Row → Fin Cf.C₀.n → E) → K.P.D.X.Rec → Prop := K.free
  on1 : (K.P.D.X.Row → Fin Cf.C₀.n → E) → K.P.D.X.Rec → Prop := K.free
  Sl  : K.P.Snd
  ε₀  : ℕ
  ε₁  : ℕ
  Kc  : K.P.Cl
  dK₂ : K.P.W2
  dK  : K.P.W0

structure PLink.Hyp {Cf : LdCf F E} [Nonempty (Fin Cf.C₀.n)] (Lk : PLink Cf) : Prop where
  sndK   : Lk.Sl.OK
  fitsK  : Lk.K.FitsK Lk.on0 Lk.on1
  foldK  : Lk.K.P.FoldErr Lk.on0 Lk.on1 Lk.ε₀ Lk.ε₁
  plInj  : Function.Injective Lk.K.pl
  bearK  : ∀ a, Lk.Kc.t ≤ Lk.Sl.t a
  close  : Lk.Kc.OK

/-- A request, and what it leaves: the data. -/
structure PReq (Cf : LdCf F E) where
  on  : LdOLd Cf
  Kr  : Type
  cr  : Cf.conf.PIdx × Cf.conf.Cells → Kr
  cr' : on.S.Msg × Cf.conf.PIdx → Kr
  r   : on.ol.Req cr cr'
  w₀  : Cf.conf.PIdx × Cf.conf.Cells
  qφ  : Finset (LdStage.start E Kr (on.ol.jReq cr)).J.E.Pos → Prop

/-- qa: the batch test's bound on the oracles that the request leaves: the seam. -/
structure PReq.Hyp {Cf : LdCf F E} (Rq : PReq Cf) (qa : Finset Rq.on.ol.toC.P.Ea.Pos → Prop) :
    Prop where
  lay    : ∀ a, ∃ l, Rq.on.lay a = Cf.lay l
  rHyp   : Rq.r.Hyp
  rZk    : Rq.r.ZkS
  rFmt   : Rq.r.Fmt (Rq.on.ol.fmtA Rq.cr Rq.qφ)
    (Rq.on.ol.fmtZ Rq.cr' (Rq.on.ol.P.q0 (Rq.on.ol.qaIn qa)))

/-- The test at N instances, over what a request leaves: the data. -/
structure PBat (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (on : LdOLd Cf) where
  N   : ℕ
  onB : (on.ol.P.D.X.Row → Fin Cf.C₀.n → E) → on.ol.P.D.X.Rec → Prop
  SnB : on.ol.toC.P.Snd
  qaB : Finset on.ol.toC.P.Ea.Pos → Prop
  εfB : ℕ
  dB  : on.ol.toC.P.W0
  dB₀ : on.ol.P.W0
  yB  : on.ol.toC.P.Ea.Str
  pB  : LdLinPl on.ol.toC
  TB  : LdLinPlT pB
  q₀B : Finset on.ol.toC.E₀.Pos → Prop
  bB' : pB.S₂.O → ℕ
  baB : on.ol.toC.Sa.O → ℕ
  tie' : on.ol.toC.P.Sh6 → TB.Q'.St × pB.S₂.Smp → (on.ol.toC.E₀.prod pB.S₂.ext).Str →
    pB.S₂.Wit × on.ol.toC.Wpa → Prop
  cA' : ChainA Unit (pB.S₂.jointCf TB.Q'.base) ldTrivJ
  same' : cA'.forget = TB.Q'.c
  x₀  : TB.St₁ × on.ol.toC.S.Smp
  y₀  : (on.ol.toC.E₀.prod on.ol.toC.S.ext).Str
  QV' : LdTcV N (⟨TB.Q', cA', same'⟩ : LdTcA pB.S₂ on.ol.toC.E₀ on.ol.toC.Wpa)
    ⟨on.ol.toC.P.Sh6, tie', pB.qB₂ N q₀B bB'⟩

structure PBat.Hyp {Cf : LdCf F E} [Nonempty (Fin Cf.C₀.n)] {on : LdOLd Cf} (Bt : PBat Cf on) :
    Prop where
  sndB   : Bt.SnB.OK
  apartB : Bt.SnB.Apart
  fitsB  : on.ol.Fits Bt.onB
  foldB  : on.ol.toC.P.FoldErr Bt.onB Bt.εfB
  pyInjB : Function.Injective on.ol.py
  monoB  : ∀ U V, V ⊆ U → Bt.qaB U → Bt.qaB V
  shared : Bt.pB.Shared
  restB  : ∀ sa m, Bt.pB.restG.val sa (Bt.pB.G₂.msg (on.ol.toC.S.res (T := OMsg.Msg) Bt.pB.kp₁ m)) =
    on.ol.toC.rest sa (on.ol.toC.aM m)
  saysAB : Bt.pB.SaysA Bt.TB.Q'.base Bt.TB.fa
  leftB  : Bt.TB.Q'.OK
  leftQB : ∀ V, Bt.TB.Q'.q V → Bt.pB.S₂.qFam Bt.q₀B Bt.bB' V
  leftKB : Bt.cA'.KB Bt.N (ldKeyU _) ldKeyT
  leftV  : Bt.QV'.OK
  tieC   : ∀ x y w, (on.ol.toC.P.V6 Bt.SnB Bt.qaB Bt.N).rel x y w →
    Bt.tie' w.1 (Bt.TB.D₂.outX (Bt.TB.D₁.outX (Bt.TB.fq (on.ol.toC.toSt x), on.ol.toC.toSmp x)))
      (Bt.TB.D₂.outY (Bt.TB.D₁.outY (on.ol.toC.toE.map y)))
      (Bt.TB.D₂.outW (Bt.TB.D₁.outW (on.ol.toC.toW w.2)))
  qaOK   : ∀ W, on.ol.toC.Sa.qFam Bt.q₀B Bt.baB W → Bt.qaB W
  oneN   : 1 ≤ Bt.N
  needNA : ∀ a,
    Bt.TB.D₁.need (Bt.TB.D₂.needV Bt.N (fun a => on.ol.toC.isSh a.1) Bt.bB')
        (.inl (.inl (.inl a))) ≤ Bt.baB a
  needNW : ∀ a,
    Bt.TB.D₁.need (Bt.TB.D₂.needV Bt.N (fun a => on.ol.toC.isSh a.1) Bt.bB')
        (.inl (.inl (.inr a))) ≤ Bt.SnB.tW a
  needNU : ∀ a,
    Bt.TB.D₁.need (Bt.TB.D₂.needV Bt.N (fun a => on.ol.toC.isSh a.1) Bt.bB') (.inl (.inr a)) ≤
      Bt.SnB.tU a
  needNO : ∀ a,
    Bt.TB.D₁.need (Bt.TB.D₂.needV Bt.N (fun a => on.ol.toC.isSh a.1) Bt.bB') (.inr a) ≤ Bt.SnB.tO a
  test₁B : Bt.TB.D₁.OK
  test₂B : Bt.TB.D₂.OK

/-- The five parts put together. -/
@[reducible] def ldParts (A : PWf F E) (Ln : PLin A) (Lk : PLink A.W.Cf)
    (Rq : PReq A.W.Cf) (Bt : PBat A.W.Cf Rq.on) (z0 : A.W.Cf.conf.PIdx) (r0 : Rq.on.S.Rnd)
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
  Wz := A.W.Cf.conf.PIdx
  piz := id
  Bz := Rq.on.ol.bEnd Rq.cr'
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

def Spec.ldParts_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Prop :=
  ∀ (A : PWf F E) (Ln : PLin A) (Lk : PLink A.W.Cf) (Rq : PReq A.W.Cf) (Bt : PBat A.W.Cf Rq.on)
      (z0 : A.W.Cf.conf.PIdx) (r0 : Rq.on.S.Rnd) (dOff : A.W.O.left.AMsg)
      (dOn : Rq.on.ol.left.AMsg) (L : ℕ),
    A.W.Cf.OK L → A.Hyp → Ln.Hyp → Lk.Hyp → Rq.Hyp Bt.qaB → Bt.Hyp →
    (ldParts A Ln Lk Rq Bt z0 r0 dOff dOn).Hyp L

theorem ldParts_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldParts_hyp F E :=
  fun _ _ _ Rq _ _ _ _ _ _ hC hA hn hk hr hb =>
    { r :=
        { base :=
            { rest :=
                { conf := hC, lay := ⟨hA.lay, hr.lay⟩, tie := hA.tie, wfLaws := hA.wfLaws,
                  wfHyp := hA.wfHyp, wfBud := hA.wfBud, wfNeed := hA.wfNeed, q₀e := hn.q₀e,
                  fold := hn.fold, pyInj := hn.pyInj
                  fitsK := hk.fitsK, foldK := hk.foldK, plInj := hk.plInj, bearK := hk.bearK,
                    rHyp := hr.rHyp, rZk := hr.rZk, rFmt := hr.rFmt, rEnd := Rq.on.ol.endOK Rq.cr',
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

end Cb
