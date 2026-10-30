-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectTerms.lean: the terms of the several parts of this library put into the object, one
by one.

The object is one record with a configuration and, over it, the sub-protocols of the proof system,
as five terms.
Definitions and one statement (`Cb.Spec.ldObjT_ok`); its proof is in
Cb/Obj/LdObjectTermsProofs.lean.
Cb/Obj/LdObject.lean has the object (`LdObj`) with five terms as parameters, each with an "OK" of
its kind. A term is a sub-protocol as a value: a reduction with its honest side, extractor and
numbers. Here the parameters are replaced by the terms that the several parts have built, and each
OK is derived from the blocks' own hypotheses.

What is put in: all five.
  wf: the preamble of weights-formedness of Cb/Ld/LdWf.lean (Bw : blocks over `W.P`), tied to the
    test's data by Cb/Obj/LdObjectWf.lean (`W : LdOWf F E`; what the preamble leaves is `W.O.left`).
  lin: the test at one instance with its closing as a term: Cb/Obj/LdObjectLinFull.lean
    (`W.O.full`), within "at most t positions of the index, at most `Bw.t a` long positions of each
    oracle message a that the preamble left".
  link: the link on chains with its closing: Cb/Obj/LdObjectLinkFull.lean (`K.full`); see "On the
    link's pair" below.
  req: a request built of segments: Cb/Obj/LdObjectReqSeg.lean (`termAt r piz w₀`), to a last stage
    with any further witness Wz and any base joint Bz that is tied to what the batch test starts
    from (`EndOK`): so that the core of a chain with a range check has room (a ghost beside the
    prover encoded index).
  linB: the test at N instances on chains of batch links: Cb/Obj/LdObjectOnBTerm.lean (`termT`),
    under any condition onB on the index that holds wherever the list's item speaks.

Main names:
  `T.Hyp L` (`T : LdObjT F E`): the blocks' own hypotheses, part by part.
  `Spec.ldObjT_ok`: `T.Hyp L` ⇒ `T.obj.OK L`. So `Cb.ldObj_hyp` and `Cb.ldObj_props`
    apply to `T.obj`, each under its other premises.


Why `T.LayOK`: no proof in Cb/Obj/LdObjectTermsProofs.lean uses it. It is a clause of `T.Hyp` all
the same: "heldB reads the layout only" (`Cf.OK`) and "the keys describe the index" (the laws of
weights-formedness) can hold together only if no key depends on an entry off `Cf.lay`: such a key
could be pushed out of its table without changing what "held" returns. The converse is not needed: a
place that "held" reads and no key reads is an entry that the index set leaves free. Likewise
online: a tensor row that read a place off `Cf.lay` would speak of an entry that is no part of the
index.
The two lines on budgets (`fitOff`, `fitOn` of `LdObj.OK`, Cb/Obj/LdObject.lean) are derived in the
proof: offline by `Cb.ldOWf_fit` (the test's tail keeps within what the preamble's words bear),
online by `Cb.ldOS_fitAt`.
On `plan`: what is asked of the closing Qt of the offline test is that it is in order behind the
test's core and the step without rounds (`Q.OkBehind`, Cb/Ld/LdLinCloseAlt.lean), not by itself
(`Q.OK`: every link has the whole bundle). `Q.OK` gives it (`ldAlt_of_ok`). Why: the closing of this
protocol's technical report (lean/CREDITS.md) holds a masked link, the splitting of the fold's row,
which is honest-verifier zero knowledge only behind the rounds that sent its mask
(Cb/Ld/LdLinClosePlanP.lean, Cb/Ld/LdLinCloseDemandPA.lean). The conditions `cOk`, `cOkV` on the
closing cZ of the test at N instances are of the same form (`OkFrom`, `OkFromV` behind the core's
chains).
On `rZk`: what zero knowledge asks of the request's program, beside its hypotheses, is `r.ZkS`
(Cb/Req1/LdReqS.lean): `r.Zk` with the set of fresh facts closed, at each segment's entry and before
the last part, under join at one reading, a coarser reading, another type for the same masks. `r.Zk`
gives `r.ZkS` (`ldReqS_of_zk`). Why: in the technical report a later segment's sumcheck that ends
at a map of the index has own masks from two sendings; by our reading `r.Zk` cannot be met by that
layout.
On the link's pair (`on0K`, `on1K`): two data fields of `LdObjD`, (`K.free`, `K.free`) where nothing
is said; the link's term is `K.fullAt on0K on1K ..` (Cb/Obj/LdObjectLinkPairFull.lean; at (`K.free`,
`K.free`) it is `K.full`, by definition); `HypRest` asks `fitsK` (the object's condition gives the
pair) and `foldK` at the pair. See the head of Cb/Obj/LdObject.lean.

Notation: `L`: a natural number (`LdCf.OK L`, Cb/Obj/LdObjectConf.lean, says that it bounds the
lists at the radius of decoding).

Limits:
One level lower, still parameters with a property: the whole tests on groups inside the closings
(plans Qt, Kc); the closing cZ of the batch test (a chain of batch links, with six named
conditions); the request r itself (its moves, `r.Hyp`, `r.ZkS`, `r.Fmt`: formats move by move,
Cb/Req1/LdSegFormat.lean); the blocks Bw of weights-formedness (`Bw.Hyp`); all senders.
Online the request is not built, and its "conditions" are the security properties (by reading).
`r.Hyp` at a move "sub a b c" is `c.AllB` for any chain c: completeness and
round-by-round knowledge soundness, link by link, are assumed of a parameter; at a move "fold D l"
it asks of any link l the whole bundle `GoodT`, honest-verifier zero knowledge included: that l is
the proximity test that closes each segment; a move "step" asks `StepT` (its clauses acc, know: the
arithmetization) (`LdMv.Hyp`, Cb/Req1/LdSeg.lean). For every first sending d and every chain c to
the last stage there is a request with `r.Hyp` ↔ `d.Hyp` ∧ `c.AllB`. So "an accepted proof implies
Rno" is, online, assumed at the level of the oracle reduction: that the claim on the instance x is
about the extracted index is not derived from data. True of this generic theorem (`ldObjT_ok`).



Proved are: the composition, the batch test
behind the request, the offline phase, the link, the compilation, each under the hypotheses of its
statement. The cure in Lean is the reference request as a term: Cb/Req1/LdReqRef*.lean,
Cb/Obj/LdObjectDataRef.lean. The term stands. Among what is still a
property of terms there: each closing's fold link, senders, entry and exit steps, the model's side,
where the masks come from. No theorem of this library states that the hypotheses of `ldReqRefFinal`
(Cb/Req1/LdReqRefFinal.lean) can be met together.


`T.Hyp L` is a long conjunction of hypotheses of different parts. That they can be met together is
not shown in this file. No theorem of this library states that the hypotheses of `ldObjT_ok` or
`ldObjT_hyp` can be met together. As far as this file shows, these hypotheses have not been met by a
request that says something. By itself the theorem says that the parts' terms fit (types and joints
meet, nothing else is needed), not that a protocol with these properties exists.




This file exhibits no instance that meets the whole of `T.Hyp`. Clauses of `T.Hyp` were
unsatisfiable as first written and have been mended: each asked a condition at all states, of data
that a state is free to choose. The supports of the filed forms are now public and enforced at every
use: so the clause `own` of `wfHyp` (`OwnOK`, Cb/Ld/LdBatt.lean; among its fields "no incoming mask
form reads an own entry of the batching") is equivalent, if there is a record (`Nonempty C.Rec`), to
a condition on places alone (`Spec.ldWfOwn_ok`, `Spec.ldWfOwn_conv`, Cb/Ld/LdWfOwn.lean). The rows
that the lookups of weights-formedness file now stand in its last claims as vectors of public
lengths: if they were a list of any length, the clause `rows` of `T.Hyp` (the offline plan says the
rows and `Ab`, at all states: `LdLinC.Says`, Cb/Ld/LdLinClosePre.lean) could be met by no plan with
a fixed finite set of rows. As far as this file shows, every theorem that assumes `T.Hyp` may hold
of nothing.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectProofs
import Cb.Obj.LdObjectWf
import Cb.Obj.LdObjectLinFullProofs
import Cb.Obj.LdObjectLinFullA
import Cb.Obj.LdObjectLinkFull
import Cb.Obj.LdObjectLinkPairFull
import Cb.Obj.LdObjectReqSeg
import Cb.Obj.LdObjectReqSegS
import Cb.Obj.LdObjectOnBTermProofs
import Cb.Req1.LdSegFormat
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- An `LdOL`, as data over its own configuration. -/
@[reducible] def LdOL.d {F E : Type} [Field F] [Field E] [Algebra F E] (O : LdOL F E) :
    LdOLd O.Cf :=
  { S := O.S, Cl := O.Cl, Y := O.Y, finY := O.finY, klo := O.klo, l := O.l, lay := O.lay,
    py := O.py, g := O.g, ψ := O.ψ, τ := O.τ, restM := O.restM, more := O.more, e' := O.e',
    t := O.t, NW := O.NW, SdW := O.SdW, iW := O.iW, lW := O.lW, NU := O.NU, SdU := O.SdU,
    iU := O.iU, lU := O.lU, NO := O.NO, SdO := O.SdO, iO := O.iO, lO := O.lO }

/-- The object with the terms that the library builds for its sub-protocols: the data, without the
closings of the two tests for linear constraints. -/
structure LdObjD (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] where
  /-- the configuration, the preamble of weights-formedness and the offline test's data -/
  W   : LdOWf F E
  [ne : Nonempty (Fin W.Cf.C₀.n)]
  Bw  : W.P.Blk
  /-- the offline test -/
  εf  : ℕ
  Sn  : W.O.toC.P.Snd
  q₀  : Finset extNone.Pos → Prop
  dT  : W.O.toC.P.W0
  dT₀ : W.O.P.W0
  /-- the link with its closing -/
  K   : W.Cf.LinkPar
  /-- the conditions on the two encoded indices at the link's first joint; if nothing is said:
  neither has a collision at its record's seed -/
  on0K : (K.P.D.X.Row → Fin W.Cf.C₀.n → E) → K.P.D.X.Rec → Prop := K.free
  on1K : (K.P.D.X.Row → Fin W.Cf.C₀.n → E) → K.P.D.X.Rec → Prop := K.free
  Sl  : K.P.Snd
  ε₀  : ℕ
  ε₁  : ℕ
  Kc  : K.P.Cl
  dK₂ : K.P.W2
  dK  : K.P.W0
  /-- the online phase: what a request leaves and the batch test's data; a request of segments -/
  on  : LdOLd W.Cf
  N   : ℕ
  Kr  : Type
  cr  : W.Cf.conf.PIdx × W.Cf.conf.Cells → Kr
  /-- the last stage of the request: its further witness (the prover encoded index, and room for the
  core of a chain with a range check), where the prover encoded index stands in it, its base
  joint -/
  Wz  : Type
  piz : Wz → W.Cf.conf.PIdx
  Bz  : Rels Kr (on.ol.Cl × W.Cf.conf.Rec) W.Cf.conf.E0 (on.ol.S.Msg × Wz)
  r   : on.ol.ReqAt cr Wz Bz
  w₀  : W.Cf.conf.PIdx × W.Cf.conf.Cells
  qφ  : Finset (LdStage.start E Kr (on.ol.jReq cr)).J.E.Pos → Prop
  /-- the test at N instances -/
  onB : (on.ol.P.D.X.Row → Fin W.Cf.C₀.n → E) → on.ol.P.D.X.Rec → Prop
  SnB : on.ol.toC.P.Snd
  qaB : Finset on.ol.toC.P.Ea.Pos → Prop
  εfB : ℕ
  dB  : on.ol.toC.P.W0
  dB₀ : on.ol.P.W0
  yB  : on.ol.toC.P.Ea.Str
  /-- fixed values -/
  z0   : Wz
  r0   : on.S.Rnd
  dOff : W.O.left.AMsg
  dOn  : on.ol.left.AMsg

attribute [instance] LdObjD.ne

/-- The object with the terms that the library builds for its sub-protocols: the data. The two
closings are parameters: the plan Qt of whole tests after the test at one instance; the chain cZ of
batch links after the test at N instances. -/
structure LdObjT (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    extends LdObjD F E where
  Qt  : LdTc W.O.toC.S W.O.toC.E₀ W.O.toC.Wpa
  fq  : W.O.toC.St6 → Qt.St
  VT  : JV N LdLinP.JT
  cZ  : ChainV Unit N (on.ol.toC.P.V6 SnB qaB N) VT
  kT  : JKey LdLinP.JT

namespace LdObjD
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (T : LdObjD F E)

/-- The bound on what the test at N instances reads. -/
def qiB : Finset T.on.ol.left.El.Pos → Prop := T.on.ol.P.q0 (T.on.ol.qaIn T.qaB)

/-- The three layouts agree: the places from which the offline and the online tensor rows (and the
keys of weights-formedness) read the index matrix lie on the configuration's layout, the places that
"held" and the link read. -/
structure LayOK : Prop where
  off : ∀ a, ∃ l, T.W.lay a = T.W.Cf.lay l
  on  : ∀ a, ∃ l, T.on.lay a = T.W.Cf.lay l

/-- What the senders of the two tests and of the link are asked: four clauses. (The senders inside
weights-formedness and inside a request are in those parts' own records.) -/
structure HypSnd : Prop where
  snd    : T.Sn.OK
  sndK   : T.Sl.OK
  sndB   : T.SnB.OK
  apartB : T.SnB.Apart

/-- The blocks' own hypotheses, part by part, without those on closings and on these senders, but
for `bearK`. -/
structure HypRest (L : ℕ) : Prop where
  conf   : T.W.Cf.OK L
  /-- No proof uses this clause: it is named so that it stands in the last theorem's text and every
  instance has to meet it. -/
  lay    : T.LayOK
  /-- weights-formedness -/
  tie    : T.W.Tie
  wfLaws : T.W.P.Laws
  wfHyp  : T.Bw.Hyp
  wfBud  : ∀ l, l ≤ T.W.P.n → ∀ ρ, (T.Bw.sub l).P.bud ρ ∅
  wfNeed : ∀ l, l ≤ T.W.P.n → ∀ ρ U, (T.Bw.sub l).R.need ρ U = U
  /-- the offline test -/
  q₀e    : T.q₀ ∅
  fold   : T.W.O.toC.P.FoldErr T.W.O.on0 T.εf
  pyInj  : Function.Injective T.W.O.py
  /-- the link -/
  fitsK  : T.K.FitsK T.on0K T.on1K
  foldK  : T.K.P.FoldErr T.on0K T.on1K T.ε₀ T.ε₁
  plInj  : Function.Injective T.K.pl
  bearK  : ∀ a, T.Kc.t ≤ T.Sl.t a
  /-- a request -/
  rHyp   : T.r.Hyp
  rZk    : T.r.ZkS
  rFmt   : T.r.Fmt (T.on.ol.fmtA T.cr T.qφ) (T.on.ol.fmtZAt T.Bz T.piz T.qiB)
  rEnd   : T.on.ol.EndOK T.piz T.Bz
  /-- the test at N instances -/
  fitsB  : T.on.ol.Fits T.onB
  foldB  : T.on.ol.toC.P.FoldErr T.onB T.εfB
  pyInjB : Function.Injective T.on.ol.py
  monoB  : ∀ U V, V ⊆ U → T.qaB U → T.qaB V

/-- The two together. -/
structure HypD (L : ℕ) : Prop where
  rest : T.HypRest L
  snds : T.HypSnd

end LdObjD

namespace LdObjT
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (T : LdObjT F E)

/-- The five terms. -/
def wfT : T.W.O.WfT Unit :=
  ⟨T.W.P.Wp, Prod.fst, (T.Bw.p0, ()), T.W.P.lastB, T.Bw.link.R, T.Bw.link.H,
    T.Bw.link.ext, T.Bw.link.P⟩
def linT : T.W.O.LinT :=
  ⟨T.W.O.full T.Sn T.εf T.Qt T.fq T.dT,
    T.W.O.hFull0 T.Sn T.εf T.Qt T.fq T.dT,
    T.W.O.extF T.Sn T.εf T.Qt T.fq T.dT T.dT₀,
    T.W.O.numsF0 T.Sn T.εf T.Qt T.fq T.dT,
    T.W.O.S.qFam (E₀ := T.W.O.P.ix) (fun V => V.card ≤ T.W.O.t) T.Bw.t⟩
def linkT : T.K.Tail := T.K.fullAt T.on0K T.on1K T.Sl T.ε₀ T.ε₁ T.Kc T.dK₂ T.dK
def reqT : T.on.ol.ReqT T.Kr := T.on.ol.termAt T.r T.piz T.w₀
def linB : T.on.ol.LinBT T.N :=
  T.on.ol.termT T.onB T.SnB T.qaB T.εfB T.N T.cZ T.dB T.dB₀

/-- The object. -/
def obj : LdObj F E where
  Cf := T.W.Cf
  off := T.W.O.d
  on := T.on
  K := T.K
  on0K := T.on0K
  on1K := T.on1K
  N := T.N
  Kw := Unit
  Kr := T.Kr
  wf := T.wfT
  lin := T.linT
  link := T.linkT
  req := T.reqT
  linB := T.linB
  cw := fun _ => ()
  cr := T.cr
  z0 := T.z0
  r0 := T.r0
  dOff := T.dOff
  dOn := T.dOn

open Classical in
/-- The blocks' own hypotheses: those of `LdObjD.HypD`, and those on the closings of the link and of
the two tests. -/
structure Hyp (L : ℕ) : Prop where
  base   : T.toLdObjD.HypD L
  /-- the closing of the link -/
  close  : T.Kc.OK
  /-- the closing of the offline test -/
  rows   : T.W.O.toC.Says T.Qt.base T.fq
  plan   : T.Qt.OkBehind
    ((T.W.O.toC.P.chain T.W.O.on0 T.Sn T.εf).append (T.W.O.toC.chain T.fq T.Qt.base))
  demand : ∀ V, T.Qt.q V →
    T.W.O.toC.P.q5 T.Sn (T.W.O.S.qFam (E₀ := extNone) T.q₀ T.Bw.t) (V.biUnion T.W.O.toC.toE.src)
  /-- the six conditions on the closing of the test at N instances -/
  cOk    : T.cZ.forget.forget.OkFrom (T.on.ol.toC.P.chain T.onB T.SnB T.εfB)
  cSides : T.cZ.forget.forget.SidesCT (T.on.ol.toC.P.q5 T.SnB T.qaB)
  cKB    : T.cZ.forget.KB T.N T.on.ol.toC.P.key6 T.kT
  cOkV   : T.cZ.OkFromV (T.on.ol.toC.P.chainV T.SnB T.qaB T.N T.onB T.εfB)
  cCoh   : T.cZ.forget.Coh
  cEnd   : ∀ Jn, T.VT.q Jn fun _ => ∅

end LdObjT

def Spec.ldObjT_ok (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] : Prop :=
  ∀ (T : LdObjT F E) (L : ℕ), T.Hyp L → T.obj.OK L

end Cb
