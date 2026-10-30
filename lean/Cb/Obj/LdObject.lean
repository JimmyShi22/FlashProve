-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObject.lean: the record of all sub-protocols of the holographic IOP over one configuration,
and the statements that conditions on the configuration and on each of them (`Obj.OK L`) give all
that the generic construction requires of them and, under further hypotheses on the configuration
and the numbers, the IOP's properties.

Definitions and statements (`Cb.Spec.ldObj_hyp`, `Cb.Spec.ldObj_props`); the
proofs are in Cb/Obj/LdObjectProofs.lean.

Hiop/RecBuild.lean builds the holographic IOP with an untrusted committer and records from a
configuration C and a record `SubsR C` of four sub-protocols: the preamble of weights-formedness,
the link, the preamble of a request, and the IOPP for the constraint relation at its two settings
(one instance; at most N). Hiop/RecMain.lean states its properties from the four parameter lists
(`SubsR.Hyp`) and the laws of the configuration (`ConfigurationWithOutOfDomainSample.Props`), under the hypotheses of its
statements. Here C := `Cf.conf` (Cb/Obj/LdObjectConf.lean), and the lists are derived from
`Obj.OK L`.
A parameter list is what Hiop requires of one sub-protocol: an item on round-by-round knowledge
soundness and a list of all other items (for a preamble `PreKnowR`, `PreListR`, Hiop/RecSubs.lean).
A term is a reduction given with its honest prover, extractor and numbers. For "configuration" see
the head of Cb/Obj/LdObjectConf.lean; for "link", "joint" and "tail", that of
Cb/Obj/LdObjectLink.lean.

The data (`LdObj F E`, the object):
  `Cf`: the configuration's data.
  `off`, `on`: for each of the two phases: what its preamble leaves and the data of the test that
    follows (`LdOLd Cf`; `LdOL`: Cb/Obj/LdObjectLin.lean).
  `K`: the link's data. `on0K`, `on1K`: see "On the link's pair" below.
  `N`: the bound on the size of a batch.
  five terms, each any term of its kind: `wf` (`WfT`, Cb/Obj/LdObjectOff.lean), `lin` (`LinT` there:
    a tail), `link` (`K.Tail`, Cb/Obj/LdObjectLink.lean), `req` (`ReqT`, Cb/Obj/LdObjectReq.lean),
    `linB` (`LinBT`, Cb/Obj/LdObjectOnB.lean).
  cores; fixed values.
`Obj.subs : SubsR Obj.Cf.conf`, `Obj.nums`: the five terms in the types of the lists.
`Obj.OK L` asks:
  `conf`: `Cf.OK L`.
  `wf`, `lin`, `link`, `req`, `linB`: each term's own OK (among its clauses: for the preambles its
    bundle between the two end joints of its kind and its formats, for the tails `TailTr`, for the
    batch the honest half and one `KnowB`).
  `fitsK`: see "On the link's pair" below.
  `fitOff`, `fitOn`: the two lines "the preamble's budget bears what the test behind it reads of the
    oracles left", as they stand in the list (they tie two terms; rules that derive them from "the
    preamble's term bears what follows" at the test's bound: `Cb.ldOW_fit`, `Cb.ldOR_fit`,
    `Cb.ldObj_fit`).

Main names:
  `Spec.ldObj_hyp`: `Obj.OK L` ⇒ `Obj.subs.Hyp Obj.nums`: all items of the four parameter lists, the
    two lines on budgets included.
  `Spec.ldObj_props`: with `Obj.OK L`, `Cf.PadBij`, b ≤ the code's own number
    (`Cf.C₀.b`), εs at least every error, as a probability, and at least (L choose 2)·err / (number
    of seeds), err being `Cf.Z.err`: the object has all properties of Hiop/RecInterface.lean
    (`PropsR`: its fields `sub`, `sound`, `honest`).




  `Spec.ldObj_padBij_none`: with no pad and no answer `Cf.PadBij` holds.

On the link's pair of conditions (`on0K`, `on1K`): the pair is data: `OK` asks that the object's own
condition gives it (`fitsK`, Cb/Obj/LdObjectLinkPair.lean: an index that decodes with its record,
without a collision, has on0K; an index without a collision has on1K) and that the term is a tail
from the joint at that pair (`link`). Where nothing is said the pair is (`K.free`, `K.free`):
neither index has a collision at its record's seed. Then `fitsK` holds trivially and `link` is
`K.TailOK` (Cb/Obj/LdObjectLink.lean), by definition. The pair (`K.dec0`, `K.free`) takes the first
index by the regime "it decodes": under the conditions told there, no bad point for its fold, a
larger radius, fewer locations (Cb/Obj/LdObjectLinkAt.lean).

Limits: the theorems (Cb/Obj/LdObjectProofs.lean) are conditional on five terms that are not given
here. That `Obj.OK L` can be met is not shown in this file: until each of the five kinds
has a value with its OK proved, the theorems say nothing about a protocol. They fix the joints at
which the five terms have to meet, and show that for the four parameter lists nothing else is needed
beside `Obj.OK L` and whatever the arguments hold as proofs.


This file says nothing on zero knowledge of the whole object (Hiop/RecWhole.lean), nothing on the
compiled argument, and nothing on numerals.
Declared: This protocol's technical report (lean/CREDITS.md) has one sub-protocol "IOPP for linear
constraints" with parameters (form, bound on instances, locations), used at two settings; here, as
in Hiop/RecSubs.lean, the two settings are two independent terms `lin` and `linB`: wider.

Terms: lean/GLOSSARY.md.
-/
/- Limits: no theorem of this library states the conclusion of `ldObj_hyp` of a concrete object.




-/
import Cb.Obj.LdObjectOff
import Cb.Obj.LdObjectOnB
import Cb.Obj.LdObjectLinkProofs
import Cb.Obj.LdObjectLinkPair
import Hiop.RecMainProof
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR
open scoped ENNReal

/-- What a preamble leaves and the data of the test after it, over a fixed configuration: the fields
of `LdOL` but `Cf`. -/
structure LdOLd {F E : Type} [Field F] [Field E] [Algebra F E] (Cf : LdCf F E) where
  S  : Sig E
  Cl : Type
  Y   : Type
  [finY : Fintype Y]
  klo : ℕ
  l   : ℕ
  lay : Y × (Fin klo → Bool) → Cf.J₀
  py  : Y → Fin l → Bool
  g     : Cl → Y → E
  ψ     : Cl → (Fin Cf.X.v → E) × (Fin klo → E)
  τ     : Cl → E
  restM : Cl → S.Msg → E
  more  : Cl → S.Msg → Prop
  e' : ℕ
  t  : ℕ
  NW  : Sig E
  SdW : NW.Seeds
  iW  : NW.O
  lW  : ((Fin Cf.X.v ⊕ Fin klo) → Bool) → (NW.om iW).C.J
  NU  : Sig E
  SdU : NU.Seeds
  iU  : NU.O
  lU  : Fin Cf.C₀.k → (NU.om iU).C.J
  NO  : Sig E
  SdO : NO.Seeds
  iO  : NO.O
  lO  : Y → (NO.om iO).C.J

attribute [instance] LdOLd.finY

/-- the LdOL -/
@[reducible] def LdOLd.ol {F E : Type} [Field F] [Field E] [Algebra F E]
    {Cf : LdCf F E} (D : LdOLd Cf) : LdOL F E :=
  { Cf := Cf, S := D.S, Cl := D.Cl, Y := D.Y, finY := D.finY, klo := D.klo, l := D.l, lay := D.lay,
    py := D.py, g := D.g, ψ := D.ψ, τ := D.τ, restM := D.restM, more := D.more, e' := D.e',
    t := D.t, NW := D.NW, SdW := D.SdW, iW := D.iW, lW := D.lW, NU := D.NU, SdU := D.SdU,
    iU := D.iU, lU := D.lU, NO := D.NO, SdO := D.SdO, iO := D.iO, lO := D.lO }

/-- The object: the data. -/
structure LdObj (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] where
  Cf   : LdCf F E
  off  : LdOLd Cf
  on   : LdOLd Cf
  K    : Cf.LinkPar
  /-- the conditions on the two encoded indices at the link's first joint
  (Cb/Obj/LdObjectLinkPair.lean); if nothing is said: neither has a collision at its record's
  seed -/
  on0K : (K.P.D.X.Row → Fin Cf.C₀.n → E) → K.P.D.X.Rec → Prop := K.free
  on1K : (K.P.D.X.Row → Fin Cf.C₀.n → E) → K.P.D.X.Rec → Prop := K.free
  N    : ℕ
  /-- the types of the two cores; the five terms -/
  Kw   : Type
  Kr   : Type
  wf   : off.ol.WfT Kw
  lin  : off.ol.LinT
  link : K.Tail
  req  : on.ol.ReqT Kr
  linB : on.ol.LinBT N
  /-- the cores at the first joints of the two preambles -/
  cw   : Cf.conf.PIdx → Kw
  cr   : Cf.conf.PIdx × Cf.conf.Cells → Kr
  /-- fixed values -/
  z0   : req.Wp
  r0   : on.S.Rnd
  dOff : off.ol.left.AMsg
  dOn  : on.ol.left.AMsg

namespace LdObj
variable {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] (Obj : LdObj F E)

/-- The four sub-protocols over the configuration. -/
def subs : SubsR Obj.Cf.conf where
  off := Obj.off.ol.left
  on := Obj.on.ol.left
  N := Obj.N
  wf := Obj.wf.wf
  linOff := Obj.lin.Q
  link := Obj.K.link Obj.link
  req := Obj.req.req
  linOn := Obj.linB.Q
  cellsOf := Obj.req.cellsOf Obj.z0 Obj.r0
  hWf := Obj.wf.hWf
  hLinOff := Obj.lin.hLin
  hLink := Obj.K.hLink Obj.link
  hReq := Obj.req.hReq
  hLinOn := Obj.linB.hQ
  dOff := Obj.dOff
  dOn := Obj.dOn

def nums : Obj.subs.Nums :=
  ⟨Obj.wf.nums, Obj.lin.nums, Obj.K.nums Obj.link, Obj.req.nums, Obj.linB.P⟩

open Classical in
/-- What is asked of the configuration and of the five terms. -/
structure OK (L : ℕ) : Prop where
  conf  : Obj.Cf.OK L
  wf    : Obj.wf.OK Obj.cw
  lin   : Obj.lin.OK
  fitsK : Obj.K.FitsK Obj.on0K Obj.on1K
  link  : Obj.K.TailOKAt Obj.on0K Obj.on1K Obj.link
  req   : Obj.req.OK Obj.cr
  linB  : Obj.linB.OK
  fitOff : ∀ ρ₁ ρ₂, Obj.wf.nums.bud ρ₁ ((Obj.lin.Q.extReads ρ₂).biUnion (Obj.wf.wf.srcO ρ₁))
  fitOn  : ∀ ρ₁ ρ₂, Obj.req.nums.bud ρ₁ ((Obj.linB.R.extReads ρ₂).biUnion (Obj.req.req.srcO ρ₁))

end LdObj

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The four parameter lists, whole, from `Obj.OK L`. -/
def ldObj_hyp : Prop := ∀ (Obj : LdObj F E) (L : ℕ), Obj.OK L → Obj.subs.Hyp Obj.nums

/-- The object: `PropsR`, under the hypotheses below. -/
def ldObj_props : Prop :=
  ∀ (Obj : LdObj F E) (L b : ℕ) (εs : ℝ≥0∞), Obj.OK L → Obj.Cf.PadBij → b ≤ Obj.Cf.C₀.b →
    Obj.nums.Below εs →
    ((L.choose 2 * Obj.Cf.Z.err : ℕ) : ℝ≥0∞) ≤ εs * (Fintype.card Obj.Cf.conf.Seed : ℝ≥0∞) →
    Obj.subs.lhr.PropsR Obj.Cf.conf.Ryes Obj.Cf.conf.Rno Obj.subs.wit (Obj.nums.lh b εs)

def ldObj_padBij_none : Prop := ∀ (Cf : LdCf F E), IsEmpty Cf.Z.S → IsEmpty Cf.Pd → Cf.PadBij

end
end Spec
end Cb
