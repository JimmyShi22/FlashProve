-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldObj.lean: this file makes the object's data (`LdObjD`, Cb/Obj/LdObjectTerms.lean) from
the data of its parts, for variable data; the object's data are one record with the data of the
protocol's sub-protocols (the preamble of weights-formedness, the offline test for linear
constraints, the link, a request and the batch test) over one configuration, without the closings of
the two linear tests. The clauses of the records on the object that speak of places, seeds and the
index's folds are theorems, each under the hypotheses of its statement.

Definitions and statements; the proofs are in Cb/Ld/LdBldObjProofs.lean. Generic: any finite field F
and any finite field E that is an algebra over F. Nothing assumed beyond the hypotheses of the
statements and whatever the arguments hold as proofs.
A regime is the condition on an encoded index and its record under which a fold's error is stated:
the first, "no collision" at the record's seed (`K.free`, Cb/Obj/LdObjectLink.lean), or the second,
"it decodes with its record" (`K.dec0`, Cb/Obj/LdObjectLinkPair.lean; `onDec`,
Cb/Obj/LdObjectLinB.lean); `LdObjD.Par3` (Cb/Obj/LdObjectDataThird.lean) lets the link's first index
have either.

Main names:
  `BldNm Fm`: for each member: L (bound on its list), t (positions that its encoding hides), d (its
    distance as read). The record has no condition on them. t is the argument t of `Sig.StdL.OK`
    (Cb/Ld/LdSendStdL.lean).
  `BldObj F E`, the input: Zw (weights-formedness; the three families of the offline linear test
    that it stores are overwritten); ne: the configuration's code C₀ has a position; Lo, Lb: what
    the offline and the batch linear test need beside the configuration and the claims; Lk: what the
    link needs beside them (`BldLn`, `BldLk`, Cb/Ld/LdBldLin.lean); Kc: the link's closing (a group
    on the link's family, a bridge, a whole test: parameters); Rq: the request (the three families
    of the batch linear test that it stores are overwritten); N; baB: how many positions of each
    message that the request leaves the batch test may read; numbers (`BldNm`) for the members of
    the seven families, not for weights-formedness' own; fixed values.
  `X.D : LdObjD F E`, through `ldPartsD` (Cb/Obj/LdObjectPartsD.lean). Chosen here, as the clauses
    of `Own3₀` (Cb/Obj/LdObjectDataRefJ.lean) prescribe them (εfIs, on1Is, ε₁Is, onBIs, εfBIs) or
    allow them (par, q₀e, monoB): εf := εThird e' (offline fold, first regime); the link: the first
    (parent's) index in the regime "it decodes with its record", ε₀ := 0; the further (child's)
    index in the regime "no collision", ε₁ := εThird e₁; the batch test: the regime "it decodes",
    εfB := 0; q₀ := "nothing"; qaB := nothing of further oracles, at most baB a positions of the
    message a.
  `X.Y : X.D.StdS` (Cb/Obj/LdObjectSendersLin.lean): pads in E; the link's seeds: the family's joint
    seed.
  `Spec.bldObj_snd`: `X.D = X.D.std X.Y` (which senders are in the object: by definition); `D.std Y`
    is D with its seven senders replaced by the standard senders of Y.
  `Spec.bldObj_wf`: (`X.D.W`, `X.D.Bw`) is the pair (`X.ZwB.W`, `X.ZwB.G.B`) of weights-formedness
    with the offline test's families laid in (by definition).
  `Spec.bldObj_places`: `Lo.Inj`, `Lb.Inj`, `Lk.Inj` ⇒ the two `Places`, the link's `Reads`.
    `Spec.bldObj_fair`: the seeds of the seven families are fair.
  `X.OwnNum`: what `Own3₀` still asks, on data and numbers: both layouts of the index matrix land on
    the configuration's; the rows of both index matrices are at different corners; |Lay| ≤ 2^l;
    offline e' ≤ eM; the link: e₀ + eM < d, e₁ ≤ eM; the link's whole test reads no more positions
    than each member hides (exactly: the field bearK: `X.Kc.t` ≤ `X.nK.t a` for every member a);
    online e' + eM < d.
  `Spec.bldObj_own`: `X.OwnNum` ⇒ `X.D.Own3₀`.

Notation: `εThird e` (`LdCf.εThird`, Cb/Obj/LdObjectThirdTests.lean): the error of a fold of the
index at the radius e, within a third; `eM`: the radius of decoding, in columns (`LdIx.eM`,
Cb/Ld/LdFoldEq.lean), a field of the configuration (`LdCf`, Cb/Obj/LdObjectConf.lean); `N`: the
batch test is the test at N instances (`PBatD`, Cb/Obj/LdObjectPartsD.lean).

Limits: this file says nothing on codes and lists. It says nothing on the
plans of whole tests, their groups, towers. It does not say that an input of interest exists.



Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBldLin
import Cb.Obj.LdObjectPartsD
import Cb.Obj.LdObjectPartWfE
import Cb.Obj.LdObjectSendersLin
import Cb.Obj.LdObjectDataRefJ
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

/-- all data of weights-formedness, the offline test's families laid in (here and in the next two:
no other field's type reads these fields) -/
@[reducible] def LdWfE.withBld (Z : LdWfE F E)
    (L : BldLn E ((Fin Z.W.Cf.X.v ⊕ Fin Z.W.klo) → Bool) (Fin Z.W.Cf.C₀.k) Z.W.P.Rw) : LdWfE F E :=
  { Z with W := Z.W.withBld L }

/-- a request, the batch test's families laid in -/
@[reducible] def PReqG.withBld {Cf : LdCf F E} (Rq : PReqG Cf)
    (L : BldLn E ((Fin Cf.X.v ⊕ Fin Rq.on.klo) → Bool) (Fin Cf.C₀.k) Rq.on.Y) : PReqG Cf :=
  { Rq with on := Rq.on.withBld L }

/-- the end of a request, the batch test's families laid in -/
@[reducible] def LdORE.withBld {Kc : Type} (R : LdORE F E Kc)
    (L : BldLn E ((Fin R.Cf.X.v ⊕ Fin R.klo) → Bool) (Fin R.Cf.C₀.k) R.Rw) : LdORE F E Kc :=
  { R with
    e' := L.e', t := L.t
    NW := L.FW.sig, SdW := L.FW.Sd, iW := L.iW, lW := fun c => L.FW.lay.atD L.iW (L.aW c)
    NU := L.FU.sig, SdU := L.FU.Sd, iU := L.iU, lU := fun k => L.FU.lay.atD L.iU (L.aU k)
    NO := L.FO.sig, SdO := L.FO.Sd, iO := L.iO, lO := fun y => L.FO.lay.atD L.iO (L.aO y) }

end

/-- three numbers for each member of a family -/
structure BldNm {E : Type} (Fm : BldF E) where
  L : Fm.O → ℕ
  t : Fm.O → ℕ
  d : Fm.O → ℕ

/-- The input. -/
structure BldObj (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E]
    [DecidableEq E] [Algebra F E] : Type 1 where
  Zw  : LdWfE F E
  [ne : Nonempty (Fin Zw.W.Cf.C₀.n)]
  Lo  : BldLn E ((Fin Zw.W.Cf.X.v ⊕ Fin Zw.W.klo) → Bool) (Fin Zw.W.Cf.C₀.k) Zw.W.P.Rw
  Lk  : BldLk E (Fin Zw.W.Cf.C₀.k)
  Kc  : (Zw.W.Cf.bldK Lk).P.Cl
  Rq  : PReqG Zw.W.Cf
  Lb  : BldLn E ((Fin Zw.W.Cf.X.v ⊕ Fin Rq.on.klo) → Bool) (Fin Zw.W.Cf.C₀.k) Rq.on.Y
  N   : ℕ
  baB : Rq.on.S.O → ℕ
  /-- numbers -/
  nW  : BldNm Lo.FW
  nU  : BldNm Lo.FU
  nO  : BldNm Lo.FO
  nK  : BldNm Lk.F
  nWB : BldNm Lb.FW
  nUB : BldNm Lb.FU
  nOB : BldNm Lb.FO
  /-- fixed values -/
  dT  : (Zw.W.withBld Lo).O.toC.P.W0
  dT₀ : (Zw.W.withBld Lo).O.P.W0
  w1  : (Zw.W.withBld Lo).O.toC.P.W1
  w3  : (Zw.W.withBld Lo).O.toC.P.W3
  wK  : (Zw.W.Cf.bldK Lk).P.W1
  dK₂ : (Zw.W.Cf.bldK Lk).P.W2
  dK  : (Zw.W.Cf.bldK Lk).P.W0
  dB  : (Rq.on.withBld Lb).ol.toC.P.W0
  dB₀ : (Rq.on.withBld Lb).ol.P.W0
  w1B : (Rq.on.withBld Lb).ol.toC.P.W1
  w3B : (Rq.on.withBld Lb).ol.toC.P.W3
  yB  : (Rq.on.withBld Lb).ol.toC.P.Ea.Str
  z0  : Rq.Wz
  r0  : Rq.on.S.Rnd
  dOff : (Zw.W.withBld Lo).O.left.AMsg
  dOn  : (Rq.on.withBld Lb).ol.left.AMsg

attribute [instance] BldObj.ne

namespace BldObj
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [DecidableEq E]
  [Algebra F E] (X : BldObj F E)

/-- the configuration -/
abbrev Cf : LdCf F E := X.Zw.W.Cf

/-- weights-formedness with the offline test's families -/
@[reducible] def ZwB : LdWfE F E := X.Zw.withBld X.Lo

/-- The first part. -/
@[reducible] def A : PWf F E := { W := X.ZwB.W, ne := X.ne, Bw := X.ZwB.G.B }

/-- the request with the batch test's families (its field on: what the request leaves) -/
@[reducible] def RqB : PReqG X.Cf := X.Rq.withBld X.Lb

/-- The data of the offline test's three standard senders. -/
@[reducible] def TS : X.A.W.O.toC.P.Std E := X.A.W.O.toC.P.bldStd X.Lo X.dT X.w1 X.w3

/-- The data of the batch test's three standard senders. -/
@[reducible] def TB : X.RqB.on.ol.toC.P.Std E :=
  X.RqB.on.ol.toC.P.bldStd X.Lb X.dB X.w1B X.w3B

/-- the link's parameters -/
@[reducible] def K : X.Cf.LinkPar := X.Cf.bldK X.Lk

/-- the parts -/
@[reducible] def pLn : PLinD X.A :=
  ⟨X.Cf.εThird X.Lo.e', X.TS.snd X.nW.L X.nU.L X.nO.L X.nW.t X.nU.t X.nO.t,
    fun U => U = ∅, X.dT, X.dT₀⟩
@[reducible] def pLk : PLink X.Cf :=
  ⟨X.K, X.K.dec0, X.K.free, X.K.P.stdS X.Lk.F.Sd X.nK.L X.nK.t X.Lk.F.lay X.Lk.ixK X.wK, 0,
    X.Cf.εThird X.Lk.e₁, X.Kc, X.dK₂, X.dK⟩
@[reducible] def pBt : PBatD X.Cf X.RqB.on :=
  ⟨X.N, X.RqB.on.ol.onDec, X.TB.snd X.nWB.L X.nUB.L X.nOB.L X.nWB.t X.nUB.t X.nOB.t,
    X.RqB.on.ol.toC.Sa.qFam (E₀ := X.RqB.on.ol.toC.E₀) (fun U => U = ∅) X.baB, 0, X.dB, X.dB₀, X.yB⟩

/-- The object's data. -/
@[reducible] def D : LdObjD F E :=
  ldPartsD X.A X.pLn X.pLk X.RqB X.pBt X.z0 X.r0 X.dOff X.dOn

/-- The data of the seven standard senders: pads in E. -/
@[reducible] def Y : X.D.StdS where
  Fp := E
  TS := X.TS
  LW := X.nW.L
  LU := X.nU.L
  LO := X.nO.L
  tW := X.nW.t
  tU := X.nU.t
  tO := X.nO.t
  YK := X.Lk.F.lay
  ixK := X.Lk.ixK
  wK := X.wK
  SdK := X.Lk.F.Sd
  LK := X.nK.L
  tK := X.nK.t
  TB := X.TB
  LWB := X.nWB.L
  LUB := X.nUB.L
  LOB := X.nOB.L
  tWB := X.nWB.t
  tUB := X.nUB.t
  tOB := X.nOB.t

/-- What `Own3₀` still asks. -/
structure OwnNum : Prop where
  layO  : ∀ a, ∃ l, X.Zw.W.lay a = X.Cf.lay l
  layB  : ∀ a, ∃ l, X.Rq.on.lay a = X.Cf.lay l
  pyO   : Function.Injective X.Zw.W.py
  pyB   : Function.Injective X.Rq.on.py
  lay2  : Fintype.card X.Cf.Lay ≤ 2 ^ X.Lk.l
  e'le  : X.Lo.e' ≤ X.Cf.eM
  e₀far : X.Lk.e₀ + X.Cf.eM < X.Cf.C₀.d
  e₁le  : X.Lk.e₁ ≤ X.Cf.eM
  bearK : ∀ a, X.Kc.t ≤ X.nK.t a
  e'far : X.Lb.e' + X.Cf.eM < X.Cf.C₀.d

end BldObj

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

def bldObj_snd : Prop := ∀ X : BldObj F E, X.D = X.D.std X.Y

def bldObj_wf : Prop :=
  ∀ X : BldObj F E, (⟨X.D.W, X.D.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨X.ZwB.W, X.ZwB.G.B⟩

def bldObj_places : Prop :=
  ∀ X : BldObj F E, X.Lo.Inj → X.Lb.Inj → X.Lk.Inj →
    X.Y.TS.Places ∧ X.Y.TB.Places ∧
    X.Y.YK.Reads X.Y.ixK fun m => Sum.elim (X.D.K.P.uv₀ m) (X.D.K.P.uv₁ m)

def bldObj_fair : Prop :=
  ∀ X : BldObj F E, X.D.W.O.toC.P.SdW.Fair ∧ X.D.W.O.toC.P.SdU.Fair ∧ X.D.W.O.toC.P.SdO.Fair ∧
    X.Y.SdK.Fair ∧ X.D.on.ol.toC.P.SdW.Fair ∧ X.D.on.ol.toC.P.SdU.Fair ∧ X.D.on.ol.toC.P.SdO.Fair

/-- The index's folds. -/
def bldObj_own : Prop := ∀ X : BldObj F E, X.OwnNum → X.D.Own3₀

end
end Spec
end Cb
