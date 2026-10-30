-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectReqEnd.lean: what the last part of a request's preamble leaves, as the data of the
test for linear constraints that follows.

A request's preamble is an interactive oracle reduction from a request to claims on the encoded
index and on the oracles that it leaves. Its last moves, the final batching, make the claims on the
encoded index that are still pending into one.
Definitions and statements; the proofs are in Cb/Obj/LdObjectReqEndProofs.lean. The analogue for the
offline phase is Cb/Obj/LdObjectWf.lean. A tensor row (`LdTenD.TenOK`, Cb/Req1/LdSegRefTen.lean) is
a claim < g ⊗ eq(point, ·), matrix of the index > + < a further linear form, entries of the oracle
messages > = a target. The batching (Cb/Ld/LdBatt.lean) makes several tensor rows into one: a linear
combination with coefficients from the evader's seed, then a sumcheck over the column variables.

Why: the object's record has one datum "what the preamble leaves" for the preamble of a request and
for the test that follows it. Cb/Obj/LdObjectReq.lean (the request's list over the configuration)
takes that datum (claims Cl; row vector g, point ψ, target τ; the mask part restM; the further
predicate "more") as given. The plan of the test asks conditions on it at all states: the mask part
is a linear form in entries at places that the plan can name; "more" is said exactly by rows of a
fixed finite family. If a request filed rows or mask forms as free data of the state, these could
not be met. So the datum is read off the last block of the request: the batching of the pending
tensor rows on the encoded index into one (`LdTenD`, Cb/Req1/LdSegRefTen.lean; Cb/Ld/LdBatt.lean),
beside the rows that stay open on the oracle messages that are left.

Main names:
  `LdORE F E Kc`: the data of the end of a request and of the test that follows, over one
    configuration Cf. The rows that stay open are a family over a fixed type Bn of linear forms on
    all entries. The pending tensor rows have mask forms as coefficients on names Nm laid at entries
    by a fixed map μAt. wAt: the places of the batching's own masks. e: how the k column variables
    are the two groups of the test's layout.
  `R.X : LdTenD E Kc`: the batching's data: nothing else is claimed beside the rows and the tensor
    rows; the further witness: the prover encoded index and a ghost G, which no relation reads: the
    core may read it (Cb/Obj/LdObjectReq.lean, Why).
  `R.O : LdOL F E`: the test's data, read off the batching's last claim z: row vector: ε times the
    batched row vector; point: the point of the batching's sumcheck, split along e; target: the last
    value; restM: the two mask terms; more: the rows that stay open hold.
  `R.Tie`: the condition that `R.mat U` is the index matrix of U in the test's layout, read over E
    (it says what mat is: it can always be met by the choice of mat).
  `R.lastP`: the last three moves of a request: re-bracketing; the batching; the last step. From
    "rows on all entries, beside the pending tensor rows" to the last stage `R.z`.
  `Spec.ldORE_holds`: under `R.Tie`: (the one tensor row holds, and the rows that stay open hold) if
    and only if `R.O.holds`, claim by claim.
  `Spec.ldORE_hyp`: `R.lastP.Hyp` from: 2 ≤ degree (`R.n`); the evader's law (`R.Z.OK`); `R.Tie`.
  `Spec.ldORE_zk`: `R.lastP.Zk base` from these, the places (`X.Own`), and: the batching's fact is
    fresh before it.
  `Spec.ldORE_kinds`: its moves are of the kinds that the last part of a request holds; k + 2
    rounds, nothing withheld.
  `Spec.ldORE_rest`: at all states restM is a linear form in the entries with public support:
    coefficients c z n (`R.restC`) with restM z m = ∑_n c z n · (entry n of m), and c z n = 0 unless
    n is one of the places wAt, μAt.
  `Spec.ldORE_more`: "more" is: all rows of the fixed family Bn hold, at the states that the claim
    holds. (Their supports are public if the forms sl are laid at named places:
    Cb/Req1/LdSegRefSupp.lean.)

Limits: this file does not say that the plan's clauses hold for a given plan: they are conditions on
places. The rows that stay open (Bn, Sb, sl) are free fields. Their supports are public only if the
forms are laid at named places. For a request built of segments they are meant to be the last
segment's rows and the kept rows: nothing says so but the step into `R.X.src`. This file does not
say how the pending rows come to stand at `R.X.src` (the segments' own batchings:
Cb/Req1/LdSegRefTen.lean). It does not say that the message which holds the masks at wAt, μAt is
left open by all closings.
That the pending tensor rows are batched into one after the last segment, and that the groups left
open go to the test, restates a write-up of ours in our own words
(lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Obj.LdObjectWf
import Cb.Req1.LdSegRefTen
import Cb.Req1.LdSegClose
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.RngPk

/-- The end of a request and the test that follows, over one configuration: the data. -/
structure LdORE (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Type 1 where
  Cf  : LdCf F E
  /-- the oracle messages that are left -/
  S   : Sig E
  /-- the rows that stay open -/
  Bn  : Type
  Sb  : Bn → Type
  sl  : ∀ b, Slf E (Sb b) S.Ent
  /-- the matrix of the index -/
  Rw  : Type
  [finRw : Fintype Rw]
  k   : ℕ
  mat : Cf.conf.Msg → Rw × (Fin k → Bool) → E
  /-- the rest of the explicit part; the record -/
  St  : Type
  rc  : St → Cf.conf.Rec
  /-- the pending tensor rows -/
  Q   : Type
  [finQ : Fintype Q]
  g   : St → Q → Rw → E
  pt  : St → Q → Fin k → E
  Nm  : Type
  [finNm : Fintype Nm]
  mf  : St → Q → Nm → E
  μAt : Nm → S.Ent
  Z   : Evader E Q
  n   : ℕ
  wAt : PIdx (List.replicate k (pfCube E n)) → S.Ent
  Rd  : S.Ent → Prop
  /-- a ghost: a part of the further witness that no relation reads, and the core, which may read it
  (the integer cells of all range checks of the request) -/
  G    : Type
  core : (Cf.conf.Msg × S.Msg) × G → Kc
  /-- the column variables: those that name a code row, and klo inside a row; the layout -/
  klo : ℕ
  e   : Fin k ≃ Fin Cf.X.v ⊕ Fin klo
  l   : ℕ
  lay : Rw × (Fin klo → Bool) → Cf.J₀
  py  : Rw → Fin l → Bool
  /-- what else the test needs -/
  e'  : ℕ
  t   : ℕ
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
  lO  : Rw → (NO.om iO).C.J

attribute [instance] LdORE.finRw LdORE.finQ LdORE.finNm

namespace LdORE
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E]
  [Algebra F E] (R : LdORE F E Kc)

/-- The batching of the pending tensor rows. -/
@[reducible] def X : LdTenD E Kc where
  S := R.S
  C := R.Cf.conf
  Wp := R.G
  Bn := R.Bn
  Sb := R.Sb
  sl := R.sl
  Rw := R.Rw
  k := R.k
  mat := R.mat
  St := R.St
  rc := R.rc
  Q := R.Q
  g := R.g
  pt := R.pt
  Nm := R.Nm
  mf := R.mf
  μAt := R.μAt
  Z := R.Z
  n := R.n
  wAt := R.wAt
  A0 := ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, R.core⟩
  Rd := R.Rd

/-- The test's data, read off the batching's last claim. -/
@[reducible] def O : LdOL F E where
  Cf := R.Cf
  S := R.S
  Cl := R.X.bt.par.Mid
  Y := R.Rw
  klo := R.klo
  l := R.l
  lay := R.lay
  py := R.py
  g := fun cl y => cl.eps * R.X.bt.rowVec cl y
  ψ := fun cl =>
    (fun i => R.X.bt.outPt cl (R.e.symm (Sum.inl i)),
      fun i => R.X.bt.outPt cl (R.e.symm (Sum.inr i)))
  τ := fun cl => cl.fin
  restM := fun cl m => R.X.bt.maskPart cl (Sum.elim (fun _ => 0) (R.S.ents m))
  more := fun cl m => R.X.RowsOK (R.X.stOf cl).1 m
  e' := R.e'
  t := R.t
  NW := R.NW
  SdW := R.SdW
  iW := R.iW
  lW := R.lW
  NU := R.NU
  SdU := R.SdU
  iU := R.iU
  lU := R.lU
  NO := R.NO
  SdO := R.SdO
  iO := R.iO
  lO := R.lO

/-- The condition that the matrix of the index is the index matrix in the layout of the encoded
index. -/
def Tie : Prop :=
  ∀ (U : R.Cf.conf.Msg) (r : R.Rw) (c : Fin R.Cf.X.v ⊕ Fin R.klo → Bool),
    R.mat U (r, fun i => c (R.e i)) = R.O.D.mat (R.Cf.upM U) r c

/-- The core at the last stage. -/
def coreZ (w : R.S.Msg × (R.Cf.conf.PIdx × R.G)) : Kc := R.core ((w.2.1.1.1, w.1), w.2.2)

/-- The last base joint of a request: the index is decoded by the statement with its record;
`R.O.holds`; the ghost is read by the core alone. -/
def bEnd :
    Rels Kc (R.O.Cl × R.Cf.conf.Rec) R.Cf.conf.E0 (R.S.Msg × (R.Cf.conf.PIdx × R.G)) where
  rel  := fun x y w => R.Cf.conf.Enc x.2 y w.2.1 ∧ R.O.holds x.1 x.2 w.2.1.1.1 w.1
  relR := fun a w => ∃ U, R.Cf.conf.dcd a.2 a.1.2 = some U ∧ R.O.holds a.1.1 a.1.2 U w.1
  on   := fun a => ¬ R.Cf.conf.coll a.2 a.1.2.1
  core := R.coreZ

/-- The last stage of a request. -/
@[reducible] def z : LdStage E Kc :=
  ⟨R.S, R.O.Cl × R.Cf.conf.Rec, R.Cf.conf.E0, R.Cf.conf.PIdx × R.G, R.bEnd⟩

/-- The record in the batching's last claim. -/
def recOf (z : R.X.bt.par.Mid) : R.Cf.conf.Rec := R.rc (R.X.stOf z).2

/-- The last step: the record is written beside the claim. -/
def endStep : LdMv R.X.m1 R.z := ldStepF R.S R.X.m1.A R.bEnd fun z => (z, R.recOf z)

/-- The last three moves of a request. -/
def lastP : LdProg R.X.src R.z :=
  (((LdProg.nil R.X.src).snoc R.X.stepIn).snoc (.sub R.X.m0 R.X.m1 (.one R.X.link))).snoc R.endStep

/-- The coefficients of the mask part. -/
def restC (z : R.X.bt.par.Mid) (n : R.S.Ent) : E :=
  (∑ i, if R.wAt (pIx R.X.bt.fmt (pdPlains E R.n R.k) i) = n then
        hSl (R.X.bt.par.vars z.st) (R.X.bt.par.hp z.st z.pt) i
      else 0) +
    z.eps * (∏ i, R.X.bt.outPt z i) * ∑ q, R.X.bt.chi z q * placed R.μAt (R.mf (R.X.stOf z).2 q) n

end LdORE

namespace Spec
section
variable (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- States, under `R.Tie`: what the batching leaves is what the test starts from. -/
def ldORE_holds : Prop :=
  ∀ (R : LdORE F E Kc), R.Tie →
    ∀ (cl : R.X.bt.par.Mid) (rec : R.Cf.conf.Rec) (U : R.Cf.conf.Msg) (m : R.S.Msg),
      (R.X.bt.RowHolds cl (R.X.msg (U, m)) ∧ R.X.RowsOK (R.X.stOf cl).1 m) ↔ R.O.holds cl rec U m

/-- All that the last three moves ask (`R.lastP.Hyp`). -/
def ldORE_hyp : Prop := ∀ (R : LdORE F E Kc), 2 ≤ R.n → R.Z.OK → R.Tie → R.lastP.Hyp

def ldORE_zk : Prop :=
  ∀ (R : LdORE F E Kc) (base : MaskFact R.X.src.J.W → Prop),
    2 ≤ R.n → R.Z.OK → R.X.Own → R.X.stepIn.After base R.X.mask.fact → R.lastP.Zk base

def ldORE_kinds : Prop :=
  ∀ (R : LdORE F E Kc), (R.lastP.All fun t => t = .sub ∨ t = .step) ∧
    R.lastP.nAll = R.k + 2 ∧ R.lastP.pBad = 0 ∧ R.lastP.pHid = 0

/-- States: at all states the mask part is a linear form in the entries, with public support. -/
def ldORE_rest : Prop :=
  ∀ (R : LdORE F E Kc),
    (∀ z m, R.O.restM z m = ∑ n, R.restC z n * R.S.ents m n) ∧
    ∀ z n, (∀ i, n ≠ R.wAt i) → (∀ a, n ≠ R.μAt a) → R.restC z n = 0

/-- States: "more" says that the rows of a fixed family hold. -/
def ldORE_more : Prop :=
  ∀ (R : LdORE F E Kc) z m, R.O.more z m ↔ Slf.All R.sl (R.X.stOf z).1 (R.S.ents m)

end
end Spec
end Cb
