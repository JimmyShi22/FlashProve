-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefTen.lean: the batching of a segment's tensor rows on the encoded index, beside the
rows of the body, as a list of moves.

This file is about one batching step of a segment's body: several linear claims on one matrix
(tensor rows on the encoded index) are reduced, by random coefficients and a sumcheck, to one such
claim. It is written as a sequence of reductions (a list of moves).
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Req1/LdSegRefTenProofs.lean.
What zero knowledge asks of a move, beside its hypotheses: Cb/Req1/LdReq.lean. Cb/Ld/LdWfIdx.lean:
claims that read the encoded index: the index is a further oracle, decoded by the statement with
its record.
The form of a tensor row (`BattPar.ten`, Cb/Ld/LdBatt.lean) is the multilinear extension, at a
point z, of vᵀM on the columns of a matrix M; the row claims that this form plus a mask form on
entries is a public target (`X.TenOK`). `X.mat` reads M off the message of the encoded index.

Why: at the end of a body all that is left of the segment's own oracle messages are rows on all
entries (Cb/Req1/LdSegRefRows.lean). Beside them are claims on the encoded index: tensor rows, one
for each sumcheck that ended at a map of the index, each with a mask form and a public target. They
are batched into one tensor row. That row is no row of this closing: it is pending and rides on.
The incoming mask forms are coefficients on names Nm (mf st q : Nm → E), laid at entries by a fixed
map μAt. The state is free to choose coefficients; it cannot choose places. So what the block asks
of the incoming forms at all states (no incoming form reads an own entry; they read entries in Rd
only) are conditions on places (`X.Own`), which can be met. With forms on all entries as free data
of the state they could not.

Main names:
  `LdTenD`: the data: S (the oracle messages that are open), C (the configuration of the index),
    the evader Z, the degree n, the places wAt of the block's own masks; most other fields have a
    comment at their place.
  St₁, fz, Az (variables of the file, no fields): what is claimed at the end, beside the rows, in
    the form that the closing needs.
  `X.prog`: the three moves.
    step, `X.src` → `X.m0`, no round: re-bracketing: the rows go inside the joint that rides along
      in the block.
    sub, `X.m0` → `X.m1`, k + 2 rounds: the block, lifted twice: the index decoded by the
      statement; over the oracle messages of the stage.
    step, `X.m1` → `X.tgt`, no round: the rows come out again; what is left is written as Az.
  `X.src`: rows on all entries, beside (the index is decoded; A0; the tensor rows hold): the form
    of the last stage of Cb/Req1/LdSegRefRows.lean.
  `X.tgt`: rows on all entries, beside Az: the form of the stage at which a closing begins
    (`Spec.ldSegRef_tn_bat`: it is `LdBatD.src`, by definition).
  `Spec.ldSegRef_tn_own`: `X.Own` (places only) gives the block's conditions on its own entries, at
    all states.
  `Spec.ldSegRef_tn_hyp`: `X.prog.Hyp` from: 2 ≤ n; the evader's law; `X.Ends` (what is left goes
    over into Az: exact forth, relaxed back, condition, core).
  `Spec.ldSegRef_tn_goodM`: the block's link is a masked block (`GoodM`, Ior/Masked.lean), with the
    letters X.mask, from 2 ≤ n, the evader's law, X.Own.
  `Spec.ldSegRef_tn_zk`: X.prog.Zk base from these and: the fact that the block needs is fresh
    before it.
  `Spec.ldSegRef_tn_kinds`: the kinds of the moves are those that a body may hold.
  `Spec.ldSegRef_tn_nums`: k + 2 rounds, nothing withheld, in this sense:
    `(X.prog St₁ fz Az).nAll = X.k + 2 ∧ (X.prog St₁ fz Az).pBad = 0 ∧ (X.prog St₁ fz Az).pHid = 0`
    (see `GoodB`, Ior/Masked.lean).

Limits: the pending rows of earlier segments. In this protocol's technical report (lean/CREDITS.md)
they pile up: they are not among the claims Q; they ride in "what else is claimed" (A0), and one
more batching after the last segment makes them into one row. Q being a parameter, the other
schedule is an instance too (the earlier pending row is one of the claims Q, its mask form again
coefficients on names: one pending row at any time); that is a variant, not the report's.
This file does not say that the masks at wAt stand in an oracle message that outlives this closing
(the message of the index's masks is in no segment's group: a condition kp of every closing). It
says nothing on the index's own test.
The place of the block restates a table of a segment in a write-up of ours that is not in this
repository in our own words (lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReq
import Cb.Ld.LdBatt
import Cb.Ld.LdWfIdx
import Cb.Ld.LdBatPeel
import Cb.Ld.LdRng
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.RngPk
open scoped ENNReal

/-- The batching of tensor rows beside the rows of a body: the data. -/
structure LdTenD (E Kc : Type) [Field E] [Fintype E] : Type 1 where
  S   : Sig E
  C   : ConfigurationWithOutOfDomainSample
  Wp  : Type
  /-- the rows that ride along -/
  Bn  : Type
  Sb  : Bn → Type
  sl  : ∀ b, Slf E (Sb b) S.Ent
  /-- the matrix of the index -/
  Rw  : Type
  [finRw : Fintype Rw]
  k   : ℕ
  mat : C.Msg → Rw × (Fin k → Bool) → E
  /-- the rest of the explicit part; the record -/
  St  : Type
  rc  : St → C.Rec
  /-- the claims: names, row vectors, points -/
  Q   : Type
  [finQ : Fintype Q]
  g   : St → Q → Rw → E
  pt  : St → Q → Fin k → E
  /-- the incoming mask forms: coefficients on names; the places of the names -/
  Nm  : Type
  [finNm : Fintype Nm]
  mf  : St → Q → Nm → E
  μAt : Nm → S.Ent
  Z   : Evader E Q
  n   : ℕ
  /-- the places of the own masks -/
  wAt : PIdx (List.replicate k (pfCube E n)) → S.Ent
  /-- what else is claimed, of (message of the index, messages) -/
  A0  : IOR.Rels Kc St C.E0 ((C.Msg × S.Msg) × Wp)
  /-- the entries of the messages that the block reads -/
  Rd  : S.Ent → Prop

attribute [instance] LdTenD.finRw LdTenD.finQ LdTenD.finNm

namespace LdTenD
variable {E Kc : Type} [Field E] [Fintype E] (X : LdTenD E Kc)

/-- the explicit part of the rows -/
abbrev Xr : Type := (X.Bn → E) × (∀ b, X.Sb b)
/-- the rows hold -/
def RowsOK (x : X.Xr) (m : X.S.Msg) : Prop := Slf.All X.sl x (X.S.ents m)

/-- The parameters of the block: entries = those of the matrix beside all entries of the messages;
the state holds the rows' explicit part too. -/
def bt : BattPar E where
  St := X.Xr × X.St
  J := (X.Rw × (Fin X.k → Bool)) ⊕ X.S.Ent
  Rw := X.Rw
  k := X.k
  mAt := Sum.inl
  Q := X.Q
  g := fun st => X.g st.2
  pt := fun st => X.pt st.2
  slM := fun q st => Sum.elim (fun _ => 0) (placed X.μAt (X.mf st.2 q))
  Z := X.Z
  n := X.n
  wAt := fun i => Sum.inr (X.wAt i)

/-- the entries, from the tuple (message of the index, messages) -/
def msg (um : X.C.Msg × X.S.Msg) : X.bt.J → E := Sum.elim (X.mat um.1) (X.S.ents um.2)

/-- The tensor rows hold: for each claim, < g ⊗ eq(point, ·), matrix > + < incoming mask form,
entries > is the public target. -/
def TenOK (x : (X.Q → E) × X.St) (um : X.C.Msg × X.S.Msg) : Prop :=
  ∀ q, X.bt.ten (X.g x.2 q) (X.pt x.2 q) (X.msg um) +
      ∑ j, (Sum.elim (fun _ => 0) (placed X.μAt (X.mf x.2 q)) : X.bt.J → E) j * X.msg um j = x.1 q

/-- what is claimed beside the rows, before the block, on tuples -/
def tenA : IOR.Rels Kc ((X.Q → E) × X.St) X.C.E0 ((X.C.Msg × X.S.Msg) × X.Wp) :=
  ⟨fun x y w => X.A0.rel x.2 y w ∧ X.TenOK x w.1,
    fun a w => X.A0.relR (a.1.2, a.2) w ∧ X.TenOK a.1 w.1,
    fun a => X.A0.on (a.1.2, a.2),
    X.A0.core⟩

/-- what rides along in the block: the rows, and what else is claimed -/
def A1 : IOR.Rels Kc (X.Xr × X.St) X.C.E0 ((X.C.Msg × X.S.Msg) × X.Wp) :=
  ⟨fun st y w => X.RowsOK st.1 w.1.2 ∧ X.A0.rel st.2 y w,
    fun a w => X.RowsOK a.1.1 w.1.2 ∧ X.A0.relR (a.1.2, a.2) w,
    fun a => X.A0.on (a.1.2, a.2),
    X.A0.core⟩

/-- the state in the claim that the block leaves -/
def stOf (z : X.bt.par.Mid) : X.Xr × X.St := (show (X.Xr × X.St) × X.Z.D from z.st).1

/-- Rows on all entries, beside the claims on the index. -/
@[reducible] def src : LdStage E Kc :=
  ⟨X.S, X.Xr × ((X.Q → E) × X.St), X.C.E0, X.C.PIdx × X.Wp,
    claimRels X.RowsOK (idxAt X.C (fun x => X.rc x.2) X.tenA)⟩
/-- the two stages of the block -/
@[reducible] def m0 : LdStage E Kc :=
  ⟨X.S, (X.Q → E) × (X.Xr × X.St), X.C.E0, X.C.PIdx × X.Wp,
    idxAt X.C (fun x => X.rc x.2.2) (X.bt.baseIn X.C.E0 X.A1 fun w => X.msg w.1)⟩
@[reducible] def m1 : LdStage E Kc :=
  ⟨X.S, X.bt.par.Mid, X.C.E0, X.C.PIdx × X.Wp,
    idxAt X.C (fun z => X.rc (X.stOf z).2) (X.bt.baseOut X.C.E0 X.A1 fun w => X.msg w.1)⟩

/-- The block's link. -/
def link : IOR.Link Kc X.m0.J X.m1.J :=
  X.m0.lift X.m1.A (X.bt.batt X.C.E0)
    (idxH X.C (X.bt.hon X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1))
    (idxExt X.C fun _ _ _ wp => wp) (X.bt.nums X.C.E0 Kc)

/-- the entries that the block reads: the matrix, and the entries in Rd -/
def RdJ : X.bt.J → Prop := Sum.elim (fun _ => True) X.Rd

/-- The letters of its item "masked messages". -/
def mask : IOR.MaskData X.link.R X.m0.J.W :=
  idxMask X.C X.S (X.bt.maskData X.C.E0 (fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1) X.RdJ)

/-- The conditions on the own entries: on places alone. -/
structure Own : Prop where
  inj : Function.Injective X.wAt
  own : ∀ i, X.Rd (X.wAt i)
  rdM : ∀ a, X.Rd (X.μAt a)
  wM  : ∀ i a, X.wAt i ≠ X.μAt a

variable (St₁ : Type) (fz : X.bt.par.Mid → St₁)
  (Az : IOR.Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp)))

/-- Rows on all entries, beside Az. -/
@[reducible] def tgt : LdStage E Kc :=
  ⟨X.S, X.Xr × St₁, X.C.E0, X.C.PIdx × X.Wp, claimRels X.RowsOK Az⟩

/-- What is left goes over into Az. -/
structure Ends : Prop where
  fw   : ∀ z y w, X.m1.A.rel z y w → Az.rel (fz z) y w
  bw   : ∀ z y w,
    X.m1.A.on (z, y) → X.RowsOK (X.stOf z).1 w.1 → Az.relR (fz z, y) w → X.m1.A.relR (z, y) w
  on   : ∀ z y, X.m1.A.on (z, y) → Az.on (fz z, y)
  core : ∀ w, Az.core w = X.m1.A.core w

/-- the two steps -/
def stepIn : LdMv X.src X.m0 :=
  .step X.src X.m0 (sideF X.S fun x => (x.2.1, (x.1, x.2.2))) (sideG X.S (ExtMap.id X.C.E0))
    (sideM X.S (fun x => (x.2.1, (x.1, x.2.2))) fun _ w => w.2) (sideB X.S fun _ w => w.2)
def stepOut : LdMv X.m1 (X.tgt St₁ Az) :=
  .step X.m1 (X.tgt St₁ Az) (sideF X.S fun z => ((X.stOf z).1, fz z)) (sideG X.S (ExtMap.id X.C.E0))
    (sideM X.S (fun z => ((X.stOf z).1, fz z)) fun _ w => w.2) (sideB X.S fun _ w => w.2)

/-- The three moves. -/
def prog : LdProg X.src (X.tgt St₁ Az) :=
  (((LdProg.nil X.src).snoc X.stepIn).snoc (.sub X.m0 X.m1 (.one X.link))).snoc
    (X.stepOut St₁ fz Az)

end LdTenD

namespace Spec
open IOR

/-- The conditions on places give the block's conditions, at all states. -/
def ldSegRef_tn_own : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenD E Kc), X.Own → X.bt.OwnOK X.RdJ

/-- The last stage is the stage at which a closing begins. -/
def ldSegRef_tn_bat : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenD E Kc) [Fintype X.Bn] (Zr : Evader E X.Bn)
      (St₁ : Type) (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))),
    X.tgt St₁ Az = (⟨X.S, X.Bn, X.Sb, X.sl, Zr, St₁, X.C.PIdx × X.Wp, X.C.E0, Az⟩ : LdBatD E Kc).src

/-- All that the list of moves asks. -/
def ldSegRef_tn_hyp : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenD E Kc) (St₁ : Type) (fz : X.bt.par.Mid → St₁)
      (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))),
    2 ≤ X.n → X.Z.OK → X.Ends St₁ fz Az → (X.prog St₁ fz Az).Hyp

/-- States, under the hypotheses below: the block's link is a masked block. -/
def ldSegRef_tn_goodM : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenD E Kc),
    2 ≤ X.n → X.Z.OK → X.Own → X.link.GoodM X.mask

def ldSegRef_tn_zk : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenD E Kc) (St₁ : Type) (fz : X.bt.par.Mid → St₁)
      (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))) (base : MaskFact X.src.J.W → Prop),
    2 ≤ X.n → X.Z.OK → X.Own → X.stepIn.After base X.mask.fact → (X.prog St₁ fz Az).Zk base

def ldSegRef_tn_kinds : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenD E Kc) (St₁ : Type) (fz : X.bt.par.Mid → St₁)
      (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))),
    (X.prog St₁ fz Az).All fun t => t = .send ∨ t = .sub ∨ t = .step

def ldSegRef_tn_nums : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenD E Kc) (St₁ : Type) (fz : X.bt.par.Mid → St₁)
      (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))),
    (X.prog St₁ fz Az).nAll = X.k + 2 ∧ (X.prog St₁ fz Az).pBad = 0 ∧ (X.prog St₁ fz Az).pHid = 0

end Spec
end Cb
