-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBattVSeg.lean: the batching of a segment's tensor rows on the encoded index, with a value
shown, beside the rows of the body, as a list of moves.

A batching step of an interactive oracle proof (Cb/Ld/LdBattV.lean) as it is placed inside the
protocol for one request. The linear claims that it batches read the matrix of the encoded index, an
oracle beside the prover's current oracle messages. The step stands between two changes of the
statement's form that have no round.
Definitions and statements; the proofs are in Cb/Ld/LdBattVSegProofs.lean.
It uses Cb/Ld/LdBattV.lean (the block, at the base, for each fixed tuple), Cb/Ld/LdWfIdx.lean
(claims that read the encoded index: the index is a further oracle, decoded by the statement with
its record) and Cb/Req1/LdSeg.lean, Cb/Req1/LdReq.lean (stages, moves, what zero knowledge asks). It
is the analogue of Cb/Req1/LdSegRefTen.lean for the second form of the batching
(Cb/Ld/LdBattV.lean); names are the same wherever the thing is the same.

At the end of a body all that is left of the segment's own oracle messages are rows on all entries.
Beside them are claims on the encoded index: tensor rows at points, one for each sumcheck that
ended at a map of the index, each with a mask form and a public target. They are batched. Two rows
come out:
  the row on the hiding coefficients and the incoming masks joins the family of rows that rides: one
    more row for the closing (`X.BnO` = X.Bn ⊕ Unit, `X.SbO`, `X.slO`; the new form: `X.slA`, its
    target: `X.tA`). It reads no entry of the index, and (under `X.Own`) not the inner entry;
  the tensor row at the last point is no row of this closing: it is pending and rides on, in "what
    is left" (`X.left`). Of all oracle messages it reads the one inner entry, at `X.cAt`.

The data: `LdTenVD` (`wAt`: the places of the hiding coefficients). `wAt` and `cAt` go into any open
oracle messages: nothing is wired. In the protocol that we follow wAt lies in the segment's own
messages, cAt in the message that holds the index's masks, and the incoming forms' places μAt in the
segment's own messages.
As in `LdTenD` (Cb/Req1/LdSegRefTen.lean) the incoming mask forms are coefficients on names Nm (mf
st q : Nm → E), laid at entries by a fixed map `μAt`: the state chooses coefficients, not places. So
what the block asks at all states are conditions on places (`X.Own`).
The column factors are eq(point, ·), as in `LdTenD` (field `pt`): narrower than the block at the
base, which takes any vector on the columns.
`X.Mid`: the explicit part that the block leaves (state with the riding rows' explicit part, seed,
ε, the point with β, the last value, the value shown): it is where `LdTenD` has X.bt.par.Mid.

The three moves (`X.prog`; a move: `LdMv`, Cb/Req1/LdSeg.lean; a stage: `LdStage`,
Cb/Req1/LdSegKit.lean):
  step, `X.src` → `X.m0` (no round): re-bracketing: the rows go inside the joint that rides along in
    the block;
  sub, `X.m0` → `X.m1` (k + 4 rounds): the block, lifted twice: the index decoded by the statement;
    over the oracle messages of the stage;
  step, `X.m1` → `X.tgt` (no round): the rows come out again, with the new row; what is left is
    written as Az.

Main names:
  `Spec.ldBattVSeg_hyp`: `X.prog.Hyp` from: 2 ≤ n; the evader's law (`X.Z.OK`: `Evader.OK`,
    Cb/Gen/BatEvader.lean); `X.Ends`.
  `Spec.ldBattV_good` (= `Spec.ldBattVSeg_goodM`): the block's link is a masked block, with the
    letters `X.mask`, from 2 ≤ n, the evader's law, `X.Own`: complete; round-by-round knowledge
    sound with the extractor "the pairs stay" and the errors of Cb/Ld/LdBattV.lean; the item "masked
    messages" on the k n + 3 own entries. (`GoodM`, `MM`: told in the head of Cb/Ld/LdBattV.lean.)
  `Spec.ldBattVSeg_two`: two holders: under `X.Own`, and if Rd₁ and Rd₂ hold of every entry in
    `X.Rd`: in every set of facts closed under joining (in this sense: `MaskFact.JCl`,
    Cb/Req1/LdSegFreshS.lean), `X.mask.fact` follows from two wide facts of the stage `X.m0`
    (Cb/Req1/LdSegCarry.lean): one whose own entries are the places wAt, one whose own entry is cAt
    (both in the form "a vector laid at places"); each may forget its own holder's pads and encoding
    randomness.
  `Spec.ldBattVSeg_zk`: `X.prog.Zk base` from these (2 ≤ n, the evader's law, `X.Own`) and: the fact
    that the block needs is fresh before it.
  `Spec.ldBattVSeg_kinds`, `Spec.ldBattVSeg_nums`: kinds (every move is a send, a sub or a step); k
    + 4 rounds, nothing withheld (in this sense:
    `(X.prog St₁ fz Az).pBad = 0 ∧ (X.prog St₁ fz Az).pHid = 0`).

Notation: `S`: a signature (`Sig E`): the stage's oracle messages; `C`: a configuration (`ConfigurationWithOutOfDomainSample`,
Hiop/RecConf.lean): the encoded index's; `Wp`: the further witness beside the prover encoded index;
`Bn`, `Sb`, `sl`: the rows that ride along: names, types of states, forms (`Slf`); `n`: the largest
degree of a round polynomial of a column variable (Cb/Ld/LdBattV.lean); `Kc`: the type into which
the joints' `core` maps.

Limits: the pending rows of earlier segments are not among the claims Q: they ride in "what else is
claimed" (A0), as in Cb/Req1/LdSegRefTen.lean; `Q` and `A0` are free fields of `LdTenVD`.
This file does not say that cAt stands in an oracle message that outlives this closing, and wAt, μAt
in members of its group. It does not say that entries of the index's mask message used by different
segments differ. It does not say that the two wide facts hold. It says nothing on the index's own
test.
The list always runs the block, also if there is no claim (Q empty): then k + 4 idle rounds, and a
pending row with the row vector 0. The protocol that we follow skips the step in a segment without
tensor rows: a matter of the body that calls the list.
In files of their own: that the list does not look at other blocks' masks (Cb/Ld/LdBattVLook.lean:
`X.carry2`, `ldBattVSeg_carry`); what is left on the kept messages (Cb/Ld/LdBattVKeep.lean); from
wide facts before the list to the block's fact (Cb/Ld/LdBattVCarry.lean: `ldBattVSeg_in`,
`ldBattVSeg_pair`); format (Cb/Ld/LdBattVFmt.lean); errors, as probabilities, at most a bound,
countability (Cb/Ld/LdBattVBelow.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReq
import Cb.Ld.LdBattV
import Cb.Ld.LdWfIdx
import Cb.Ld.LdBatPeel
import Cb.Ld.LdRng
import Cb.Req1.LdSegCarry
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.RngPk
open scoped ENNReal

/-- The batching of tensor rows with a value shown, beside the rows of a body: the data. -/
structure LdTenVD (E Kc : Type) [Field E] [Fintype E] : Type 1 where
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
  /-- the claims -/
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
  /-- the places of the own masks: the hiding coefficients; the one inner entry -/
  wAt : PIdx (List.replicate k (pfCube E n) ++ [pDummy E 1]) → S.Ent
  cAt : S.Ent
  /-- what else is claimed -/
  A0  : IOR.Rels Kc St C.E0 ((C.Msg × S.Msg) × Wp)
  /-- the entries of the messages that the block reads -/
  Rd  : S.Ent → Prop

attribute [instance] LdTenVD.finRw LdTenVD.finQ LdTenVD.finNm

namespace LdTenVD
variable {E Kc : Type} [Field E] [Fintype E] (X : LdTenVD E Kc)

/-- the explicit part of the rows -/
abbrev Xr : Type := (X.Bn → E) × (∀ b, X.Sb b)
/-- the rows hold -/
def RowsOK (x : X.Xr) (m : X.S.Msg) : Prop := Slf.All X.sl x (X.S.ents m)

/-- The parameters of the block. -/
def bt : BattVPar E where
  St := X.Xr × X.St
  J := (X.Rw × (Fin X.k → Bool)) ⊕ X.S.Ent
  Rw := X.Rw
  k := X.k
  mAt := Sum.inl
  Q := X.Q
  g := fun st => X.g st.2
  cf := fun st q => Alg.eqk (X.pt st.2 q)
  slM := fun q st => Sum.elim (fun _ => 0) (placed X.μAt (X.mf st.2 q))
  Z := X.Z
  n := X.n
  wAt := fun i => Sum.inr (X.wAt i)
  cAt := Sum.inr X.cAt

/-- the entries, from the tuple (message of the index, messages) -/
def msg (um : X.C.Msg × X.S.Msg) : X.bt.J → E := Sum.elim (X.mat um.1) (X.S.ents um.2)

/-- The tensor rows hold: for each claim, < g ⊗ eq(point, ·), matrix > + < incoming mask form,
entries > is the public target. -/
def TenOK (x : (X.Q → E) × X.St) (um : X.C.Msg × X.S.Msg) : Prop :=
  ∀ q, tenAt X.bt.mAt (X.g x.2 q) (X.pt x.2 q) (X.msg um) +
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

/-- The explicit part that the block leaves. -/
abbrev Mid : Type := X.bt.our.par.Out

/-- the state in it -/
def stOf (z : X.Mid) : X.Xr × X.St := X.bt.stOf z

/-- Rows on all entries, beside the claims on the index. -/
@[reducible] def src : LdStage E Kc :=
  ⟨X.S, X.Xr × ((X.Q → E) × X.St), X.C.E0, X.C.PIdx × X.Wp,
    claimRels X.RowsOK (idxAt X.C (fun x => X.rc x.2) X.tenA)⟩
/-- the two stages of the block -/
@[reducible] def m0 : LdStage E Kc :=
  ⟨X.S, (X.Q → E) × (X.Xr × X.St), X.C.E0, X.C.PIdx × X.Wp,
    idxAt X.C (fun x => X.rc x.2.2) (X.bt.baseIn X.C.E0 X.A1 fun w => X.msg w.1)⟩
@[reducible] def m1 : LdStage E Kc :=
  ⟨X.S, X.Mid, X.C.E0, X.C.PIdx × X.Wp,
    idxAt X.C (fun z => X.rc (X.stOf z).2) (X.bt.baseOut X.C.E0 X.A1 fun w => X.msg w.1)⟩

/-- The block's link. -/
def link : IOR.Link Kc X.m0.J X.m1.J :=
  X.m0.lift X.m1.A (X.bt.battV X.C.E0)
    (idxH X.C (X.bt.hon X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1))
    (idxExt X.C fun _ _ _ wp => wp) (X.bt.nums X.C.E0 Kc)

/-- the entries that the block reads: the matrix, and the entries in Rd -/
def RdJ : X.bt.J → Prop := Sum.elim (fun _ => True) X.Rd

/-- The letters of its item "masked messages". -/
def mask : IOR.MaskData X.link.R X.m0.J.W :=
  idxMask X.C X.S (X.bt.maskData X.C.E0 (fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1) X.RdJ)

/-- The conditions on the own entries: on places alone. -/
structure Own : Prop where
  inj  : Function.Injective X.wAt
  wc   : ∀ i, X.wAt i ≠ X.cAt
  own  : ∀ i, X.Rd (X.wAt i)
  ownC : X.Rd X.cAt
  rdM  : ∀ a, X.Rd (X.μAt a)
  wM   : ∀ i a, X.wAt i ≠ X.μAt a
  cM   : ∀ a, X.cAt ≠ X.μAt a

/-! ### What comes out -/

/-- The new row: the value form of the hiding polynomial, laid at wAt, and ε γ_1 .. γ_k times the
combination of the incoming forms, laid at μAt; its public target. -/
def slA : Slf E X.Mid X.S.Ent := fun z =>
  placed (fun i => X.wAt (pIx (X.bt.fmt ++ [pDummy E 1]) (X.bt.our.datD z.st) i))
      (hSl (X.bt.our.par.vars z.st) (X.bt.our.par.hp z.st z.pt)) +
    placed X.μAt fun a => z.eps * (∏ i, X.bt.outPt z i) * ∑ q, X.bt.chi z q * X.mf (X.stOf z).2 q a
def tA (z : X.Mid) : E := z.fin - z.eps * X.bt.shown z
/-- The places that the new row names: those of the hiding coefficients and of the incoming forms.
The inner entry's place is none of them (under `X.Own`: `wc`, `cM`). -/
def NamedA (n : X.S.Ent) : Prop := (∃ i, X.wAt i = n) ∨ ∃ a, X.μAt a = n

/-- The family of rows at the output: the rows that rode along, and the new row. -/
abbrev BnO : Type := X.Bn ⊕ Unit
def SbO : X.BnO → Type
  | .inl b => X.Sb b
  | .inr _ => X.Mid
def slO : ∀ b, Slf E (X.SbO b) X.S.Ent
  | .inl b => X.sl b
  | .inr _ => X.slA
abbrev XrO : Type := (X.BnO → E) × (∀ b, X.SbO b)
def RowsOKO (x : X.XrO) (m : X.S.Msg) : Prop := Slf.All X.slO x (X.S.ents m)
/-- their explicit part, read off what the block leaves -/
def rowsOf (z : X.Mid) : X.XrO :=
  (fun b => match b with | .inl b => (X.stOf z).1.1 b | .inr _ => X.tA z, fun b => match b with | .inl b => (X.stOf z).1.2 b | .inr _ => z)

/-- The pending row: < row vector ⊗ eq(γ, ·), matrix > + β · (the inner entry) = the value shown. -/
def PendOK (z : X.Mid) (um : X.C.Msg × X.S.Msg) : Prop := X.bt.RowB z (X.msg um)

/-- What is left beside the rows: the index is decoded; what else was claimed; the pending row. -/
def leftA : IOR.Rels Kc X.Mid X.C.E0 ((X.C.Msg × X.S.Msg) × X.Wp) :=
  ⟨fun z y w => X.A0.rel (X.stOf z).2 y w ∧ X.PendOK z w.1,
    fun a w => X.A0.relR ((X.stOf a.1).2, a.2) w ∧ X.PendOK a.1 w.1,
    fun a => X.A0.on ((X.stOf a.1).2, a.2),
    X.A0.core⟩
def left : IOR.Rels Kc X.Mid X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp)) :=
  idxAt X.C (fun z => X.rc (X.stOf z).2) X.leftA

variable (St₁ : Type) (fz : X.Mid → St₁) (Az : IOR.Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp)))

/-- The rows of the family at the output, on all entries, beside Az. -/
@[reducible] def tgt : LdStage E Kc :=
  ⟨X.S, X.XrO × St₁, X.C.E0, X.C.PIdx × X.Wp, claimRels X.RowsOKO Az⟩

/-- What is left goes over into Az. -/
structure Ends : Prop where
  fw   : ∀ z y w, X.left.rel z y w → Az.rel (fz z) y w
  bw   : ∀ z y w,
    X.left.on (z, y) → X.RowsOKO (X.rowsOf z) w.1 → Az.relR (fz z, y) w → X.left.relR (z, y) w
  on   : ∀ z y, X.left.on (z, y) → Az.on (fz z, y)
  core : ∀ w, Az.core w = X.left.core w

/-- the two steps -/
def stepIn : LdMv X.src X.m0 :=
  .step X.src X.m0 (sideF X.S fun x => (x.2.1, (x.1, x.2.2))) (sideG X.S (ExtMap.id X.C.E0))
    (sideM X.S (fun x => (x.2.1, (x.1, x.2.2))) fun _ w => w.2) (sideB X.S fun _ w => w.2)
def stepOut : LdMv X.m1 (X.tgt St₁ Az) :=
  .step X.m1 (X.tgt St₁ Az) (sideF X.S fun z => (X.rowsOf z, fz z)) (sideG X.S (ExtMap.id X.C.E0))
    (sideM X.S (fun z => (X.rowsOf z, fz z)) fun _ w => w.2) (sideB X.S fun _ w => w.2)

/-- The three moves. -/
def prog : LdProg X.src (X.tgt St₁ Az) :=
  (((LdProg.nil X.src).snoc X.stepIn).snoc (.sub X.m0 X.m1 (.one X.link))).snoc
    (X.stepOut St₁ fz Az)

end LdTenVD

namespace Spec
open IOR

/-- The conditions on places give the block's conditions, at all states. -/
def ldBattVSeg_own : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenVD E Kc), X.Own → X.bt.OwnOK X.RdJ

/-- The last stage is the stage at which a closing begins, at the family with the new row: it is
`LdBatD.src`, by definition. -/
def ldBattVSeg_bat : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenVD E Kc) [Fintype X.BnO] (Zr : Evader E X.BnO)
      (St₁ : Type) (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))),
    X.tgt St₁ Az =
      (⟨X.S, X.BnO, X.SbO, X.slO, Zr, St₁, X.C.PIdx × X.Wp, X.C.E0, Az⟩ : LdBatD E Kc).src

/-- The new row of the family is the block's first row, whatever the message of the index. -/
def ldBattVSeg_rowA : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenVD E Kc) (z : X.Mid) (um : X.C.Msg × X.S.Msg),
    X.slA.Holds (X.tA z, z) (X.S.ents um.2) ↔ X.bt.RowA z (X.msg um)
/-- Its form is 0 outside the places of the hiding coefficients and of the incoming forms. -/
def ldBattVSeg_rowA_supp : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenVD E Kc) (z : X.Mid) (n : X.S.Ent),
    (∀ i, X.wAt i ≠ n) → (∀ a, X.μAt a ≠ n) → X.slA z n = 0
def ldBattVSeg_rowA_named : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenVD E Kc) (z : X.Mid) (n : X.S.Ent),
    ¬ X.NamedA n → X.slA z n = 0
/-- The rows at the output hold: the rows that rode along hold, and the block's first row. -/
def ldBattVSeg_rowsO : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenVD E Kc) (z : X.Mid) (um : X.C.Msg × X.S.Msg),
    X.RowsOKO (X.rowsOf z) um.2 ↔ X.RowsOK (X.stOf z).1 um.2 ∧ X.bt.RowA z (X.msg um)

/-- The pending row is a claim in the form in which a later batching takes one (`LdTenD.TenOK`,
`LdTenVD.TenOK`): names Nm' laid by μAt', the coefficient β on the one name ν that is laid at cAt, 0
on the others. -/
def ldBattVSeg_pend : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenVD E Kc) (z : X.Mid) (um : X.C.Msg × X.S.Msg)
      (Nm' : Type) [Fintype Nm'] [DecidableEq Nm'] (μAt' : Nm' → X.S.Ent) (ν : Nm'),
    μAt' ν = X.cAt →
    (X.PendOK z um ↔
      tenAt X.bt.mAt (X.bt.outG z) (X.bt.outPt z) (X.msg um) +
          ∑ j, (Sum.elim (fun _ => 0) (placed μAt' (Pi.single ν (X.bt.beta z))) : X.bt.J → E) j *
            X.msg um j = X.bt.shown z)

/-- What is left is one choice of Az. -/
def ldBattVSeg_ends_left : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenVD E Kc), X.Ends X.Mid id X.left

/-- If 2 ≤ `X.n`, `X.Z.OK` and `X.Ends St₁ fz Az`: all that the list of moves asks (`LdProg.Hyp`)
holds. -/
def ldBattVSeg_hyp : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenVD E Kc) (St₁ : Type) (fz : X.Mid → St₁)
      (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))),
    2 ≤ X.n → X.Z.OK → X.Ends St₁ fz Az → (X.prog St₁ fz Az).Hyp

/-- If 2 ≤ `X.n`, `X.Z.OK` and `X.Own`: the block's link is a masked block. -/
def ldBattVSeg_goodM : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenVD E Kc),
    2 ≤ X.n → X.Z.OK → X.Own → X.link.GoodM X.mask
/-- the same, under the name of the block -/
def ldBattV_good : Prop := ldBattVSeg_goodM

/-- Two holders: under the hypotheses below, the fact that the block needs follows from two wide
facts of its stage: on the hiding coefficients, on the inner entry. -/
def ldBattVSeg_two : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenVD E Kc) (Y : MaskFact X.m0.J.W → Prop)
      (Rd₁ Rd₂ : X.S.Ent → Prop) (Rr₁ Rr₂ : X.S.O → Prop),
    X.Own → (∀ n, X.Rd n → Rd₁ n ∧ Rd₂ n) →
    MaskFact.JCl Y
      (X.m0.wideFact Rd₁ Rr₁ (fun n => ∃ i, X.wAt i = n) (X.bt.WIx → E) fun M =>
        Function.extend X.wAt M fun _ => 0) →
    MaskFact.JCl Y
      (X.m0.wideFact Rd₂ Rr₂ (fun n => ∃ _u : Unit, X.cAt = n) (Unit → E) fun M =>
        Function.extend (fun _ : Unit => X.cAt) M fun _ => 0) →
    MaskFact.JCl Y X.mask.fact

def ldBattVSeg_zk : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenVD E Kc) (St₁ : Type) (fz : X.Mid → St₁)
      (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))) (base : MaskFact X.src.J.W → Prop),
    2 ≤ X.n → X.Z.OK → X.Own → X.stepIn.After base X.mask.fact → (X.prog St₁ fz Az).Zk base

def ldBattVSeg_kinds : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenVD E Kc) (St₁ : Type) (fz : X.Mid → St₁)
      (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))),
    (X.prog St₁ fz Az).All fun t => t = .send ∨ t = .sub ∨ t = .step

def ldBattVSeg_nums : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenVD E Kc) (St₁ : Type) (fz : X.Mid → St₁)
      (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))),
    (X.prog St₁ fz Az).nAll = X.k + 4 ∧ (X.prog St₁ fz Az).pBad = 0 ∧ (X.prog St₁ fz Az).pHid = 0

end Spec
end Cb
