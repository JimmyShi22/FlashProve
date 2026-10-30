-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPlanRows.lean: assembly of the holographic IOP from its sub-protocols: the object
with the terms that the library builds for its sub-protocols (`LdObjT`), the last part of both tests
for linear constraints (their closings) at the plan without a splitting, "the rest" of each plan one
more test on one group of oracle messages.

Definitions, one statement and its proof.
Why: in Cb/Obj/LdObjectPlan.lean (which says what object, closing and plan are) each plan ends in a
closing Q' of what the preamble left: a parameter with properties (it says what the preamble left;
it meets its conditions, `Q'.OK`; its demand; online also: knowledge sound for every vector of
statements, an honest side for a batch). Here Q' is a term: the rows that the preamble left, as rows
on one group of all oracle messages that are still open, one test on that group, then nothing
(Cb/Ld/LdLinClosePlanOne.lean: `X.one`; for a batch Cb/Ld/LdLinClosePlanOneB.lean: `X.oneA`,
`X.oneV`: run in every slot).

Main names:
  `LdObjR F E`: `LdObjD`; for each plan: the plan, its first two tests (TP₀, TB₀: their own "rest"
    is not read), the third test X; offline: where the named entries of weights-formedness stand
    (nAt); online: the rows that a request leaves (rowsB, tgB) and its "rest" as a form (slB).
  `R.HypR L`: `LdObjD.HypD L`, and `R.HypPl`: conditions on places, numbers and forms alone, but for
    the online clauses abRel, abRelR, restVal (see Limits) and the clauses on demands q₀is, q₀Be,
    qaOK:
    offline: the further oracles' demand is "nothing"; the named entries stand where nAt says; the
      plan's form restG is the mask part of the tensor row; the places that it reads are kept at the
      first bridge and lie in the second group; the places of the filed rows are kept at both
      bridges; the third test takes all rows and keeps nothing; four families of inequalities;
    online: all members of the first group are shared; what the request leaves says exactly "the
      rows rowsB hold"; their places are kept at both bridges; restG is the form slB, which is
      "rest", and its places lie in the second group; the third test takes all rows and keeps
      nothing; `q₀Be`, `qaOK`; 1 ≤ N; four families of inequalities.
  `R.Hyp L`: `R.HypR L`, and the seven tests on groups, each OK.
  `Spec.ldObjR_hyp`: `R.Hyp L` ⇒ `R.toP.Hyp L` (`R.toP : LdObjP`, Cb/Obj/LdObjectPlan.lean).

So offline no hypothesis is left that speaks of what a joint of a closing says.

Notation: `L`: a natural number (`LdCf.OK L`, Cb/Obj/LdObjectConf.lean, says that it bounds the
lists at the radius of decoding); `wX`, `wXB`: the last argument (`w₀`) of the closings `X.one`,
`XB.one` (`LdRowsD.one`, Cb/Ld/LdLinClosePlanOne.lean); `x₀`: fixed values for what a slot owns
(`LdLinPlT.repX`, Cb/Ld/LdLinCloseVLin.lean); `R.TP₀.D₁.need` .. (`LdRunD.need`,
Cb/Ld/LdLinCloseDemand.lean): the bound after one more test; `R.Sn.tW a`, `R.Sn.tU a`, `R.Sn.tO a`
(online `R.SnB.`): natural numbers (`LdLinP.Snd`, Cb/Ld/LdLin.lean: numbers of long positions that
the encodings bear).

Limits: online three clauses are left that say what fields of the request's last claims are (abRel,
abRelR: what is left says exactly "the rows hold"; restVal: "rest" is the given form): they are the
request's to show.
(For the end of a request, `R : LdORE` (Cb/Obj/LdObjectReqEnd.lean), the two facts on `R.O` under
them, on `restM` and on `more`, are proved: Cb/Obj/LdObjectPartBatRe.lean: `ldPartBatRe_facts`; not
wired in here.)
plRB, plSB (places of rows and of "rest") are asked at all states: harmless with one group for all
that is left and forms of public support; a trap for a rest sorted into several groups. "One group
for all that the preamble left" is the only plan here, and not only the simplest choice: as the
lookups' supports stand (`LdWfP.Lks.OK.supR`, Cb/Ld/LdWfBlocks.lean), every filed row of
weights-formedness reads the body's and the masks' oracle messages; were these in two groups, every
such row would be a row on two groups and would have to be split first.
Proofs among the data, among them: those of the plans' and tests' own records (among them: every
oracle message is a member of the test's group or kept).
What the head of Cb/Obj/LdObjectPlan.lean declares under "Limits" holds here too: a write-up
of ours (lean/CREDITS.md) has another plan for the closing of the test for linear
constraints: one splitting, in the shared part. That plan is not the one under this file (here: the
plan without a splitting).
That `R.Hyp L` can be met is not shown in this file (as the head of Cb/Obj/LdObjectTerms.lean says
of `T.Hyp L`). No instance that meets the hypotheses of `ldObjR_hyp` is part of this library; as far
as the library shows, this theorem may hold of nothing. These hypotheses have not been met by a
request that says something, nor by any request in this library.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Obj.LdObjectPlan
import Cb.Obj.LdObjectWfRowsProofs
import Cb.Obj.LdObjectWfRestProofs
import Cb.Ld.LdLinClosePlanOneProofs
import Cb.Ld.LdLinClosePlanOneBProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The object, "the rest" of each plan one more test: the data. -/
structure LdObjR (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    extends LdObjD F E where
  /-- offline -/
  p    : LdLinPl W.O.toC
  TP₀  : LdLinPlT p
  nAt  : W.P.N → W.P.S.Ent
  X    : LdRowsD p.S₂ W.O.toC.E₀ W.O.toC.Wpa (p.rowsL (W.rowsA nAt))
  wX   : (p.S₂.sub X.kp).Wit × W.O.toC.Wpa
  /-- online -/
  pB   : LdLinPl on.ol.toC
  TB₀  : LdLinPlT pB
  RwB  : Type
  [finRwB : Fintype RwB]
  rowsB : RwB → Slf E on.ol.toC.Sta on.ol.toC.Sa.Ent
  tgB  : on.ol.toC.Sta → RwB → E
  slB  : Slf E on.ol.toC.Sta on.ol.toC.Sa.Ent
  XB   : LdRowsD pB.S₂ on.ol.toC.E₀ on.ol.toC.Wpa (pB.rowsL rowsB)
  wXB  : (pB.S₂.sub XB.kp).Wit × on.ol.toC.Wpa
  q₀B  : Finset on.ol.toC.E₀.Pos → Prop
  baB  : on.ol.toC.Sa.O → ℕ
  x₀   : (TB₀.withRest (XB.one tgB wXB)).St₁ × on.ol.toC.S.Smp
  y₀   : (on.ol.toC.E₀.prod on.ol.toC.S.ext).Str

attribute [instance] LdObjR.finRwB

namespace LdObjR
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R : LdObjR F E)

/-- The object with both closings at the plan. -/
def toP : LdObjP F E :=
  { R.toLdObjD with
    p := R.p
    TP := R.TP₀.withRest (R.X.one R.W.tgA R.wX)
    b' := fun _ => R.X.t
    pB := R.pB
    TB := R.TB₀.withRest (R.XB.one R.tgB R.wXB)
    q₀B := R.q₀B
    bB' := R.XB.bOne R.N
    baB := R.baB
    tie' := fun _ _ _ _ => True
    cA' := (R.XB.oneA R.wXB).cA
    same' := (R.XB.oneA R.wXB).same
    x₀ := R.x₀
    y₀ := R.y₀
    QV' := R.XB.oneV R.N R.q₀B R.wXB }

/-- The conditions on places, numbers and forms of the two plans. -/
structure HypPl : Prop where
  /-- offline -/
  q₀is   : R.q₀ = fun U => U = ∅
  entAt  : R.W.P.EntAt R.nAt
  restIs : R.p.restG = R.p.restOf (R.W.restF R.nAt)
  plW    : ∀ i,
    ∃ h : R.p.kp₁
        (.inl (.inl
            (.inl (R.nAt (R.W.P.wAt (pIx R.W.P.bt.fmt (pdPlains E R.W.P.bt.n R.W.P.bt.k) i))).1))),
      R.p.G₂.mem ⟨_, h⟩
  plC    : ∀ (q : Fin (R.W.P.n + 1)) n,
    R.W.P.gC q n → ∃ h : R.p.kp₁ (.inl (.inl (.inl (R.nAt n).1))), R.p.G₂.mem ⟨_, h⟩
  plR    : ∀ (r : R.W.RB) n,
    R.W.P.gR r.1.1 r.2 n → ∃ h : R.p.kp₁ (.inl (.inl (.inl (R.nAt n).1))), R.p.kp₂ ⟨_, h⟩
  nowX   : ∀ b, R.X.now b
  kpX    : ∀ o, ¬ R.X.kp o
  needA  : ∀ a, R.TP₀.D₁.need (R.TP₀.D₂.need fun _ => R.X.t) (.inl (.inl (.inl a))) ≤ R.Bw.t a
  needW  : ∀ a, R.TP₀.D₁.need (R.TP₀.D₂.need fun _ => R.X.t) (.inl (.inl (.inr a))) ≤ R.Sn.tW a
  needU  : ∀ a, R.TP₀.D₁.need (R.TP₀.D₂.need fun _ => R.X.t) (.inl (.inr a)) ≤ R.Sn.tU a
  needO  : ∀ a, R.TP₀.D₁.need (R.TP₀.D₂.need fun _ => R.X.t) (.inr a) ≤ R.Sn.tO a
  /-- online -/
  shared : R.pB.Shared
  abRel  : ∀ sa y m wp,
    R.on.ol.toC.Ab.rel sa y (m, wp) ↔ rowsHold R.rowsB R.tgB sa (R.on.ol.toC.Sa.ents m)
  abRelR : ∀ sa y m wp,
    R.on.ol.toC.Ab.relR (sa, y) (m, wp) ↔ rowsHold R.rowsB R.tgB sa (R.on.ol.toC.Sa.ents m)
  plRB   : ∀ b st (a : R.on.ol.toC.Sa.O) j,
    R.rowsB b st ⟨a, j⟩ ≠ 0 → ∃ h : R.pB.kp₁ (.inl (.inl (.inl a))), R.pB.kp₂ ⟨_, h⟩
  restIsB : R.pB.restG = R.pB.restOf R.slB
  restVal : ∀ sa ma, R.on.ol.toC.rest sa ma = R.slB.val sa (R.on.ol.toC.Sa.ents ma)
  plSB   : ∀ st (a : R.on.ol.toC.Sa.O) j,
    R.slB st ⟨a, j⟩ ≠ 0 → ∃ h : R.pB.kp₁ (.inl (.inl (.inl a))), R.pB.G₂.mem ⟨_, h⟩
  nowXB  : ∀ b, R.XB.now b
  kpXB   : ∀ o, ¬ R.XB.kp o
  q₀Be   : R.q₀B ∅
  qaOK   : ∀ W, R.on.ol.toC.Sa.qFam R.q₀B R.baB W → R.qaB W
  oneN   : 1 ≤ R.N
  needNA : ∀ a,
    R.TB₀.D₁.need (R.TB₀.D₂.needV R.N (fun a => R.on.ol.toC.isSh a.1) (R.XB.bOne R.N))
        (.inl (.inl (.inl a))) ≤ R.baB a
  needNW : ∀ a,
    R.TB₀.D₁.need (R.TB₀.D₂.needV R.N (fun a => R.on.ol.toC.isSh a.1) (R.XB.bOne R.N))
        (.inl (.inl (.inr a))) ≤ R.SnB.tW a
  needNU : ∀ a,
    R.TB₀.D₁.need (R.TB₀.D₂.needV R.N (fun a => R.on.ol.toC.isSh a.1) (R.XB.bOne R.N))
        (.inl (.inr a)) ≤ R.SnB.tU a
  needNO : ∀ a,
    R.TB₀.D₁.need (R.TB₀.D₂.needV R.N (fun a => R.on.ol.toC.isSh a.1) (R.XB.bOne R.N)) (.inr a) ≤
      R.SnB.tO a

/-- all but the seven tests -/
structure HypR (L : ℕ) : Prop where
  base   : R.toLdObjD.HypD L
  pl     : R.HypPl

/-- All hypotheses: `HypR`, and the seven tests on groups. -/
structure Hyp (L : ℕ) : Prop where
  r      : R.HypR L
  close  : R.Kc.OK
  test₁  : R.TP₀.D₁.OK
  test₂  : R.TP₀.D₂.OK
  test₃  : R.X.run.OK
  test₁B : R.TB₀.D₁.OK
  test₂B : R.TB₀.D₂.OK
  test₃B : R.XB.run.OK

end LdObjR

def Spec.ldObjR_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] : Prop :=
  ∀ (R : LdObjR F E) (L : ℕ), R.Hyp L → R.toP.Hyp L

theorem ldObjR_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldObjR_hyp F E := by
  intro R L h
  obtain ⟨a1, a2, a3⟩ := ldOWfRows_three
    F E R.W R.nAt R.p R.X R.wX h.r.pl.entAt h.r.pl.nowX h.r.pl.kpX h.r.pl.plR h.test₃
  obtain ⟨b1, b2, b3⟩ := ldRowsOne_three E _ _ _ _ R.on.ol.toC R.pB R.RwB R.rowsB R.tgB R.XB R.wXB
    R.q₀B h.r.pl.nowXB h.r.pl.kpXB h.r.pl.abRel h.r.pl.abRelR h.r.pl.plRB h.test₃B h.r.pl.q₀Be
  have hle : ∀ o, R.XB.t ≤ R.XB.bOne R.N o := by
    intro o
    have h1 :=
      ldDemandLe_need E _ R.XB.run R.N (fun a => R.on.ol.toC.isSh a.1.1) (fun _ => 0) o h.r.pl.oneN
    have hm : R.XB.G.mem o := (R.XB.hc o).resolve_right (h.r.pl.kpXB o)
    have h2 : R.XB.run.need (fun _ => 0) o = R.XB.t := by
      unfold LdRunD.need
      rw [if_pos hm, dif_neg (h.r.pl.kpXB o)]
      rfl
    exact h2 ▸ h1
  exact
    { r :=
        { base := h.r.base
          rest := ldOWfRest_is F E R.W R.nAt R.p h.r.pl.entAt h.r.pl.restIs h.r.pl.plW h.r.pl.plC
          saysA := a1
          left := a2
          leftQ := by
            intro V hV
            have := a3 V hV
            show R.p.S₂.qFam R.q₀ _ V
            rw [h.r.pl.q₀is]
            exact this
          needA := h.r.pl.needA
          needW := h.r.pl.needW
          needU := h.r.pl.needU
          needO := h.r.pl.needO
          shared := h.r.pl.shared
          restB :=
            ldRest_is E _ _ _ _ R.on.ol.toC R.pB R.slB h.r.pl.restIsB h.r.pl.restVal h.r.pl.plSB
          saysAB := b1
          leftB := b2
          leftQB := fun V hV => ⟨(b3 V hV).1, fun a => ((b3 V hV).2 a).trans (hle a)⟩
          leftKB := ldRowsOneB_kb E _ _ _ _ _ _ R.XB R.wXB R.N h.r.pl.kpXB h.test₃B
          leftV := ldRowsOneB_v E _ _ _ _ R.on.ol.toC R.pB _ _ _ R.XB R.wXB R.N R.q₀B
            h.r.pl.kpXB h.test₃B h.r.pl.q₀Be
          tieC := fun _ _ _ _ => trivial
          qaOK := h.r.pl.qaOK
          oneN := h.r.pl.oneN
          needNA := h.r.pl.needNA
          needNW := h.r.pl.needNW
          needNU := h.r.pl.needNU
          needNO := h.r.pl.needNO }
      close := h.close
      test₁ := h.test₁
      test₂ := h.test₂
      test₁B := h.test₁B
      test₂B := h.test₂B }

end Cb
