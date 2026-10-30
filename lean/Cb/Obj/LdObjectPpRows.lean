-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPpRows.lean: assembly of the holographic IOP from its sub-protocols: the object at
the plan of a write-up of ours (lean/CREDITS.md; one splitting, the shared one; three
tests), "the rest" one more test on a group: the clauses of `LdObjPp.Hyp` that speak of terms (of
what closes the rest, and
`rest`, `restB`; `rest0`, `sndOK` stay as they are) reduce to conditions on places, numbers and
forms, and to nine tests on groups.

Definitions, one statement and its proof: an assembly. Generic.
A plan (`LdLinPp`, Cb/Ld/LdLinClosePlanP.lean) fixes how the rows that the test for linear
constraints leaves are closed.
Why: `LdObjPp` (Cb/Obj/LdObjectPlanPaper.lean) takes "what closes the rest" (TP.Q'; TB.Q', cA', QV',
tie') as parameters with the whole bundle asked of them (left, leftB, leftQ, leftQB, leftKB, leftV,
saysA, saysAB, tieC). Here they are terms: one test X (XB) on a group of all that is left after the
third test, on the rows that the preamble left; in a session: the fourth kind of group, the group of
what the request leaves beside the messages in the instance's group.
The analogue of Cb/Obj/LdObjectPlanRows.lean (`LdObjR`: the plan without a splitting).

Main names:
  `LdObjRp F E`: data only, but for the proofs among its fields and inside their types (among them
    `LdObjD.ne`; `LdLinPp.hU`, `LdLinPpT.hc₁`, `LdRowsD.hc`): `LdObjD`; Y: the seven standard
    senders; offline: the plan p, its three tests TP₀, nAt, the fourth test X, the free entry n₀ at
    which the splitting's mask stands; online: pB, TB₀, the rows rowsB with targets tgB, the mask
    part as a form slB, XB, n₀B; demands; fixed values.
  `R.HypPl`: the conditions on places, numbers and forms. For each of the two plans: `Plain` (the
    mask entry stands in an oracle message other than G_u, Ω; what the splitting reads), `Kept`; the
    mask entry is a free entry of Ω's family's layout (kIs), what the splitting reads in Ω's family
    is no pad entry (noPad; of the places of G_u, which it reads too, nothing is asked); restG is
    the mask part, read on the instance's group; the places of that form lie in messages kept at
    both shared bridges and in the instance's group; the rows' places lie in messages kept at all
    three bridges; the fourth test takes all rows and keeps nothing; four families of inequalities:
    the write-up's four budgets, by membership: the fold's message: its group's positions
    (needU); the splitting's message: both shared groups': it stands in Ω's family, so its
    inequality is one of needO's (needNO's), beside Ω's own: its shared group's + N times an
    instance's (exactly: needO: `R.TP₀.D₃.need fun _ => R.X.t`; needNO:
    `R.TB₀.D₃.needV R.N (fun a => R.on.ol.toC.isSh a.1.1) (R.XB.bOneP R.N)`); an instance's message:
    its group's (needW); what a preamble leaves: the sum over the groups that hold it (needA).
    Offline also: q₀ is "nothing" (`q₀is`); `EntAt` (`entAt`). Online also: `Shared`; what the
    request leaves says exactly "the rows hold"; demands; 1 ≤ N.
  `R.Hyp L`: `(D.std Y).HypRest L`, `Y.Hyp` (both: Cb/Obj/LdObjectPpCore.lean gives them from the
    hypotheses of `D.CoreJ`, E of characteristic p, at L = 1); `R.HypPl`; nine tests on groups that
    meet their conditions (`D.OK`): the link's; offline four; online four.
  `Spec.ldObjRp_hyp`: `R.Hyp L` ⇒ `R.toPp.Hyp L`. So (`Cb.ldObjPp_hyp`) `R.toPp.toT.Hyp L`.

Zero knowledge of the splitting asks no clause on a fresh mask: kIs, noPad, `Plain` (its field rs₀K)
and the senders' layouts (`Places`, `YW.OK`, `YU.OK`, `YO.OK`, inside `Y.Hyp`) are asked (exactly:
`ldSpV_fresh`, Cb/Ld/LdLinStdSpV.lean; Cb/Obj/LdObjectPaperBatch.lean).

Notation: `L`: a natural number (`LdCf.OK L`, Cb/Obj/LdObjectConf.lean, says that it bounds the
lists at the radius of decoding); `wX`, `wXB`: fixed values: arguments of the closings `X.one`,
`XB.one`.

Limits: one test for "the rest" is narrower than the write-up's theorem, which allows a set
of further groups, each with a whole test of its own, run for every instance; equal at its two uses:
at a request that set is one group (the last segment's), offline one too (the message with the
multiplicities).
The nine `D.OK` are properties of terms here (towers: Cb/Obj/LdObjectPpData.lean). This file does
not say that the conditions can be met together. Nothing forces two different base codes or lengths
for the two shared groups: they are any groups.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Obj.LdObjectPlanPaper
import Cb.Obj.LdObjectPpRest
import Cb.Ld.LdLinCloseDemandLe
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- the data of the plan's tests, with "the rest" := the closing R of the preamble's rows -/
@[reducible] def LdLinPpT.withRest {E ι κ J Y : Type} [Field E]
    [Fintype E] [Fintype Y] [Fintype κ] [Fintype J] {C : LdLinC E ι κ J Y}
    {p : LdLinPp C} (T : LdLinPpT p) {B : Type} {rows : B → Slf E C.Sta p.S₃.Ent}
    {tg : C.Sta → B → E} (R : LdRowsQ p.S₃ C.E₀ C.Wpa rows tg) : LdLinPpT p :=
  { T with Q' := R.Q, fa := R.fx }

/-- The object at the write-up's plan, "the rest" one more test: the data. -/
structure LdObjRp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    extends LdObjD F E where
  Y    : toLdObjD.StdS
  /-- offline -/
  p    : LdLinPp W.O.toC
  TP₀  : LdLinPpT p
  nAt  : W.P.N → W.P.S.Ent
  X    : LdRowsD p.S₃ W.O.toC.E₀ W.O.toC.Wpa (p.rowsL (W.rowsA nAt))
  wX   : (p.S₃.sub X.kp).Wit × W.O.toC.Wpa
  n₀   : Σ a, Y.TS.YO.Fr a
  /-- online -/
  pB   : LdLinPp on.ol.toC
  TB₀  : LdLinPpT pB
  RwB  : Type
  [finRwB : Fintype RwB]
  rowsB : RwB → Slf E on.ol.toC.Sta on.ol.toC.Sa.Ent
  tgB  : on.ol.toC.Sta → RwB → E
  slB  : Slf E on.ol.toC.Sta on.ol.toC.Sa.Ent
  XB   : LdRowsD pB.S₃ on.ol.toC.E₀ on.ol.toC.Wpa (pB.rowsL rowsB)
  wXB  : (pB.S₃.sub XB.kp).Wit × on.ol.toC.Wpa
  n₀B  : Σ a, Y.TB.YO.Fr a
  q₀B  : Finset on.ol.toC.E₀.Pos → Prop
  baB  : on.ol.toC.Sa.O → ℕ
  /-- fixed values -/
  x₀   : on.ol.toC.S.Smp
  y₀   : on.ol.toC.S.ext.Str
  xB   : (TB₀.withRest (XB.one tgB wXB)).StB
  xC   : (TB₀.withRest (XB.one tgB wXB)).StC
  yE   : on.ol.toC.E₀.Str
  sh₀  : on.ol.toC.Sh6
  x₄   : on.ol.toC.P.X4
  y₄   : on.ol.toC.P.E4.Str

attribute [instance] LdObjRp.finRwB

namespace LdObjRp
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R : LdObjRp F E)

/-- The object with both closings at the write-up's plan. -/
def toPp : LdObjPp F E :=
  { R.toLdObjD with
    Y := R.Y
    p := R.p
    TP := R.TP₀.withRest (R.X.one R.W.tgA R.wX)
    b' := fun _ => R.X.t
    n₀ := R.n₀
    pB := R.pB
    TB := R.TB₀.withRest (R.XB.one R.tgB R.wXB)
    q₀B := R.q₀B
    bB' := R.XB.bOneP R.N
    baB := R.baB
    tie' := fun _ _ _ _ => True
    x₀ := R.x₀
    y₀ := R.y₀
    cA' := (R.XB.oneA R.wXB).cA
    same' := (R.XB.oneA R.wXB).same
    xB := R.xB
    xC := R.xC
    QV' := R.XB.oneVP R.N R.q₀B R.wXB
    n₀B := R.n₀B
    yE := R.yE
    sh₀ := R.sh₀
    x₄ := R.x₄
    y₄ := R.y₄ }

/-- The conditions on places, numbers and forms of the two plans. -/
structure HypPl : Prop where
  /-- offline -/
  q₀is   : R.q₀ = fun U => U = ∅
  entAt  : R.W.P.EntAt R.nAt
  plain  : R.p.Plain
  kept   : R.p.Kept
  kIs    : (⟨R.p.k₀.o, R.p.k₀.j⟩ : R.W.O.toC.S.Ent) = R.W.O.toC.eO (R.Y.TS.YO.entF R.n₀)
  noPad  : ∀ n, R.p.Rs₀ (R.W.O.toC.eO n) → R.Y.TS.YO.NoPad n
  restIs : R.p.restG = R.p.restOf (R.W.restF R.nAt)
  plW    : ∀ i,
    ∃ (h₁ : R.p.kp₁
          (.inl (.inl (.inl
                (R.nAt (R.W.P.wAt (pIx R.W.P.bt.fmt (pdPlains E R.W.P.bt.n R.W.P.bt.k) i))).1))))
        (h₂ : R.p.kp₂ ⟨_, h₁⟩),
      R.p.Gc.mem ⟨⟨_, h₁⟩, h₂⟩
  plC    : ∀ (q : Fin (R.W.P.n + 1)) n, R.W.P.gC q n →
    ∃ (h₁ : R.p.kp₁ (.inl (.inl (.inl (R.nAt n).1)))) (h₂ : R.p.kp₂ ⟨_, h₁⟩),
      R.p.Gc.mem ⟨⟨_, h₁⟩, h₂⟩
  plR    : ∀ (r : R.W.RB) n, R.W.P.gR r.1.1 r.2 n →
    ∃ (h₁ : R.p.kp₁ (.inl (.inl (.inl (R.nAt n).1)))) (h₂ : R.p.kp₂ ⟨_, h₁⟩), R.p.kp₃ ⟨⟨_, h₁⟩, h₂⟩
  nowX   : ∀ b, R.X.now b
  kpX    : ∀ o, ¬ R.X.kp o
  needA  : ∀ a,
    R.TP₀.D₁.need (R.TP₀.D₂.need (R.TP₀.D₃.need fun _ => R.X.t)) (.inl (.inl (.inl a))) ≤ R.Bw.t a
  needW  : ∀ a,
    R.TP₀.D₁.need (R.TP₀.D₂.need (R.TP₀.D₃.need fun _ => R.X.t)) (.inl (.inl (.inr a))) ≤ R.Y.tW a
  needU  : ∀ a,
    R.TP₀.D₁.need (R.TP₀.D₂.need (R.TP₀.D₃.need fun _ => R.X.t)) (.inl (.inr a)) ≤ R.Y.tU a
  needO  : ∀ a, R.TP₀.D₁.need (R.TP₀.D₂.need (R.TP₀.D₃.need fun _ => R.X.t)) (.inr a) ≤ R.Y.tO a
  /-- online -/
  shared : R.pB.Shared
  plainB : R.pB.Plain
  keptB  : R.pB.Kept
  kIsB   : (⟨R.pB.k₀.o, R.pB.k₀.j⟩ : R.on.ol.toC.S.Ent) = R.on.ol.toC.eO (R.Y.TB.YO.entF R.n₀B)
  noPadB : ∀ n, R.pB.Rs₀ (R.on.ol.toC.eO n) → R.Y.TB.YO.NoPad n
  abRel  : ∀ sa y m wp,
    R.on.ol.toC.Ab.rel sa y (m, wp) ↔ rowsHold R.rowsB R.tgB sa (R.on.ol.toC.Sa.ents m)
  abRelR : ∀ sa y m wp,
    R.on.ol.toC.Ab.relR (sa, y) (m, wp) ↔ rowsHold R.rowsB R.tgB sa (R.on.ol.toC.Sa.ents m)
  plRB   : ∀ b st (a : R.on.ol.toC.Sa.O) j, R.rowsB b st ⟨a, j⟩ ≠ 0 →
    ∃ (h₁ : R.pB.kp₁ (.inl (.inl (.inl a)))) (h₂ : R.pB.kp₂ ⟨_, h₁⟩), R.pB.kp₃ ⟨⟨_, h₁⟩, h₂⟩
  restIsB : R.pB.restG = R.pB.restOf R.slB
  restVal : ∀ sa ma, R.on.ol.toC.rest sa ma = R.slB.val sa (R.on.ol.toC.Sa.ents ma)
  plSB   : ∀ st (a : R.on.ol.toC.Sa.O) j, R.slB st ⟨a, j⟩ ≠ 0 →
    ∃ (h₁ : R.pB.kp₁ (.inl (.inl (.inl a)))) (h₂ : R.pB.kp₂ ⟨_, h₁⟩), R.pB.Gc.mem ⟨⟨_, h₁⟩, h₂⟩
  nowXB  : ∀ b, R.XB.now b
  kpXB   : ∀ o, ¬ R.XB.kp o
  q₀Be   : R.q₀B ∅
  qaOK   : ∀ W, R.on.ol.toC.Sa.qFam R.q₀B R.baB W → R.qaB W
  oneN   : 1 ≤ R.N
  needNA : ∀ a,
    R.TB₀.D₁.need
        (R.TB₀.D₂.need (R.TB₀.D₃.needV R.N (fun a => R.on.ol.toC.isSh a.1.1) (R.XB.bOneP R.N)))
        (.inl (.inl (.inl a))) ≤ R.baB a
  needNW : ∀ a,
    R.TB₀.D₁.need
        (R.TB₀.D₂.need (R.TB₀.D₃.needV R.N (fun a => R.on.ol.toC.isSh a.1.1) (R.XB.bOneP R.N)))
        (.inl (.inl (.inr a))) ≤ R.Y.tWB a
  needNU : ∀ a,
    R.TB₀.D₁.need
        (R.TB₀.D₂.need (R.TB₀.D₃.needV R.N (fun a => R.on.ol.toC.isSh a.1.1) (R.XB.bOneP R.N)))
        (.inl (.inr a)) ≤ R.Y.tUB a
  needNO : ∀ a,
    R.TB₀.D₁.need
        (R.TB₀.D₂.need (R.TB₀.D₃.needV R.N (fun a => R.on.ol.toC.isSh a.1.1) (R.XB.bOneP R.N)))
        (.inr a) ≤ R.Y.tOB a

/-- All hypotheses, beside whatever the arguments hold as proofs. -/
structure Hyp (L : ℕ) : Prop where
  rest0  : (R.toLdObjD.std R.Y).HypRest L
  sndOK  : R.Y.Hyp
  pl     : R.HypPl
  close  : R.Kc.OK
  test₁  : R.TP₀.D₁.OK
  test₂  : R.TP₀.D₂.OK
  test₃  : R.TP₀.D₃.OK
  test₄  : R.X.run.OK
  test₁B : R.TB₀.D₁.OK
  test₂B : R.TB₀.D₂.OK
  test₃B : R.TB₀.D₃.OK
  test₄B : R.XB.run.OK

end LdObjRp

def Spec.ldObjRp_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Prop :=
  ∀ (R : LdObjRp F E) (L : ℕ), R.Hyp L → R.toPp.Hyp L

theorem ldObjRp_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldObjRp_hyp F E := by
  intro R L h
  obtain ⟨a1, a2, a3⟩ :=
    ldOWfRowsP_three F E R.W R.nAt R.p R.X R.wX h.pl.entAt h.pl.nowX h.pl.kpX h.pl.plR h.test₄
  obtain ⟨b1, b2, b3⟩ := ldRowsOneP_three E _ _ _ _ R.on.ol.toC R.pB R.RwB R.rowsB R.tgB R.XB R.wXB
    R.q₀B h.pl.nowXB h.pl.kpXB h.pl.abRel h.pl.abRelR h.pl.plRB h.test₄B h.pl.q₀Be
  have hle : ∀ o, R.XB.t ≤ R.XB.bOneP R.N o := by
    intro o
    have h1 :=
      ldDemandLe_need E _ R.XB.run R.N (fun a => R.on.ol.toC.isSh a.1.1.1) (fun _ => 0) o h.pl.oneN
    have hm : R.XB.G.mem o := (R.XB.hc o).resolve_right (h.pl.kpXB o)
    have h2 : R.XB.run.need (fun _ => 0) o = R.XB.t := by
      unfold LdRunD.need
      rw [if_pos hm, dif_neg (h.pl.kpXB o)]
      rfl
    exact h2 ▸ h1
  exact
    { r :=
        { rest0 := h.rest0
          sndOK := h.sndOK
          plain := h.pl.plain
          kept := h.pl.kept
          rest := ldOWfRestP_is F E R.W R.nAt R.p h.pl.entAt h.pl.restIs h.pl.plW h.pl.plC
          saysA := a1
          left := a2
          leftQ := by
            intro V hV
            have := a3 V hV
            show R.p.S₃.qFam R.q₀ _ V
            rw [h.pl.q₀is]
            exact this
          kIs := h.pl.kIs
          noPad := h.pl.noPad
          needA := h.pl.needA
          needW := h.pl.needW
          needU := h.pl.needU
          needO := h.pl.needO
          shared := h.pl.shared
          plainB := h.pl.plainB
          keptB := h.pl.keptB
          restB := ldRestP_is E _ _ _ _ R.on.ol.toC R.pB R.slB h.pl.restIsB h.pl.restVal h.pl.plSB
          saysAB := b1
          leftB := b2
          leftQB := fun V hV => ⟨(b3 V hV).1, fun a => ((b3 V hV).2 a).trans (hle a)⟩
          leftKB := ldRowsOneB_kb E _ _ _ _ _ _ R.XB R.wXB R.N h.pl.kpXB h.test₄B
          leftV := ldRowsOneP_v E _ _ _ _ R.on.ol.toC R.pB _ _ _ R.XB R.wXB R.N R.q₀B
            h.pl.kpXB h.test₄B h.pl.q₀Be
          tieC := fun _ _ _ _ => trivial
          qaOK := h.pl.qaOK
          oneN := h.pl.oneN
          kIsB := h.pl.kIsB
          noPadB := h.pl.noPadB
          needNA := h.pl.needNA
          needNW := h.pl.needNW
          needNU := h.pl.needNU
          needNO := h.pl.needNO }
      close := h.close
      test₁ := h.test₁
      test₂ := h.test₂
      test₃ := h.test₃
      test₁B := h.test₁B
      test₂B := h.test₂B
      test₃B := h.test₃B }

end Cb
