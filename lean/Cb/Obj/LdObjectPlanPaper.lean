-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPlanPaper.lean: assembly of the holographic IOP from its sub-protocols: this file
defines the object with the terms that the library builds for its sub-protocols (`LdObjT`) with both
closings of the test for linear constraints at the plan of this protocol's technical report
(lean/CREDITS.md): one splitting, always, the shared one.

Definitions, statements and proofs: an assembly.
The object (`LdObj`, Cb/Obj/LdObject.lean) has, over one configuration, the sub-protocols from which
Hiop/RecBuild.lean builds the holographic IOP. `LdObjT` (Cb/Obj/LdObjectTerms.lean): the object with
the terms that the library builds as its five terms (`wf`, `lin`, `link`, `req`, `linB`); its two
closings (`Qt` offline, `cZ` at N instances) are parameters. A closing is the chain of steps after a
test's core, down to the trivial statement.
A plan fixes how the rows that the test for linear constraints leaves are closed: the groups of
oracle messages, the rows that go to the test on each group, and the messages kept for later tests.
The plan: Cb/Ld/LdLinClosePlanP.lean (its definitions say it): one splitting, in the shared part;
three tests on groups; then Q', which closes what the preamble left.
The analogue of Cb/Obj/LdObjectPlan.lean (the plan without a splitting).

Main names:
  `LdObjPp F E`: `LdObjD` (its own seven senders are not read); Y: the standard senders
    (Cb/Obj/LdObjectSendersLin.lean); for each of the two tests: the plan, its three tests and Q',
    the free entry n₀ at which the mask κ stands; offline `b'`, online `bB'`, `baB` (numbers of
    positions) and `q₀B` (a demand); online also what the batch needs (`tie'`, `cA'` with the proof
    `same'`, `QV'`, fixed values).
  `P.HypR L`, `P.Hyp L` (with `P.HypR L` as its field `r`): `P.D.HypRest L` (`rest0`); `Y.Hyp`
    (`sndOK`); for each plan (offline | online): `Plain` (`plain` | `plainB`), `Kept` (`kept` |
    `keptB`) (online also `Shared`: `shared`), "restG is rest" (`rest` | `restB`), `SaysA` (`saysA`
    | `saysAB`), Q''s own conditions (`left`, `leftQ` | `leftB`, `leftQB`), κ is the free entry n₀
    of a member of Ω's family (`kIs` | `kIsB`), the front reads no pad entry of Ω's family (`noPad`
    | `noPadB`), four families of inequalities (`needA` .. `needO` | `needNA` .. `needNO`); online
    also `tieC`, `qaOK`, 1 ≤ N (`oneN`), `leftKB`, `leftV`; the link's test (`close`) and the six
    tests on groups (`test₁` .. `test₃` | `test₁B` .. `test₃B`): OK.
  `Spec.ldObjPp_parts`: `P.Hyp L` ⇒ all nine clauses of `LdObjT.Hyp` on the two closings, at the
    fields of `P.toT`, the offline closing's `plan` in the form "in order behind the core"
    (`OkBehind`, Cb/Ld/LdLinCloseAlt.lean).
  `Spec.ldObjPp_hyp`: `P.Hyp L` ⇒ `P.toT.Hyp L`. So the chain above `LdObjT` applies to the object
    at the report's plan: `Cb.ldObjT_ok` at `P.toT` (⇒ `P.toT.obj.OK L`) and `Cb.ldObj_hyp` at
    `P.toT.obj`.



No hypothesis that κ is fresh: under the hypotheses of its statement (`Spec.ldObjPp_parts`), that κ
is fresh follows from the sender's law, offline and online (for one instance and for sets of slots).

Why "behind the core": this closing holds a masked link (the splitting), so it is in order only
behind the core that sent the mask, not by itself; the clause `plan` of `LdObjT.Hyp` has that form
(the head of Cb/Obj/LdObjectTerms.lean, on `plan`).

Limits: Q' (what closes the rest) is a parameter with its own conditions, offline and online.
That `P.Hyp L` can be met is not shown in this file. No theorem of this library states that the
hypotheses of `ldObjPp_parts` or `ldObjPp_hyp` can be met together. `ldObjPp_parts` is used in the
proof of `ldObjPp_hyp`.

What the head of Cb/Obj/LdObjectTerms.lean says on the request holds here.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectPlan
import Cb.Obj.LdObjectSendersLin
import Cb.Obj.LdObjectPaperBatch
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The object, both closings at the report's plan (one splitting, the shared one): the
data. -/
structure LdObjPp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    extends LdObjD F E where
  /-- the seven standard senders: the data's own senders are not read -/
  Y   : toLdObjD.StdS
  /-- offline -/
  p   : LdLinPp W.O.toC
  TP  : LdLinPpT p
  b'  : p.S₃.O → ℕ
  n₀  : Σ a, Y.TS.YO.Fr a
  /-- online -/
  pB  : LdLinPp on.ol.toC
  TB  : LdLinPpT pB
  q₀B : Finset on.ol.toC.E₀.Pos → Prop
  bB' : pB.S₃.O → ℕ
  baB : on.ol.toC.Sa.O → ℕ
  tie' : on.ol.toC.P.Sh6 → TB.Q'.St × pB.S₃.Smp → (on.ol.toC.E₀.prod pB.S₃.ext).Str →
    pB.S₃.Wit × on.ol.toC.Wpa → Prop
  x₀  : on.ol.toC.S.Smp
  y₀  : on.ol.toC.S.ext.Str
  cA' : ChainA Unit (pB.S₃.jointCf TB.Q'.base) ldTrivJ
  same' : cA'.forget = TB.Q'.c
  xB  : TB.StB
  xC  : TB.StC
  QV' : LdTcV N (⟨TB.Q', cA', same'⟩ : LdTcA pB.S₃ on.ol.toC.E₀ on.ol.toC.Wpa)
    ⟨on.ol.toC.P.Sh6, tie', TB.qB₃ N q₀B bB'⟩
  n₀B : Σ a, Y.TB.YO.Fr a
  /-- fixed values -/
  yE  : on.ol.toC.E₀.Str
  sh₀ : on.ol.toC.Sh6
  x₄  : on.ol.toC.P.X4
  y₄  : on.ol.toC.P.E4.Str

namespace LdObjPp
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (P : LdObjPp F E)

/-- the data with the standard senders put in -/
@[reducible] def D : LdObjD F E := P.toLdObjD.std P.Y

/-- the closing of the test at N instances -/
def cZ : ChainV Unit P.N (P.on.ol.toC.P.V6 P.D.SnB P.qaB P.N) P.QV'.VT :=
  P.TB.cZV P.N P.q₀B P.bB' P.tie' P.x₀ P.y₀ P.cA' P.same' P.xB P.xC P.D.SnB P.qaB P.QV'

/-- The object with the terms that the library builds for its sub-protocols. -/
def toT : LdObjT F E :=
  { P.D with Qt := P.TP.QF, fq := P.W.O.toC.fqP P.TP.fa, VT := P.QV'.VT, cZ := P.cZ, kT := ldKeyT }

structure HypR (L : ℕ) : Prop where
  rest0  : P.D.HypRest L
  sndOK  : P.Y.Hyp
  /-- the offline plan -/
  plain  : P.p.Plain
  kept   : P.p.Kept
  rest   : ∀ sa m, P.p.restG.val sa (P.p.Gc.msg (P.p.left₂ m)) = P.W.O.toC.rest sa (P.W.O.toC.aM m)
  saysA  : P.p.SaysA P.TP.Q'.base P.TP.fa
  left   : P.TP.Q'.OK
  leftQ  : ∀ V, P.TP.Q'.q V → P.p.S₃.qFam P.q₀ P.b' V
  kIs    : (⟨P.p.k₀.o, P.p.k₀.j⟩ : P.W.O.toC.S.Ent) = P.W.O.toC.eO (P.Y.TS.YO.entF P.n₀)
  noPad  : ∀ n, P.p.Rs₀ (P.W.O.toC.eO n) → P.Y.TS.YO.NoPad n
  needA  : ∀ a, P.TP.D₁.need (P.TP.D₂.need (P.TP.D₃.need P.b')) (.inl (.inl (.inl a))) ≤ P.Bw.t a
  needW  : ∀ a, P.TP.D₁.need (P.TP.D₂.need (P.TP.D₃.need P.b')) (.inl (.inl (.inr a))) ≤ P.Y.tW a
  needU  : ∀ a, P.TP.D₁.need (P.TP.D₂.need (P.TP.D₃.need P.b')) (.inl (.inr a)) ≤ P.Y.tU a
  needO  : ∀ a, P.TP.D₁.need (P.TP.D₂.need (P.TP.D₃.need P.b')) (.inr a) ≤ P.Y.tO a
  /-- the online plan -/
  shared : P.pB.Shared
  plainB : P.pB.Plain
  keptB  : P.pB.Kept
  restB  : ∀ sa m,
    P.pB.restG.val sa (P.pB.Gc.msg (P.pB.left₂ m)) = P.on.ol.toC.rest sa (P.on.ol.toC.aM m)
  saysAB : P.pB.SaysA P.TB.Q'.base P.TB.fa
  leftB  : P.TB.Q'.OK
  leftQB : ∀ V, P.TB.Q'.q V → P.pB.S₃.qFam P.q₀B P.bB' V
  leftKB : P.cA'.KB P.N (ldKeyU _) ldKeyT
  leftV  : P.QV'.OK
  tieC   : ∀ x y w, (P.on.ol.toC.P.V6 P.D.SnB P.qaB P.N).rel x y w →
    P.tie' w.1
      (P.TB.fa (P.on.ol.toC.toSt x).1.1.1.1,
        P.pB.S₂.res (T := OMsg.Smp) P.pB.kp₃
          (P.pB.S₁.res (T := OMsg.Smp) P.pB.kp₂
            (P.on.ol.toC.S.res (T := OMsg.Smp) P.pB.kp₁ (P.on.ol.toC.toSmp x))))
      (P.TB.D₃.outY (P.TB.D₂.outY (P.TB.D₁.outY (P.on.ol.toC.toE.map y))))
      (P.TB.D₃.outW (P.TB.D₂.outW (P.TB.D₁.outW (P.on.ol.toC.toW w.2))))
  qaOK   : ∀ W, P.on.ol.toC.Sa.qFam P.q₀B P.baB W → P.qaB W
  oneN   : 1 ≤ P.N
  kIsB   : (⟨P.pB.k₀.o, P.pB.k₀.j⟩ : P.on.ol.toC.S.Ent) = P.on.ol.toC.eO (P.Y.TB.YO.entF P.n₀B)
  noPadB : ∀ n, P.pB.Rs₀ (P.on.ol.toC.eO n) → P.Y.TB.YO.NoPad n
  needNA : ∀ a,
    P.TB.D₁.need (P.TB.D₂.need (P.TB.D₃.needV P.N (fun a => P.on.ol.toC.isSh a.1.1) P.bB'))
        (.inl (.inl (.inl a))) ≤ P.baB a
  needNW : ∀ a,
    P.TB.D₁.need (P.TB.D₂.need (P.TB.D₃.needV P.N (fun a => P.on.ol.toC.isSh a.1.1) P.bB'))
        (.inl (.inl (.inr a))) ≤ P.Y.tWB a
  needNU : ∀ a,
    P.TB.D₁.need (P.TB.D₂.need (P.TB.D₃.needV P.N (fun a => P.on.ol.toC.isSh a.1.1) P.bB'))
        (.inl (.inr a)) ≤ P.Y.tUB a
  needNO : ∀ a,
    P.TB.D₁.need (P.TB.D₂.need (P.TB.D₃.needV P.N (fun a => P.on.ol.toC.isSh a.1.1) P.bB'))
        (.inr a) ≤ P.Y.tOB a

structure Hyp (L : ℕ) : Prop where
  r      : P.HypR L
  close  : P.Kc.OK
  test₁  : P.TP.D₁.OK
  test₂  : P.TP.D₂.OK
  test₃  : P.TP.D₃.OK
  test₁B : P.TB.D₁.OK
  test₂B : P.TB.D₂.OK
  test₃B : P.TB.D₃.OK

end LdObjPp

open Classical in
/-- States: `P.Hyp L` gives all clauses on the two closings, the offline one in the form "in order
behind the core". -/
def Spec.ldObjPp_parts (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Prop :=
  ∀ (P : LdObjPp F E) (L : ℕ), P.Hyp L →
    P.W.O.toC.Says P.TP.QF.base (P.W.O.toC.fqP P.TP.fa) ∧
    P.TP.QF.OkBehind
      ((P.W.O.toC.P.chain P.W.O.on0 P.D.Sn P.εf).append
        (P.W.O.toC.chain (P.W.O.toC.fqP P.TP.fa) P.TP.QF.base)) ∧
    (∀ V, P.TP.QF.q V →
      P.W.O.toC.P.q5 P.D.Sn (P.W.O.S.qFam (E₀ := extNone) P.q₀ P.Bw.t)
        (V.biUnion P.W.O.toC.toE.src)) ∧
    P.cZ.forget.forget.OkFrom (P.on.ol.toC.P.chain P.onB P.D.SnB P.εfB) ∧
    P.cZ.forget.forget.SidesCT (P.on.ol.toC.P.q5 P.D.SnB P.qaB) ∧
    P.cZ.forget.KB P.N P.on.ol.toC.P.key6 ldKeyT ∧
    P.cZ.OkFromV (P.on.ol.toC.P.chainV P.D.SnB P.qaB P.N P.onB P.εfB) ∧
    P.cZ.forget.Coh ∧
    ∀ Jn, P.QV'.VT.q Jn fun _ => ∅

open Classical in
theorem ldObjPp_parts (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldObjPp_parts F E := by
  intro P L h
  classical
  have hS := ldObjS_snd P.toLdObjD P.Y h.r.sndOK
  have hr := h.r.rest0
  -- offline: the mask is fresh by the sender's law
  have hSaysO : P.W.O.toC.Says (P.p.x₁ P.TP.Q'.base).A (P.W.O.toC.fqP P.TP.fa) :=
    ldLinPp_says E _ _ _ _ P.W.O.toC P.p _ P.TP.Q'.base P.TP.fa h.r.rest h.r.saysA
  have o0 : P.p.Rs₀ (P.W.O.toC.eO (P.Y.TS.YO.entF P.n₀)) := h.r.kIs ▸ h.r.plain.rs₀K
  have ol := stdL_ownOne P.Y.Fp E P.W.O.toC.P.NO P.Y.TS.YO P.Y.tO P.W.O.toC.P.W4 P.W.O.toC.P.W3
    P.Y.TS.datO (fun w => w.2) (fun _ => 0, P.Y.TS.w3) P.n₀ P.W.O.toC.P.SdO
    (fun n => P.p.Rs₀ (P.W.O.toC.eO n)) h.r.sndOK.off.okO h.r.noPad o0
  have of0 := ldLinSp_entO E _ _ _ _ P.W.O.toC P.W.O.on0 P.εf P.D.Sn (P.p.x₁ P.TP.Q'.base)
    (P.W.O.toC.fqP P.TP.fa)
    (P.Y.TS.YO.ownOne P.Y.TS.datO (fun w => w.2) (fun _ => 0, P.Y.TS.w3) P.n₀) P.p.Rs₀
    (fun _ => False) (P.Y.TS.YO.entF P.n₀) ol hS.snd.hidO (fun _ h => h) o0
  rw [← h.r.kIs] at of0
  have hbehO := ldLinPpT_behindA E _ _ _ _ P.W.O.toC P.p P.TP P.W.O.on0 P.εf P.D.Sn P.p.Rs₀
    (fun _ => False) hr.fold hr.pyInj hS.snd h.r.rest h.r.saysA h.r.plain h.r.kept h.test₁ h.test₂
    h.test₃ h.r.left (fun _ h => h) of0
  have hdemO := ldLinPpT_demand E _ _ _ _ P.W.O.toC P.p P.TP P.D.Sn
    (P.W.O.S.qFam (E₀ := extNone) P.q₀ P.Bw.t) P.q₀ P.Bw.t P.b' h.r.leftQ (fun _ hW => hW)
    h.r.needA h.r.needW h.r.needU h.r.needO
  -- online
  have hSays : P.on.ol.toC.Says (P.pB.x₁ P.TB.Q'.base).A (P.on.ol.toC.fqP P.TB.fa) :=
    ldLinPp_says E _ _ _ _ P.on.ol.toC P.pB _ P.TB.Q'.base P.TB.fa h.r.restB h.r.saysAB
  have h0 : P.pB.Rs₀ (P.on.ol.toC.eO (P.Y.TB.YO.entF P.n₀B)) := h.r.kIsB ▸ h.r.plainB.rs₀K
  have l0 := stdL_ownOne P.Y.Fp E P.on.ol.toC.P.NO P.Y.TB.YO P.Y.tOB P.on.ol.toC.P.W4
    P.on.ol.toC.P.W3 P.Y.TB.datO (fun w => w.2) (fun _ => 0, P.Y.TB.w3) P.n₀B P.on.ol.toC.P.SdO
    (fun n => P.pB.Rs₀ (P.on.ol.toC.eO n)) h.r.sndOK.on.okO h.r.noPadB h0
  have f0 := ldLinSp_entO E _ _ _ _ P.on.ol.toC P.onB P.εfB P.D.SnB (P.pB.x₁ P.TB.Q'.base)
    (P.on.ol.toC.fqP P.TB.fa)
    (P.Y.TB.YO.ownOne P.Y.TB.datO (fun w => w.2) (fun _ => 0, P.Y.TB.w3) P.n₀B) P.pB.Rs₀
    (fun _ => False) (P.Y.TB.YO.entF P.n₀B) l0 hS.sndB.hidO (fun _ h => h) h0
  rw [← h.r.kIsB] at f0
  have hbeh := ldLinPpT_behindA E _ _ _ _ P.on.ol.toC P.pB P.TB P.onB P.εfB P.D.SnB P.pB.Rs₀
    (fun _ => False) hr.foldB hr.pyInjB hS.sndB h.r.restB h.r.saysAB h.r.plainB h.r.keptB h.test₁B
    h.test₂B h.test₃B h.r.leftB (fun _ h => h) f0
  have hdem := ldLinPpT_demand E _ _ _ _ P.on.ol.toC P.pB P.TB P.D.SnB P.qaB P.q₀B P.baB P.bB'
    h.r.leftQB h.r.qaOK
    (fun a => (ldOnP_le E _ _ _ _ P.on.ol.toC P.pB P.TB P.N P.bB' _ h.r.oneN).trans (h.r.needNA a))
    (fun a => (ldOnP_le E _ _ _ _ P.on.ol.toC P.pB P.TB P.N P.bB' _ h.r.oneN).trans (h.r.needNW a))
    (fun a => (ldOnP_le E _ _ _ _ P.on.ol.toC P.pB P.TB P.N P.bB' _ h.r.oneN).trans (h.r.needNU a))
    (fun a => (ldOnP_le E _ _ _ _ P.on.ol.toC P.pB P.TB P.N P.bB' _ h.r.oneN).trans (h.r.needNO a))
  obtain ⟨hC1, hC2⟩ := ldLinAlt_chain E _ _ _ _ P.on.ol.toC P.onB P.εfB P.D.SnB P.qaB P.TB.QF
    (P.on.ol.toC.fqP P.TB.fa) hr.foldB hr.pyInjB hS.sndB hSays hbeh hdem
  have hKB := ldLinPpB_kb E _ _ _ _ P.on.ol.toC P.pB P.TB P.cA' P.same' P.N h.r.shared h.r.restB
    h.r.saysAB h.r.plainB h.r.keptB h.test₁B h.test₂B h.test₃B h.r.leftKB
  obtain ⟨v1, v2, v3, v4, v5⟩ :=
    ldLinPV_std P.Y.Fp E _ _ _ _ P.on.ol.toC P.pB P.TB P.N P.q₀B P.bB' P.tie' P.x₀ P.y₀ P.cA'
      P.same' P.xB P.xC P.yE P.QV' P.Y.TB P.Y.LWB P.Y.LUB P.Y.LOB P.Y.tWB P.Y.tUB P.Y.tOB P.n₀B
      P.qaB P.baB P.onB P.εfB P.sh₀ P.x₄ P.y₄ h.r.shared h.r.plainB h.r.keptB h.r.restB
      h.r.saysAB h.test₁B h.test₂B h.test₃B h.r.leftV h.r.tieC h.r.qaOK h.r.needNA h.r.needNW
      h.r.needNU h.r.needNO h.r.sndOK.on.places h.r.sndOK.on.okW h.r.sndOK.on.okU
      h.r.sndOK.on.okO h.r.kIsB h.r.noPadB
  have v5' : P.cZ.forget.forget = P.on.ol.toC.cZ P.TB.QF (P.on.ol.toC.fqP P.TB.fa) := v5
  have v4' : P.cZ.forget = _ := v4
  refine ⟨hSaysO, hbehO, hdemO, ?_, ?_, ?_, v1, v2, v3⟩
  · rw [v5']; exact hC1
  · rw [v5']; exact hC2
  · rw [v4']; exact hKB

/-- The hypotheses of the object with the lots' terms, at the report's plan. -/
def Spec.ldObjPp_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Prop :=
  ∀ (P : LdObjPp F E) (L : ℕ), P.Hyp L → P.toT.Hyp L

theorem ldObjPp_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldObjPp_hyp F E := by
  intro P L h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ldObjPp_parts F E P L h
  exact
    { base := ⟨h.r.rest0, ldObjS_snd P.toLdObjD P.Y h.r.sndOK⟩
      close := h.close
      rows := a1
      plan := a2
      demand := a3
      cOk := a4
      cSides := a5
      cKB := a6
      cOkV := a7
      cCoh := a8
      cEnd := a9 }

end Cb
