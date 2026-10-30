-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdHonPlanOn.lean: this file proves the six conditions on the closing of the test at N
instances (`Cb.Spec.ldOnT_ok`), at the technical report's plan, from the part of the object's
hypotheses that names neither the request nor the offline phase, except in its fields `rest0`,
`sndOK` and
`pl`.

Two records, statements (in `Cb.Spec`) and proofs. Generic: any finite field F and any finite field
E that is an algebra over F. Nothing assumed beyond the hypotheses of the statements and whatever
the arguments hold as proofs. The analogue of Cb/Ld/LdHonOff.lean for the online phase.
The test at N instances is the sub-protocol `linOn` of `SubsR` (Hiop/RecSubs.lean).

Why: the proof by way of `ldObjRp_hyp` (Cb/Obj/LdObjectPpRows.lean) and `ldObjPp_parts`
(Cb/Obj/LdObjectPlanPaper.lean) takes one record at each level, whose clause rest0
(`LdObjD.HypRest L`) holds "the request's moves are in order" (`r.Hyp`, with rZk, rFmt, rEnd) beside
its other clauses. Of rest0 the online half of `ldObjPp_parts` reads foldB and pyInjB alone. Whoever
wants to use that half at another object (say: the same object with the errors of the session's four
whole tests overwritten by the full list) without the request's `r.Hyp` needs it from a smaller
record.
Each record's clauses are clauses of the record that it is cut from (but rest0, typed at
`LdObjD.HypRestH`: Cb/Ld/LdHonOff.lean).

Main names:
  `P.HypOnP L`: of `LdObjPp.Hyp L`: rest0 (at `HypRestH`), sndOK; shared .. needNO (the online
    plan's clauses of `HypR`); test₁B, test₂B, test₃B.
  `R.HypOnR L`: of `LdObjRp.Hyp L`: rest0 (at `HypRestH`), sndOK, pl (`R.HypPl` whole: places,
    numbers, forms); test₁B .. test₄B.
  `Spec.ldHonP_on`: `P.HypOnP L` ⇒ the six conditions on `P.cZ`: `OkFrom`, `SidesCT`, `KB`,
    `OkFromV`, `Coh`, the end's demand.
  `Spec.ldHonP_term`: `P.HypOnP L` ⇒ `P.toT.linB.OK` (by `Cb.ldOnT_ok`: the term of the test at N
    instances, whole: both sides).
  `Spec.ldHonP_termD`: the same with the term written at P's own parameters (`P.D.on.ol.termT` at
    `P.cZ`): for whoever reads it at two objects side by side.
  `Spec.ldHonRp_on`: `R.HypOnR L` ⇒ `R.toPp.HypOnP L`.
  `Spec.ldHonP_onOf`, `Spec.ldHonRp_onOf`: `LdObjPp.Hyp`, `LdObjRp.Hyp` give these records: nothing
    new is asked.

Limits: a door. `P.HypOnP L` still holds both sides of the session's tests (test₁B .. are `D.OK`:
bundles with knowledge soundness at D's own errors): it is an honest half only where it is used at
tests whose errors are the full list. This file does not say that the records hold of any object.
It says nothing on the request, the offline phase, the link, but for the clauses on these that
rest0, sndOK and pl hold.

Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import Cb.Ld.LdHonOff

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The online half of `LdObjPp.Hyp L`. -/
structure LdObjPp.HypOnP (P : LdObjPp F E) (L : ℕ) : Prop where
  rest0  : P.D.HypRestH L
  sndOK  : P.Y.Hyp
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
  test₁B : P.TB.D₁.OK
  test₂B : P.TB.D₂.OK
  test₃B : P.TB.D₃.OK

/-- The online half of `LdObjRp.Hyp L`. -/
structure LdObjRp.HypOnR (R : LdObjRp F E) (L : ℕ) : Prop where
  rest0  : (R.toLdObjD.std R.Y).HypRestH L
  sndOK  : R.Y.Hyp
  pl     : R.HypPl
  test₁B : R.TB₀.D₁.OK
  test₂B : R.TB₀.D₂.OK
  test₃B : R.TB₀.D₃.OK
  test₄B : R.XB.run.OK

end

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

open Classical in
/-- States: `P.HypOnP L` gives the six conditions on the closing `P.cZ`. -/
def ldHonP_on : Prop :=
  ∀ (P : LdObjPp F E) (L : ℕ), P.HypOnP L →
    P.cZ.forget.forget.OkFrom (P.on.ol.toC.P.chain P.onB P.D.SnB P.εfB) ∧
    P.cZ.forget.forget.SidesCT (P.on.ol.toC.P.q5 P.D.SnB P.qaB) ∧
    P.cZ.forget.KB P.N P.on.ol.toC.P.key6 ldKeyT ∧
    P.cZ.OkFromV (P.on.ol.toC.P.chainV P.D.SnB P.qaB P.N P.onB P.εfB) ∧
    P.cZ.forget.Coh ∧
    ∀ Jn, P.QV'.VT.q Jn fun _ => ∅

def ldHonP_term : Prop := ∀ (P : LdObjPp F E) (L : ℕ), P.HypOnP L → P.toT.linB.OK

/-- The same as `ldHonP_term` at P's own parameters: what `P.toT.linB` unfolds to. -/
def ldHonP_termD : Prop :=
  ∀ (P : LdObjPp F E) (L : ℕ),
    P.HypOnP L → (P.D.on.ol.termT P.D.onB P.D.SnB P.D.qaB P.D.εfB P.D.N P.cZ P.D.dB P.D.dB₀).OK

def ldHonRp_on : Prop := ∀ (R : LdObjRp F E) (L : ℕ), R.HypOnR L → R.toPp.HypOnP L

def ldHonP_onOf : Prop := ∀ (P : LdObjPp F E) (L : ℕ), P.Hyp L → P.HypOnP L

def ldHonRp_onOf : Prop := ∀ (R : LdObjRp F E) (L : ℕ), R.Hyp L → R.HypOnR L

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

open Classical in
theorem ldHonP_on : Spec.ldHonP_on F E := by
  intro P L h
  classical
  have hS := ldObjS_snd P.toLdObjD P.Y h.sndOK
  have hr := h.rest0
  have hSays : P.on.ol.toC.Says (P.pB.x₁ P.TB.Q'.base).A (P.on.ol.toC.fqP P.TB.fa) :=
    ldLinPp_says E _ _ _ _ P.on.ol.toC P.pB _ P.TB.Q'.base P.TB.fa h.restB h.saysAB
  have h0 : P.pB.Rs₀ (P.on.ol.toC.eO (P.Y.TB.YO.entF P.n₀B)) := h.kIsB ▸ h.plainB.rs₀K
  have l0 := stdL_ownOne P.Y.Fp E P.on.ol.toC.P.NO P.Y.TB.YO P.Y.tOB P.on.ol.toC.P.W4
    P.on.ol.toC.P.W3 P.Y.TB.datO (fun w => w.2) (fun _ => 0, P.Y.TB.w3) P.n₀B P.on.ol.toC.P.SdO
    (fun n => P.pB.Rs₀ (P.on.ol.toC.eO n)) h.sndOK.on.okO h.noPadB h0
  have f0 := ldLinSp_entO E _ _ _ _ P.on.ol.toC P.onB P.εfB P.D.SnB (P.pB.x₁ P.TB.Q'.base)
    (P.on.ol.toC.fqP P.TB.fa)
    (P.Y.TB.YO.ownOne P.Y.TB.datO (fun w => w.2) (fun _ => 0, P.Y.TB.w3) P.n₀B) P.pB.Rs₀
    (fun _ => False) (P.Y.TB.YO.entF P.n₀B) l0 hS.sndB.hidO (fun _ h => h) h0
  rw [← h.kIsB] at f0
  have hbeh := ldLinPpT_behindA E _ _ _ _ P.on.ol.toC P.pB P.TB P.onB P.εfB P.D.SnB P.pB.Rs₀
    (fun _ => False) hr.foldB hr.pyInjB hS.sndB h.restB h.saysAB h.plainB h.keptB h.test₁B h.test₂B
    h.test₃B h.leftB (fun _ h => h) f0
  have hdem := ldLinPpT_demand E _ _ _ _ P.on.ol.toC P.pB P.TB P.D.SnB P.qaB P.q₀B P.baB P.bB'
    h.leftQB h.qaOK
    (fun a => (ldOnP_le E _ _ _ _ P.on.ol.toC P.pB P.TB P.N P.bB' _ h.oneN).trans (h.needNA a))
    (fun a => (ldOnP_le E _ _ _ _ P.on.ol.toC P.pB P.TB P.N P.bB' _ h.oneN).trans (h.needNW a))
    (fun a => (ldOnP_le E _ _ _ _ P.on.ol.toC P.pB P.TB P.N P.bB' _ h.oneN).trans (h.needNU a))
    (fun a => (ldOnP_le E _ _ _ _ P.on.ol.toC P.pB P.TB P.N P.bB' _ h.oneN).trans (h.needNO a))
  obtain ⟨hC1, hC2⟩ := ldLinAlt_chain E _ _ _ _ P.on.ol.toC P.onB P.εfB P.D.SnB P.qaB P.TB.QF
    (P.on.ol.toC.fqP P.TB.fa) hr.foldB hr.pyInjB hS.sndB hSays hbeh hdem
  have hKB := ldLinPpB_kb E _ _ _ _ P.on.ol.toC P.pB P.TB P.cA' P.same' P.N h.shared h.restB
    h.saysAB h.plainB h.keptB h.test₁B h.test₂B h.test₃B h.leftKB
  obtain ⟨v1, v2, v3, v4, v5⟩ :=
    ldLinPV_std P.Y.Fp E _ _ _ _ P.on.ol.toC P.pB P.TB P.N P.q₀B P.bB' P.tie' P.x₀ P.y₀ P.cA'
      P.same' P.xB P.xC P.yE P.QV' P.Y.TB P.Y.LWB P.Y.LUB P.Y.LOB P.Y.tWB P.Y.tUB P.Y.tOB P.n₀B
      P.qaB P.baB P.onB P.εfB P.sh₀ P.x₄ P.y₄ h.shared h.plainB h.keptB h.restB h.saysAB h.test₁B
      h.test₂B h.test₃B h.leftV h.tieC h.qaOK h.needNA h.needNW h.needNU h.needNO h.sndOK.on.places
      h.sndOK.on.okW h.sndOK.on.okU h.sndOK.on.okO h.kIsB h.noPadB
  have v5' : P.cZ.forget.forget = P.on.ol.toC.cZ P.TB.QF (P.on.ol.toC.fqP P.TB.fa) := v5
  have v4' : P.cZ.forget = _ := v4
  refine ⟨?_, ?_, ?_, v1, v2, v3⟩
  · rw [v5']; exact hC1
  · rw [v5']; exact hC2
  · rw [v4']; exact hKB

theorem ldHonP_term : Spec.ldHonP_term F E := by
  intro P L h
  obtain ⟨a4, a5, a6, a7, a8, a9⟩ := ldHonP_on F E P L h
  have hS := ldObjS_snd P.toLdObjD P.Y h.sndOK
  exact ldOnT_ok F E P.toT.on.ol P.toT.onB P.toT.SnB P.toT.qaB P.toT.εfB P.toT.N P.toT.VT P.toT.cZ
    P.toT.kT P.toT.dB P.toT.dB₀ P.toT.yB h.rest0.fitsB h.rest0.foldB h.rest0.pyInjB hS.sndB
    hS.apartB h.rest0.monoB a4 a5 a6 a7 a8 a9

theorem ldHonP_termD : Spec.ldHonP_termD F E := by
  intro P L h
  obtain ⟨a4, a5, a6, a7, a8, a9⟩ := ldHonP_on F E P L h
  have hS := ldObjS_snd P.toLdObjD P.Y h.sndOK
  exact ldOnT_ok F E P.D.on.ol P.D.onB P.D.SnB P.D.qaB P.D.εfB P.D.N P.QV'.VT P.cZ ldKeyT
    P.D.dB P.D.dB₀ P.D.yB h.rest0.fitsB h.rest0.foldB h.rest0.pyInjB hS.sndB hS.apartB
    h.rest0.monoB a4 a5 a6 a7 a8 a9

theorem ldHonRp_on : Spec.ldHonRp_on F E := by
  intro R L h
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
    { rest0 := h.rest0
      sndOK := h.sndOK
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
      needNO := h.pl.needNO
      test₁B := h.test₁B
      test₂B := h.test₂B
      test₃B := h.test₃B }

theorem ldHonP_onOf : Spec.ldHonP_onOf F E := fun P L h =>
  { rest0 := ldHonD_ofRest F E P.D L h.r.rest0, sndOK := h.r.sndOK, shared := h.r.shared,
    plainB := h.r.plainB, keptB := h.r.keptB, restB := h.r.restB, saysAB := h.r.saysAB,
    leftB := h.r.leftB, leftQB := h.r.leftQB
    leftKB := h.r.leftKB, leftV := h.r.leftV, tieC := h.r.tieC, qaOK := h.r.qaOK, oneN := h.r.oneN,
      kIsB := h.r.kIsB, noPadB := h.r.noPadB, needNA := h.r.needNA, needNW := h.r.needNW,
      needNU := h.r.needNU, needNO := h.r.needNO
    test₁B := h.test₁B, test₂B := h.test₂B, test₃B := h.test₃B }

theorem ldHonRp_onOf : Spec.ldHonRp_onOf F E := fun R L h =>
  { rest0 := ldHonD_ofRest F E (R.toLdObjD.std R.Y) L h.rest0, sndOK := h.sndOK, pl := h.pl,
    test₁B := h.test₁B, test₂B := h.test₂B, test₃B := h.test₃B, test₄B := h.test₄B }

end
end Cb
