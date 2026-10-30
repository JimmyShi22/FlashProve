-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPlan.lean: assembly of the holographic IOP from its sub-protocols: the object with
the terms that the library builds for its sub-protocols (`LdObjT`), the last part of both tests for
linear constraints (their closings) at the plan without a splitting.

Definitions, one statement and its proof.
The object (`LdObj`, Cb/Obj/LdObject.lean) has, over one configuration, the sub-protocols from
which Hiop/RecBuild.lean builds the holographic IOP. The closing of a test for linear constraints is
the chain of steps after its core, down to the trivial statement. A plan (`LdLinPl`,
Cb/Ld/LdLinClosePlan.lean) fixes how the rows that the test leaves are closed: the groups of oracle
messages, the rows that go to the test on each group, and the messages kept for later tests.
Cb/Obj/LdObjectTerms.lean takes the closings of the two tests for linear constraints as data with
conditions. Here both are the plan's terms (Cb/Ld/LdLinClosePlan.lean, Cb/Ld/LdLinCloseDemand.lean):
the rows that are left as rows on two groups; a whole test on the first, then on the second, then a
closing Q' of what is left.
  Offline (one instance): Qt := TP.Q. From `P.Hyp L` its three conditions (it says the rows and
    `Ab`: `LdLinC.Says`, Cb/Ld/LdLinClosePre.lean; it is in order behind the test's core and the
    step without rounds: `Qt.OkBehind`; it needs no more positions than the sent words bear) become
    theorems. `Q.OK` (every link has the whole bundle and the budgets fit) gives `Q.OkBehind`:
    `ldAlt_of_ok`, Cb/Ld/LdLinCloseAlt.lean.
  Online (N instances): cZ := TB.cZV .. (Cb/Ld/LdLinCloseVLin.lean): the first test is run once by
    the shared part, the second in every slot. From `P.Hyp L` its six conditions become theorems:
    behind the core and the budgets' half at one instance (`Cb.ldLinCl_chain`), knowledge sound from
    the key after ζ (`Cb.ldPlanLin_kb`), behind the core for sets of slots, coherent annotations,
    nothing follows (`Cb.ldLinVL_all`).

Main names:
  `LdObjP F E`: `LdObjD` (all data but the closings); offline, online (its fields: see the record).
  `P.Hyp L` (with `P.HypR L`, its field `r`): it asks `LdObjD.HypD L` (`base`) and the link's test
    (`close`: `Kc.OK`). For each of the two plans (offline | online) it asks: "restG is rest"
    (`rest` | `restB`: the plan's `restG`, the form on the second group's message, is the test's
    "rest"); that Q' says what the preamble left (`saysA` | `saysAB`: `SaysA`); the two tests' own
    OK (`test₁`, `test₂` | `test₁B`, `test₂B`; of each: its evader, the list of the group's complex,
    the radii, and that the whole test is a tail of a chain); `Q'.OK` (`left` | `leftB`) and its
    demand (`leftQ` | `leftQB`); and families of inequalities between numbers of positions, `needA`
    .. `needO` | `needNA` .. `needNO` (online for N ≥ 1 instances, the shared oracle messages
    counted once for the first test and N times for the second; those for one instance follow).
    Online it also asks that all members of the first group are shared oracle messages (`shared`);
    that the rest is knowledge sound for every vector of statements (`leftKB`), and has an honest
    side for a batch (`leftV`: `QV'.OK`); that the tie at the joint of what is left (`tie'`) is
    carried (`tieC`); and `qaOK`.
  `Spec.ldObjP_hyp`: `P.Hyp L` ⇒ `P.toT.Hyp L`.

Notation: `L`: a natural number (`LdCf.OK L`, Cb/Obj/LdObjectConf.lean, says that it bounds the
lists at the radius of decoding); `N`: a natural number, the number of instances online; `x₀`: fixed
values for what a slot owns (`LdLinPlT.repX`, Cb/Ld/LdLinCloseVLin.lean).

Limits: proofs among the data, among them these, which are needed to write the terms down and of
which none is a property of a protocol: same' (the annotated links of the rest are the rest's
links); in the plans' and tests' own records: every oracle message is a member of the test's group
or kept (hc₁, hc₂); in the link's closing: every member of the family lies in its one group (all).
What is still a parameter with a property: the whole tests T₁, T₂ on the two groups of each plan;
"the rest" of each plan (Q'; online with cA', QV'); and all that the head of
Cb/Obj/LdObjectTerms.lean names.
Declared: a write-up of ours (lean/CREDITS.md) has another plan for the closing of the test
for linear constraints: one splitting, in the shared part. That plan is not the one under this file
(here: the plan without a splitting). The object at that plan stands beside:
Cb/Obj/LdObjectPlanPaper.lean (`LdObjPp`; `ldObjPp_hyp`); the records on data (`LdObjR`, `LdObjZ`
and what stands on them, the one theorem for quoting among it) are at the plan without a splitting;
among those at the plan with a splitting: `LdObjRp`, `LdObjZp` and what stands on them
(Cb/Obj/LdObjectPpRows.lean, Cb/Obj/LdObjectPpData.lean).
No theorem of this library states that the hypotheses of `ldObjP_hyp` can be met together.
A find of the kind told in the head of Cb/Obj/LdObjectTerms.lean bears on this file
(Cb/Ld/LdLinClosePlanRows.lean tells it): "Q' says what the preamble left" (saysA) is asked at all
states. While the coefficients of a filed row were free data of the state, no closing Q' that sorts
the filed rows into more than one group could meet it. Filed rows are now read cut to public places;
whether saysA can now be met with several groups has not been checked (with one group for all that
is left it follows from conditions on `Ab`, on places, on the one test and on the demand:
`ldRowsOne_three`, Cb/Ld/LdLinClosePlanOne.lean).

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Obj.LdObjectTermsProofs
import Cb.Ld.LdLinCloseDemandProofs
import Cb.Ld.LdLinCloseVLinProofs
import Cb.Ld.LdLinCloseDemandLe
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The object, both closings at the plan: the data. -/
structure LdObjP (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    extends LdObjD F E where
  /-- offline -/
  p   : LdLinPl W.O.toC
  TP  : LdLinPlT p
  b'  : p.S₂.O → ℕ
  /-- online -/
  pB  : LdLinPl on.ol.toC
  TB  : LdLinPlT pB
  q₀B : Finset on.ol.toC.E₀.Pos → Prop
  bB' : pB.S₂.O → ℕ
  baB : on.ol.toC.Sa.O → ℕ
  tie' : on.ol.toC.P.Sh6 → TB.Q'.St × pB.S₂.Smp → (on.ol.toC.E₀.prod pB.S₂.ext).Str →
    pB.S₂.Wit × on.ol.toC.Wpa → Prop
  cA' : ChainA Unit (pB.S₂.jointCf TB.Q'.base) ldTrivJ
  same' : cA'.forget = TB.Q'.c
  x₀  : TB.St₁ × on.ol.toC.S.Smp
  y₀  : (on.ol.toC.E₀.prod on.ol.toC.S.ext).Str
  QV' : LdTcV N (⟨TB.Q', cA', same'⟩ : LdTcA pB.S₂ on.ol.toC.E₀ on.ol.toC.Wpa)
    ⟨on.ol.toC.P.Sh6, tie', pB.qB₂ N q₀B bB'⟩

namespace LdObjP
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (P : LdObjP F E)

/-- the closing of the test at N instances -/
def cZ : ChainV Unit P.N (P.on.ol.toC.P.V6 P.SnB P.qaB P.N) P.QV'.VT :=
  P.TB.cZV P.N P.q₀B P.bB' P.tie' P.cA' P.same' P.SnB P.qaB P.x₀ P.QV'

/-- The object with the terms that the library builds for its sub-protocols. -/
def toT : LdObjT F E :=
  { P.toLdObjD with Qt := P.TP.Q, fq := P.TP.fq, VT := P.QV'.VT, cZ := P.cZ, kT := ldKeyT }

/-- all but what is asked of the five tests on groups -/
structure HypR (L : ℕ) : Prop where
  base   : P.toLdObjD.HypD L
  /-- the offline plan -/
  rest   : ∀ sa m, P.p.restG.val sa (P.p.G₂.msg (P.W.O.toC.S.res (T := OMsg.Msg) P.p.kp₁ m)) =
    P.W.O.toC.rest sa (P.W.O.toC.aM m)
  saysA  : P.p.SaysA P.TP.Q'.base P.TP.fa
  left   : P.TP.Q'.OK
  leftQ  : ∀ V, P.TP.Q'.q V → P.p.S₂.qFam P.q₀ P.b' V
  /-- what the two tests and Q' need of each oracle message, against what its sender's encoding
  bears -/
  needA  : ∀ a, P.TP.D₁.need (P.TP.D₂.need P.b') (.inl (.inl (.inl a))) ≤ P.Bw.t a
  needW  : ∀ a, P.TP.D₁.need (P.TP.D₂.need P.b') (.inl (.inl (.inr a))) ≤ P.Sn.tW a
  needU  : ∀ a, P.TP.D₁.need (P.TP.D₂.need P.b') (.inl (.inr a)) ≤ P.Sn.tU a
  needO  : ∀ a, P.TP.D₁.need (P.TP.D₂.need P.b') (.inr a) ≤ P.Sn.tO a
  /-- the online plan -/
  shared : P.pB.Shared
  restB  : ∀ sa m, P.pB.restG.val sa (P.pB.G₂.msg (P.on.ol.toC.S.res (T := OMsg.Msg) P.pB.kp₁ m)) =
    P.on.ol.toC.rest sa (P.on.ol.toC.aM m)
  saysAB : P.pB.SaysA P.TB.Q'.base P.TB.fa
  leftB  : P.TB.Q'.OK
  leftQB : ∀ V, P.TB.Q'.q V → P.pB.S₂.qFam P.q₀B P.bB' V
  leftKB : P.cA'.KB P.N (ldKeyU _) ldKeyT
  leftV  : P.QV'.OK
  tieC   : ∀ x y w, (P.on.ol.toC.P.V6 P.SnB P.qaB P.N).rel x y w →
    P.tie' w.1 (P.TB.D₂.outX (P.TB.D₁.outX (P.TB.fq (P.on.ol.toC.toSt x), P.on.ol.toC.toSmp x)))
      (P.TB.D₂.outY (P.TB.D₁.outY (P.on.ol.toC.toE.map y)))
      (P.TB.D₂.outW (P.TB.D₁.outW (P.on.ol.toC.toW w.2)))
  qaOK   : ∀ W, P.on.ol.toC.Sa.qFam P.q₀B P.baB W → P.qaB W
  /-- at least one instance; the inequalities for N instances (those for one instance follow) -/
  oneN   : 1 ≤ P.N
  needNA : ∀ a,
    P.TB.D₁.need (P.TB.D₂.needV P.N (fun a => P.on.ol.toC.isSh a.1) P.bB') (.inl (.inl (.inl a))) ≤
      P.baB a
  needNW : ∀ a,
    P.TB.D₁.need (P.TB.D₂.needV P.N (fun a => P.on.ol.toC.isSh a.1) P.bB') (.inl (.inl (.inr a))) ≤
      P.SnB.tW a
  needNU : ∀ a,
    P.TB.D₁.need (P.TB.D₂.needV P.N (fun a => P.on.ol.toC.isSh a.1) P.bB') (.inl (.inr a)) ≤
      P.SnB.tU a
  needNO : ∀ a,
    P.TB.D₁.need (P.TB.D₂.needV P.N (fun a => P.on.ol.toC.isSh a.1) P.bB') (.inr a) ≤ P.SnB.tO a

/-- All hypotheses: `HypR`, and the five tests on groups: the link's one, the two of each plan
(each: the bridge's evader, the list of the group's complex, `Fits`, the whole test is a tail). -/
structure Hyp (L : ℕ) : Prop where
  r      : P.HypR L
  close  : P.Kc.OK
  test₁  : P.TP.D₁.OK
  test₂  : P.TP.D₂.OK
  test₁B : P.TB.D₁.OK
  test₂B : P.TB.D₂.OK

end LdObjP

def Spec.ldObjP_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] : Prop :=
  ∀ (P : LdObjP F E) (L : ℕ), P.Hyp L → P.toT.Hyp L

theorem ldObjP_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldObjP_hyp F E := by
  intro P L h
  obtain ⟨hV1, hV2, hV3, hV4, hV5⟩ :=
    ldLinVL_all E _ _ _ _ P.on.ol.toC P.pB P.TB P.N P.q₀B P.bB' P.tie' P.cA' P.same' P.x₀ P.y₀ P.QV'
      P.SnB P.qaB P.baB h.r.shared h.r.restB h.r.saysAB h.test₁B h.test₂B h.r.leftV h.r.tieC
      h.r.qaOK h.r.needNA h.r.needNW h.r.needNU h.r.needNO
  have hSaysB :=
    ldLinPlan_says E _ _ _ _ P.on.ol.toC P.pB _ P.TB.Q'.base P.TB.fa h.r.restB h.r.saysAB
  have hQB : P.TB.Q.OK :=
    ldChain_cons E P.on.ol.toC.S P.on.ol.toC.E₀ P.on.ol.toC.Wpa P.TB.D₁ _ P.TB.d₁ P.TB.d₁' h.test₁B
      (ldChain_cons E P.pB.S₁ P.on.ol.toC.E₀ P.on.ol.toC.Wpa P.TB.D₂ P.TB.Q' P.TB.d₂
        P.TB.d₂' h.test₂B h.r.leftB)
  have hDB := ldDemand_plan E _ _ _ _ P.on.ol.toC P.pB P.TB P.SnB P.qaB P.q₀B P.baB
    P.bB' h.r.leftQB h.r.qaOK
    (fun a =>
      (ldDemandLe_plan E _ _ _ _ P.on.ol.toC P.pB P.TB P.N P.bB' _ h.r.oneN).trans (h.r.needNA a))
    (fun a =>
      (ldDemandLe_plan E _ _ _ _ P.on.ol.toC P.pB P.TB P.N P.bB' _ h.r.oneN).trans (h.r.needNW a))
    (fun a =>
      (ldDemandLe_plan E _ _ _ _ P.on.ol.toC P.pB P.TB P.N P.bB' _ h.r.oneN).trans (h.r.needNU a))
    (fun a =>
      (ldDemandLe_plan E _ _ _ _ P.on.ol.toC P.pB P.TB P.N P.bB' _ h.r.oneN).trans (h.r.needNO a))
  obtain ⟨hC1, hC2⟩ := ldLinCl_chain E _ _ _ _ P.on.ol.toC P.TB.Q P.TB.fq
    (P.on.ol.toC.P.q5 P.SnB P.qaB) _ (P.on.ol.toC.P.chain P.onB P.SnB P.εfB) hSaysB hQB hDB
  have hKB := ldPlanLin_kb E _ _ _ _ P.on.ol.toC P.pB P.TB P.cA' P.same' P.N h.r.shared h.r.restB
    h.r.saysAB h.test₁B h.test₂B h.r.leftKB
  exact
    { base := h.r.base
      close := h.close
      rows := ldLinPlan_says E _ _ _ _ P.W.O.toC P.p _ P.TP.Q'.base P.TP.fa h.r.rest h.r.saysA
      plan := ldAlt_of_ok E P.W.O.toC.S P.W.O.toC.E₀ P.W.O.toC.Wpa P.TP.Q _ _
        (ldChain_cons E P.W.O.toC.S P.W.O.toC.E₀ P.W.O.toC.Wpa P.TP.D₁ _ P.TP.d₁ P.TP.d₁' h.test₁
          (ldChain_cons E P.p.S₁ P.W.O.toC.E₀ P.W.O.toC.Wpa P.TP.D₂ P.TP.Q' P.TP.d₂
            P.TP.d₂' h.test₂ h.r.left))
      demand := ldDemand_plan E _ _ _ _ P.W.O.toC P.p P.TP P.Sn
        (P.W.O.S.qFam (E₀ := extNone) P.q₀ P.Bw.t) P.q₀ P.Bw.t P.b' h.r.leftQ (fun _ hW => hW)
        h.r.needA h.r.needW h.r.needU h.r.needO
      cOk := by
        show P.cZ.forget.forget.OkFrom _
        rw [show P.cZ.forget.forget = _ from hV5]
        exact hC1
      cSides := by
        show P.cZ.forget.forget.SidesCT _
        rw [show P.cZ.forget.forget = _ from hV5]
        exact hC2
      cKB := by
        show P.cZ.forget.KB _ _ _
        rw [show P.cZ.forget = _ from hV4]
        exact hKB
      cOkV := hV1 _ _ _
      cCoh := hV2
      cEnd := hV3 }

end Cb
