-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/KeysAtPlan.lean: CONDITIONAL: what the four key forms of an attention
segment are worth (`kf_is_ext`, Johnson/Desc/K5/Honest/Law/Keys.lean), with its public premises
paid: at a plan that the verifier's planner returns and that passes this library's one test on a
plan, and at the library's one head on the public input. A joining of lemmas; no algebra is in this
file.

What is paid, and by what. `CallsAre`: `callsAre_of` (Johnson/Desc/First/Att/Claims/Place.lean),
from the place's four calls and the return of the verifier's function of the points. `KeyPub`:
`key_pub` (Johnson/Desc/First/Att/Claims/KeyPubOf.lean), from the same, the test's clauses, and that
each call's key point is the lookup's cut of its end point. The three conditions on the lookup's
numbers: the test's clause `CallsFit`. The table of scales is the shape's (`sclOf`,
Johnson/Road/Lane5AttDef.lean); the tables tb are a free letter.

Main names:
  `lookAll_pubOf`   the premise Lk at the challenges made of the prover's, from two lengths
  `kf_at_law`       at a shape that the planner of shapes returns, under the plan's law
  `kf_at_plan`      at a plan that the planner returns and that passes the one test
  `kf_at_head`      **at the head's letters, for each of the twelve groups**

WHAT IS LEFT AS A PREMISE: N: the reading takes numerals to numbers (it holds of the reading of the
field's elements: `gl_numerals`, Johnson/Road/FormsKeysKit.lean). Lk, hK: the library's z is the
lookup's end point, read, and each call's key point is the lookup's cut of it: the lookup's; Lk's
equation holds by the make where the z of p is laid as that end point, read (`lookAll_pubOf`). hg,
hz: the claims' reading is at the shape's numbers and at the key points of what the lookup left. hP,
ha1, ha2, hk1, hk2, h1, hk: the verifier's function of the points and its runs "first" and "keys"
return, with two remainder units and two softmax-table units. hv (`RuleAt`): every named scalar that
the key forms read has its rule value on the cells t under its slot: the one premise on values.
Limits. That any of these is met at a state of an honest run is not shown here. The head is a
hypothesis. A plan with two shifts in a group (six calls) does not pass the test and is not reached.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.Claims.BackJoin
import Johnson.Desc.K5.Honest.Law.Keys
import Johnson.Desc.K5.Honest.Law.PublicAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (geoOf ScoreP planOkAll)
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP PadIn)
open Inst.Model.AttSeg (Pub Raw keyVec)
open K5Law (unitsSix oldOf sixTop PlanLaw LookAll KeyIs)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K}

/-- **The premise on the lookup's end point holds by the make**, where the z of the library's
challenges is laid as that end point, read; its two lengths are asked. -/
theorem lookAll_pubOf (ρ : Reading K) (P : Pub5) (c : Chal) {fs : Model.Forest.Shape}
    {zx zy : Array E} (sx : zx.size = fs.dT) (sy : zy.size = fs.rK) :
    LookAll ρ fs zx zy (pubOf ρ P c (pt ρ (zx ++ zy))) :=
  ⟨sx, sy, fun _ => rfl⟩

section
variable {S : Attention.Shape} {fs : Model.Forest.Shape} {gL : Forest.Heard} {i : P.Runs.In}
  {n : ℕ} {l₁ : List Aff} {j : JoinsP} {k3 : PadIn} {kf : Array Aff} {zx zy : Array E}
  {hh : P.Heard} {L' : P.Left} {a1 a2 : ℕ} {k1 k2 : ScoreP} {p : Pub K} {t : Raw → K}

/-- **The key forms are four, and each is worth the extension of its call's vector of looked-up
values at the call's key point**, at a shape that the planner of shapes returns, under the plan's
law. Conditional; what is left as a premise is listed in the file's head. A: any plan: a letter of
a called law's that the conclusion does not read. -/
theorem kf_at_law (A : Plan) {lid : ℕ} {cf : Attention.Cfg}
    (hid : shapeHid lid cf = Except.ok (S, fs)) (PL : PlanLaw cf S fs) (N : Numerals ρ)
    (Lk : LookAll ρ fs zx zy p) (hK : ∀ q : Fin 4, KeyIs fs zx zy (gL.zk.getD q.val #[]) q)
    (hg : i.g = geoOf S) (hz : i.zk = gL.zk) (hP : P.pointsOf i.g gL.zk hh L' = some i.p)
    (ha1 : hh.remainders[0]? = some a1) (ha2 : hh.remainders[1]? = some a2)
    (hk1 : i.p.scores[0]? = some k1) (hk2 : i.p.scores[1]? = some k2)
    (h1 : P.Runs.firstRun i n = some (l₁, j)) (hk : P.Runs.keysRun i k3 j = some kf)
    (tb : Inst.Model.Tables)
    (hv : RuleAt W (oldOf S gL i) (unitsSix (oldOf S gL i) (sixTop S i gL.zk a1 a2 k1 k2))
      (L5.dimOf S) (L5.callsOf fs) p t) :
    kf.size = 4 ∧ ∀ c : Fin 4, (kf.getD c.val (Aff.ofConst zeroE)).value ρ W =
      Blocks.ext ((L5.callsOf fs).a c) (keyVec (scl := L5.sclOf S) (L5.dimOf S) tb t c)
        ((L5.callsOf fs).zC c p.z) := by
  letI : Inst.Model.Scl := L5.sclOf S
  have KP := K5Law.key_pub (gL := gL) (a1 := a1) (a2 := a2) (L5.sclOf S) rfl N hid PL.usual PL.fit
    Lk hK PL.place hg hP hk1 hk2 (K5Law.first_at_old hg hz h1) PL.key rfl
  -- The plan that the called law takes stands in one premise alone (its number of calls is the
  -- shape's) and nowhere in the conclusion: so any plan A with that number laid in serves.
  exact kf_is_ext { A with NC := S.calls.size } hg hz rfl h1 hk
    (K5Law.callsAre_of PL.place hg hP ha1 ha2 hk1 hk2) KP tb hv (L5.callsFit_ok PL.fit)
    (L5.callsFit_deep PL.fit) (L5.callsFit_a01 PL.fit)

end

section
variable {gL : Forest.Heard} {i : P.Runs.In} {n : ℕ} {l₁ : List Aff} {j : JoinsP} {k3 : PadIn}
  {kf : Array Aff} {zx zy : Array E} {hh : P.Heard} {L' : P.Left} {a1 a2 : ℕ} {k1 k2 : ScoreP}
  {p : Pub K} {t : Raw → K}

/-- **The same at a plan that the planner returns and that passes the one test.** -/
theorem kf_at_plan {settings : Model.Settings} {inp : Attention.In} {cf : Attention.Cfg}
    {A : Plan} (hA : Attention.plan settings inp cf = Except.ok A)
    (hok : planOkAll cf A.S A.fs = true) (N : Numerals ρ) (Lk : LookAll ρ A.fs zx zy p)
    (hK : ∀ q : Fin 4, KeyIs A.fs zx zy (gL.zk.getD q.val #[]) q) (hg : i.g = geoOf A.S)
    (hz : i.zk = gL.zk) (hP : P.pointsOf i.g gL.zk hh L' = some i.p)
    (ha1 : hh.remainders[0]? = some a1) (ha2 : hh.remainders[1]? = some a2)
    (hk1 : i.p.scores[0]? = some k1) (hk2 : i.p.scores[1]? = some k2)
    (h1 : P.Runs.firstRun i n = some (l₁, j)) (hk : P.Runs.keysRun i k3 j = some kf)
    (tb : Inst.Model.Tables)
    (hv : RuleAt W (oldOf A.S gL i) (unitsSix (oldOf A.S gL i) (sixTop A.S i gL.zk a1 a2 k1 k2))
      (L5.dimOf A.S) (L5.callsOf A.fs) p t) :
    kf.size = 4 ∧ ∀ c : Fin 4, (kf.getD c.val (Aff.ofConst zeroE)).value ρ W =
      Blocks.ext ((L5.callsOf A.fs).a c) (keyVec (scl := L5.sclOf A.S) (L5.dimOf A.S) tb t c)
        ((L5.callsOf A.fs).zC c p.z) :=
  kf_at_law A (L5.plan_shape hA).1 (P.plan_all (L5.plan_shape hA).1 hok).law N Lk hK hg hz hP ha1
    ha2 hk1 hk2 h1 hk tb hv

/-- **The same at the head's letters**, for the stored plan a of group g. Conditional: the head;
hg': the group; ea: the group's plan; and what is listed in the file's head. -/
theorem kf_at_head {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place} (h : P5J.AtMgA o Z D r Zp Np cF x) {g : ℕ}
    (hg' : g < 12) {a : Plan} (ea : (P5J.At.X Zp).A[g]? = some a) (N : Numerals ρ)
    (Lk : LookAll ρ a.fs zx zy p) (hK : ∀ q : Fin 4, KeyIs a.fs zx zy (gL.zk.getD q.val #[]) q)
    (hg : i.g = geoOf a.S) (hz : i.zk = gL.zk) (hP : P.pointsOf i.g gL.zk hh L' = some i.p)
    (ha1 : hh.remainders[0]? = some a1) (ha2 : hh.remainders[1]? = some a2)
    (hk1 : i.p.scores[0]? = some k1) (hk2 : i.p.scores[1]? = some k2)
    (h1 : P.Runs.firstRun i n = some (l₁, j)) (hk : P.Runs.keysRun i k3 j = some kf)
    (tb : Inst.Model.Tables)
    (hv : RuleAt W (oldOf a.S gL i) (unitsSix (oldOf a.S gL i) (sixTop a.S i gL.zk a1 a2 k1 k2))
      (L5.dimOf a.S) (L5.callsOf a.fs) p t) :
    kf.size = 4 ∧ ∀ c : Fin 4, (kf.getD c.val (Aff.ofConst zeroE)).value ρ W =
      Blocks.ext ((L5.callsOf a.fs).a c) (keyVec (scl := L5.sclOf a.S) (L5.dimOf a.S) tb t c)
        ((L5.callsOf a.fs).zC c p.z) := by
  obtain ⟨hid, PL⟩ := law_at_head h hg' ea
  exact kf_at_law a hid PL N Lk hK hg hz hP ha1 ha2 hk1 hk2 h1 hk tb hv

end

end H2K5.Honest

#print axioms H2K5.Honest.lookAll_pubOf
#print axioms H2K5.Honest.kf_at_law
#print axioms H2K5.Honest.kf_at_plan
#print axioms H2K5.Honest.kf_at_head
