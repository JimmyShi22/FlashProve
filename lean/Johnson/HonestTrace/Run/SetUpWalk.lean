-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/Run/SetUpWalk.lean

The walk through the library's "publicOfO_of_parts" (Johnson/AtFull/Public/Ledger.lean) at a turned
scan and a turned layout. Theorems alone; no definition. All stand at variable files and records:
no stored file is named here.

Main theorems:
* "base_steps": where "publicOfO" returns X and X.layers.y.h.p4 is true: its steps on attention
  and behind it, with the return of "configO" kept. At any hash o.
* "zip_at": a member of attention's plans as "publicOfO" returns them.
* "public_turn": where "publicOfO" returns X₀ at one set of files and, at another set, the layout's
  step returns the scan and layout of X₀ turned (p1), the steps that read a free thing or take the
  hash return (p2 to p7, p10, p11, p13), and "configO" returns plans alike to those of X₀ (p14):
  there "publicOfO" returns an X with "SamePlans X X₀" (Johnson/HonestTrace/Run/SetUpSame.lean).

Limits. "public_turn" is stated at "secondHashFunction" alone. Its hypotheses h₀, h3, h4 and the eleven marked
p are not proved here; the steps p8, p8', p9 and p15 to p20 are shown inside its proof.

Where a text comes from. The proof of "base_steps" repeats the walk of the library's
"publicSteps_of_O" (Johnson/Desc/Ok/PlanWritten/PublicAtSteps.lean), and that of "zip_at" lines of
the library's "cut_A" (Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean).

Not claimed: any property of a release, of a verifier or of a prover.
-/
import Johnson.HonestTrace.Run.SetUpTurn
import Johnson.HonestTrace.Run.SetUpSame
import Johnson.Desc.Ok.PlanWritten.PublicAtSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HonestTraceRun

namespace SetUp

open OnBytes OnBytes.Model OnBytes.Model.Verify
open VerifierAndGoals (FreeLines)
open Fo.BatRows (bindE_ok)
open Fo.Pub (ite_unit_ok ite_pure_ok midQ seenG seenA0)
open OnBytes.Road.K4.Trial.AttL2 (mqOf seenGOf AOf publicOfO_of_parts)
open VerifiableInference.PlanWritten (publicOfO tableHeldO hParO publicSteps_of_O pubOf_fields)

/-- **The base's steps on attention and behind it, with the run of configO kept.** The walk of the library's
publicSteps_of_O (Johnson/Desc/Ok/PlanWritten/PublicAtSteps.lean:124), which keeps of that run what takes no hash. -/
theorem base_steps {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray} {layout : Option ByteArray}
    {X : Public} (h : publicOfO o pol KL layout = .ok X) (h4 : X.layers.y.h.p4 = true) :
    ∃ (c : Attention.Config) (seen : Array SubPlan) (H0 : Head.HPlanH2),
      VerifiableInference.PlanWritten.Attention.configO o X.P X.layers.y X.layers.sc
        (midQ X.layers.y) = .ok c ∧
      attentionOwners X.layers.y.h.p4 X.layers.y.NGr (seenG X.G) (seenA0 c.plans) = .ok seen ∧
      X.A = c.plans.zipWith (fun X s => { X with seam := { X.seam with tl := s.tl } }) seen ∧
      Head.planH2 X.P.settings X.hS X.HLy (borderOf X.layers.y) X.owner X.layers.y.NGr X.P.lkW =
        .ok H0 ∧
      X.H = { H0 with Fp := H0.Fp.trimL } ∧
      crossPlans (X.G.size - 1 + X.A.size + 1) X.layers.y.NGr X.layers.y.h.p4
        (Layer.tailsOf X.layers.y) (seenG X.G) seen ⟨H0.tl, H0.Fp, H0.Tp⟩ = .ok () := by
  unfold VerifiableInference.PlanWritten.publicOfO at h
  obtain ⟨⟨P, y⟩, k1, h⟩ := bindE_ok h
  dsimp only at h
  obtain ⟨sc, k2, h⟩ := bindE_ok h
  obtain ⟨_, t3, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have h := ite_unit_ok h
  obtain ⟨_, t6, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, t8, h⟩ := bindE_ok h
  obtain ⟨_, t9, h⟩ := bindE_ok h
  obtain ⟨wsLay, t10, h⟩ := bindE_ok h
  obtain ⟨rope, t11, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨HLy, t13, h⟩ := bindE_ok h
  obtain ⟨y2, k3, h⟩ := ite_pure_ok h
  obtain ⟨layers, k4, h⟩ := bindE_ok h
  obtain ⟨G, k5, h⟩ := bindE_ok h
  obtain ⟨seen, k6, h⟩ := bindE_ok h
  obtain ⟨owner, k7, h⟩ := bindE_ok h
  obtain ⟨H0, k8, h⟩ := bindE_ok h
  obtain ⟨_, t20, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  obtain ⟨ey, esc, erope, ews, -, -, -, -, -⟩ := pubOf_fields k4
  subst ey esc erope ews
  rcases k3 with ⟨_, c, k9, e⟩ | ⟨hp, _⟩
  · subst e
    exact ⟨c, seen, H0, k9, k6, rfl, k8, rfl, t20⟩
  · exact absurd h4 hp

/-- A member of the attention's plans as publicOfO returns them. (Lines of the library's cut_A, PublicAtCut.lean:263-267.) -/
theorem zip_at {A0 : Array Attention.Plan} {seen : Array SubPlan} {g : Nat} {a : Attention.Plan}
    (hg : (A0.zipWith (fun X s => { X with seam := { X.seam with tl := s.tl } }) seen)[g]? = some a) :
    ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
  rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
  obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
  exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩

/-- **THE WALK.** Where publicOfO returns X₀ at one set of files, and at another set: the layout's step returns X₀'s
scan and layout turned (p1), the steps that read a free thing or take the hash return (p2 to p7, p10, p11, p13), and
attention's config returns plans that are alike to the base's (p14): there publicOfO returns, and the plain planner
sees no difference. -/
theorem public_turn {pol pol' KL KL' : ByteArray} {layout layout' : Option ByteArray} {X₀ : Public}
    (h₀ : publicOfO secondHashFunction pol KL layout = .ok X₀)
    {vals : List (String × Nat)} {v : FreeLines} {sc : Layer.Scales} {rope : Array Nat}
    {hp : ByteArray}
    (h3 : (layTurn X₀.layers.y v).h.p3 = true) (h4 : (layTurn X₀.layers.y v).h.p4 = true)
    (p1 : polLayout pol' = .ok (scanTurn X₀.P vals v, layTurn X₀.layers.y v))
    (p2 : Layer.scalesOf (layTurn X₀.layers.y v).h (fileWords KL') = .ok sc)
    (p3 : Layer.scalesHeld (layTurn X₀.layers.y v).h sc = .ok ())
    (p4 : tableHeldO secondHashFunction (scanTurn X₀.P vals v) .silu (layTurn X₀.layers.y v).silu = .ok ())
    (p5 : tableHeldO secondHashFunction (scanTurn X₀.P vals v) .sigmoid (layTurn X₀.layers.y v).fs = .ok ())
    (p6 : Layer.noWrap (layTurn X₀.layers.y v).h sc (layTurn X₀.layers.y v).dq = .ok ())
    (p7 : hParO secondHashFunction pol' KL' layout' = .ok hp)
    (p10 : Layer.ropeOf (layTurn X₀.layers.y v).h = .ok rope)
    (p11 : tableHeldO secondHashFunction (scanTurn X₀.P vals v) .rope rope = .ok ())
    (p13 : Head.layout (headShape (scanTurn X₀.P vals v) (layTurn X₀.layers.y v))
      (layTurn X₀.layers.y v).tauFC = .ok X₀.HLy)
    (p14 : ∀ c₀ : Attention.Config,
      VerifiableInference.PlanWritten.Attention.configO secondHashFunction X₀.P X₀.layers.y X₀.layers.sc
        (mqOf X₀.layers.y) = .ok c₀ →
      ∃ c : Attention.Config,
        VerifiableInference.PlanWritten.Attention.configO secondHashFunction (scanTurn X₀.P vals v)
          (layTurn X₀.layers.y v) sc (mqOf X₀.layers.y) = .ok c ∧
        c.plans.size = c₀.plans.size ∧
        (∀ (g : Nat) (a a₀ : Attention.Plan), c.plans[g]? = some a → c₀.plans[g]? = some a₀ →
          a.seam = a₀.seam ∧ a.ns = a₀.ns ∧ a.own = a₀.own ∧
            OnBytes.Model.forestSize a.fs = OnBytes.Model.forestSize a₀.fs) ∧
        (c.plans.map fun X => (⟨X.seam.tl, X.seam.Fp, X.seam.Tp⟩ : SubPlan)) =
          c₀.plans.map fun X => ⟨X.seam.tl, X.seam.Fp, X.seam.Tp⟩) :
    ∃ X, publicOfO secondHashFunction pol' KL' layout' = .ok X ∧ SamePlans X X₀ := by
  have S₀ := publicSteps_of_O h₀
  obtain ⟨c₀, seen, H0, k9, k6, kA, k8, kH, k20⟩ := base_steps h₀ h4
  obtain ⟨c, q14, hsz, hix, harr⟩ := p14 c₀ k9
  have p8 : Layer.weightWidthsHeld (layTurn X₀.layers.y v).h (layTurn X₀.layers.y v).kinds = .ok () :=
    (widths_turn X₀.layers.y v).trans S₀.widths
  have p8' : Head.vocabulary (headShape (scanTurn X₀.P vals v) (layTurn X₀.layers.y v)) = .ok () := by
    rw [vocabulary_turn, ← S₀.hS]
    exact S₀.vocab
  have p9 : wsLayOf (weightShape (scanTurn X₀.P vals v) (layTurn X₀.layers.y v))
      (layTurn X₀.layers.y v).h.p3 (scanTurn X₀.P vals v).lkW = .ok X₀.layers.wsLay :=
    (wsLay_turn X₀.P X₀.layers.y vals v).trans S₀.wsLay
  have p15 : Layer.Pub.of (layTurn X₀.layers.y v) sc rope X₀.layers.wsLay (scanTurn X₀.P vals v).h.V #[]
      (scanTurn X₀.P vals v).settings = .ok (pubTurn X₀.layers v sc rope) :=
    pubOf_turn S₀.layers v sc rope
  have p16 : Layer.plansG (pubTurn X₀.layers v sc rope) = .ok X₀.G :=
    (plansG_turn X₀.layers v sc rope).trans S₀.plans
  have p17 : attentionOwners (layTurn X₀.layers.y v).h.p4 (layTurn X₀.layers.y v).NGr (seenGOf X₀.G)
      (c.plans.map fun X => (⟨X.seam.tl, X.seam.Fp, X.seam.Tp⟩ : SubPlan)) = .ok seen := by
    rw [harr]
    exact k6
  have p18 : ownerOf (layTurn X₀.layers.y v) X₀.G = .ok X₀.owner :=
    (owner_turn X₀.layers.y v X₀.G).trans S₀.owner
  have p19 : Head.planH2 (scanTurn X₀.P vals v).settings
      (headShape (scanTurn X₀.P vals v) (layTurn X₀.layers.y v)) X₀.HLy
      (borderOf (layTurn X₀.layers.y v)) X₀.owner (layTurn X₀.layers.y v).NGr
      (scanTurn X₀.P vals v).lkW = .ok H0 := by
    rw [planH2_turn, ← S₀.hS]
    exact k8
  have eA : (AOf c.plans seen).size = X₀.A.size := by
    rw [kA]
    unfold OnBytes.Road.K4.Trial.AttL2.AOf
    rw [Array.size_zipWith, Array.size_zipWith, hsz]
  have p20 : crossPlans (X₀.G.size - 1 + (AOf c.plans seen).size + 1) (layTurn X₀.layers.y v).NGr
      (layTurn X₀.layers.y v).h.p4 (Layer.tailsOf (layTurn X₀.layers.y v)) (seenGOf X₀.G) seen
      ⟨H0.tl, H0.Fp, H0.Tp⟩ = .ok () := by
    rw [eA]
    exact k20
  have q14' : VerifiableInference.PlanWritten.Attention.configO secondHashFunction (scanTurn X₀.P vals v)
      (layTurn X₀.layers.y v) sc (mqOf (layTurn X₀.layers.y v)) = .ok c := by
    rw [mq_turn]
    exact q14
  have R := publicOfO_of_parts (o := secondHashFunction) (layout := layout') h3 h4 p1 p2 p3 p4 p5 p6 p7 p8 p8' p9
    p10 p11 p13 q14' p15 p16 p17 p18 p19 p20
  refine ⟨_, R, ?_⟩
  exact {
    frame := rfl
    lay := ⟨v.eps1, v.eps2, v.epsF, rfl⟩
    rd := rfl
    wsLay := rfl
    G := rfl
    H := kH.symm
    HLy := rfl
    head := by
      rw [S₀.hS]
      exact ⟨rfl, rfl, rfl⟩
    sizeA := eA
    A := by
      intro g a a₀ hg hg₀
      rw [kA] at hg₀
      obtain ⟨b, s, e1, e2, rfl⟩ := zip_at hg
      obtain ⟨b₀, s₀, f1, f2, rfl⟩ := zip_at hg₀
      obtain rfl : s = s₀ := Option.some.inj (e2.symm.trans f2)
      obtain ⟨r1, r2, r3, r4⟩ := hix g b b₀ e1 f1
      refine ⟨?_, r2, r3, r4⟩
      show ({ b.seam with tl := s.tl } : _) = { b₀.seam with tl := s.tl }
      rw [r1] }

end SetUp

end HonestTraceRun

#print axioms HonestTraceRun.SetUp.base_steps
#print axioms HonestTraceRun.SetUp.zip_at
#print axioms HonestTraceRun.SetUp.public_turn
