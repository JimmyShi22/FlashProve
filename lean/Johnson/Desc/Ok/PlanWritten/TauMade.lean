-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/TauMade.lean: the number tau of random combinations in every sub-proof's
smallness test, as the public part of a stage holds it (`publicOfO`,
Johnson/Desc/Ok/PlanWritten/PublicAt.lean).

Why. The planner refuses public files at which a sub-proof's tau is not the number of combinations
that follows from the setting (the test "plan-tau", `planSmall`, OnBytes/Params/SubRounds.lean).
Where the plan is a written value and the planner is not run, nothing asks that test. Here it is
shown from which line of the parameter file each sub-proof's tau comes, in the text that makes the
public part, which is still run.

The statements are tools: they hold of all public files and all arguments o, and no description of
the protocol is named.

  `addTreesF_floor`: where `HTailF2.addTreesF` (OnBytes/Model/Tail.lean) returns a value, tau is at
    least the level that it was handed (its test "policy-tau-hb").
  `planG_tau`, `planH2_tau`, `planA_tau`: the plan of a layer sub-proof, of the head's and of an
    attention sub-proof (`Layer.planG`, `Head.planH2`, `Attention.plan`) has the settings' tau, and
    it is at least the settings' level. `seamShape_tau`, `seamPlan_floor`: two steps of the third.
  `TauOf P tl`: tl.tau is the line tau of the scan P, and is at least the level P.frame.sec.
    `publicOfO_tau_G`, `publicOfO_tau_A`, `publicOfO_tau_H`, `publicOfO_tau`: it holds at every
    layer sub-proof, every attention sub-proof and the head's sub-proof of what `publicOfO o`
    returns.
  `publicOfO_floor`: so the line tau is at least the level wherever `publicOfO o` returns a value:
    public files whose line tau is below their level are refused in that text. (The text asks the
    same of the line itself earlier, under the same name: `polBehindLayout`,
    OnBytes/Model/Config.lean. The proof here goes by the head's sub-proof.)

What is used. A computation of `publicOfO` that returns a value, in the fields of what it returns:
`publicOfO_cut`, `configO_at` (Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean). That the record's tau
is kept by `shapeF`, `addTreesF`, `borderMeans`, `ownerIs`, `ownerHeld`, `Seam.plan` and
`attentionOwners` is the library's (`Fo.Core` and its laws,
OnBytes/Tie/Pv/Lookup/Ends/FoTailCore.lean, FoPlanSize.lean; `owners_keeps`, FoPublicA.lean). Of
OnBytes/Model/: the routines named.

Limits. Nothing is said of the columns of a smallness test, nor of which rounds a plan has. Nothing
says that a value is returned. Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.PublicAtCut
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicANm
import OnBytes.Tie.Pv.Lookup.Ends.FoTailCore
import OnBytes.Tie.Pv.Tail.EndSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten

open OnBytes OnBytes.Model OnBytes.Model.Verify
open Fo.BatRows (bindE_ok ite_ok)
open OnBytes.Tie.Pv.Tail.Port (ite_throw_ok)

/-! ## 1. The routine that adds the arrays asks that tau is not below the level -/

/-- Where `addTreesF` returns a value, tau is at least the level that it was handed. -/
theorem addTreesF_floor {tl : HTailF2} {F : Fork} {T : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} {r : HTailF2 × Fork × Tail2}
    (h : tl.addTreesF F T nU aTX hb hbLine = .ok r) : hbLine ≤ tl.tau := by
  unfold HTailF2.addTreesF at h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨ht, _⟩ := (ite_throw_ok _ _ _ _).1 h
  exact Nat.le_of_not_lt ht

/-! ## 2. The three makers of a sub-proof's plan -/

/-- A layer sub-proof's plan has the settings' tau, and it is at least the settings' level. -/
theorem planG_tau {P : Layer.Pub} {g : Nat} {O : Option Layer.HPlan2} {hp : Layer.HPlan2}
    (h : Layer.planG P g O = .ok hp) : hp.tl.tau = P.set.tau ∧ P.set.hb ≤ hp.tl.tau := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have k0 : tl.tau = P.set.tau := (Fo.shapeF_size hS).2.2
  have kf : P.set.hb ≤ tl.tau := addTreesF_floor hA
  have k1 : tl1.tau = P.set.tau := (Fo.addTreesF_core hA).2.2.trans k0
  have k2 : (tl1.ownerIs g).tau = P.set.tau := k1
  have key : hp.tl.tau = P.set.tau := by
    dsimp only at h
    split at h
    · obtain ⟨_, _, h⟩ := bindE_ok h
      obtain ⟨y, hy, h⟩ := bindE_ok h
      obtain rfl := Fo.pureE_ok hy
      obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      exact k2
    · split at h
      · repeat obtain ⟨_, _, h⟩ := bindE_ok h
        cases h
        have hy := Fo.pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
        have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
        dsimp only
        rw [hy]
        exact (Fo.borderMeans_core hB).2.2.trans k2
      · obtain ⟨_, hx, _⟩ := bindE_ok h
        cases hx
  exact ⟨key, by rw [key, ← k0]; exact kf⟩

/-- The head's sub-proof's plan likewise. -/
theorem planH2_tau {g : Settings} {h : Head.Shape} {L : Head.HL} {b : Head.Border}
    {O : Head.Owner} {NGr lkW : Nat} {hp : Head.HPlanH2}
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) : hp.tl.tau = g.tau ∧ g.hb ≤ hp.tl.tau := by
  unfold Head.planH2 at e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl1, hsh, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨⟨tla, Fa, Ta⟩, hadd, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨Tp, _, e⟩ := bindE_ok e
    obtain ⟨tlF, ho, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain rfl := Except.ok.inj e
    have k0 : tl1.tau = g.tau := (Fo.shapeF_size hsh).2.2
    have kf : g.hb ≤ tl1.tau := addTreesF_floor hadd
    have key : tlF.tau = g.tau :=
      ((Fo.ownerHeld_core ho).2.2.trans (Fo.addTreesF_core hadd).2.2).trans k0
    exact ⟨key, by rw [key, ← k0]; exact kf⟩
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1

/-- The record that `Seam.shape` returns has the settings' tau. -/
theorem seamShape_tau {g : Settings} {m : Array TMat} {tau col0F ktO aO : Nat}
    {s : Attention.Seam} (e : Attention.Seam.shape g m tau col0F ktO aO = .ok s) :
    s.tl.tau = g.tau := by
  unfold Attention.Seam.shape at e
  dsimp only at e
  rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨tl, hS, e⟩ := bindE_ok e
  cases e
  exact (Fo.shapeF_size hS).2.2

/-- Where `Seam.plan` returns a value, tau is at least the level that it was handed. -/
theorem seamPlan_floor {s s' : Attention.Seam} {nU3 hb hbLine : Nat}
    (e : s.plan nU3 hb hbLine = .ok s') : hbLine ≤ s.tl.tau := by
  unfold Attention.Seam.plan at e
  dsimp only at e
  obtain ⟨⟨tl, Fp, T⟩, hr, e⟩ := bindE_ok e
  exact addTreesF_floor hr

/-- An attention sub-proof's plan likewise. -/
theorem planA_tau {settings : Settings} {i : Attention.In} {cf : Attention.Cfg}
    {P : Attention.Plan} (e : Attention.plan settings i cf = .ok P) :
    P.seam.tl.tau = settings.tau ∧ settings.hb ≤ P.seam.tl.tau := by
  obtain ⟨seam0, h0, h1, -⟩ := Fo.BatRows.planA_rows0 settings i cf P e
  have k0 : seam0.tl.tau = settings.tau := seamShape_tau h0
  have key : P.seam.tl.tau = settings.tau := (Fo.seamPlan_core h1).2.2.trans k0
  exact ⟨key, by rw [key, ← k0]; exact seamPlan_floor h1⟩

/-! ## 3. The public part, at every o -/

/-- What is said of the record of one sub-proof's smallness test: its tau is the parameter file's
line tau, and is at least the file's level. -/
def TauOf (P : PolScan) (tl : HTailF2) : Prop := tl.tau = P.h.tau ∧ P.frame.sec ≤ tl.tau

/-- At every layer sub-proof. -/
theorem publicOfO_tau_G {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {X : Public} (h : publicOfO o pol KL layout = .ok X) (g : Nat)
    (hp : Layer.HPlan2) (hg : X.G[g]? = some hp) : TauOf X.P hp.tl := by
  obtain ⟨-, -, hG, -, -, hs, -⟩ := publicOfO_cut h
  have k := planG_tau (Fo.Pub.plansG_at X.layers X.G hG g hp hg)
  rw [hs] at k
  exact k

/-- At the head's sub-proof. -/
theorem publicOfO_tau_H {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {X : Public} (h : publicOfO o pol KL layout = .ok X) :
    TauOf X.P X.H.tl := by
  obtain ⟨-, -, -, -, ⟨H0, h0, e⟩, -, -⟩ := publicOfO_cut h
  rw [e]
  exact planH2_tau h0

/-- At every attention sub-proof. -/
theorem publicOfO_tau_A {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {X : Public} (h : publicOfO o pol KL layout = .ok X) (g : Nat)
    (a : OnBytes.Attention.Plan) (hg : X.A[g]? = some a) : TauOf X.P a.seam.tl := by
  obtain ⟨-, -, -, -, -, -, sc, A0, seen, -, k3, k6, k7⟩ := publicOfO_cut h
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  obtain ⟨s0, f1, f2⟩ := Fo.Pub.owners_keeps k6 g s e2
  have f3 : s0 = ⟨a0.seam.tl, a0.seam.Fp, a0.seam.Tp⟩ := by
    unfold Fo.Pub.seenA0 at f1
    rw [Array.getElem?_map, e1] at f1
    exact (Option.some.inj f1).symm
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := configO_at k9
    obtain ⟨cf, m1, m2⟩ := Fo.Pub.group_plan (l2 g a0 e1)
    subst e3
    show TauOf X.P s.tl
    have k := planA_tau m2
    have e : s.tl.tau = a0.seam.tl.tau := by rw [f2.2, f3]
    unfold TauOf
    rw [e]
    exact k
  · simp at e1

/-- **At every o: every sub-proof's tau is the parameter file's line, and is at least the file's
level.** -/
theorem publicOfO_tau {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {X : Public} (h : publicOfO o pol KL layout = .ok X) :
    (∀ (g : Nat) (hp : Layer.HPlan2), X.G[g]? = some hp → TauOf X.P hp.tl) ∧
      (∀ (g : Nat) (a : OnBytes.Attention.Plan), X.A[g]? = some a → TauOf X.P a.seam.tl) ∧
      TauOf X.P X.H.tl :=
  ⟨publicOfO_tau_G h, publicOfO_tau_A h, publicOfO_tau_H h⟩

/-- So the parameter file's line tau is at least its level wherever a value is returned. -/
theorem publicOfO_floor {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {X : Public} (h : publicOfO o pol KL layout = .ok X) :
    X.P.frame.sec ≤ X.P.h.tau := by
  obtain ⟨e, f⟩ := publicOfO_tau_H h
  rw [← e]
  exact f

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.addTreesF_floor
#print axioms VerifiableInference.PlanWritten.planG_tau
#print axioms VerifiableInference.PlanWritten.planH2_tau
#print axioms VerifiableInference.PlanWritten.seamShape_tau
#print axioms VerifiableInference.PlanWritten.seamPlan_floor
#print axioms VerifiableInference.PlanWritten.planA_tau
#print axioms VerifiableInference.PlanWritten.publicOfO_tau_G
#print axioms VerifiableInference.PlanWritten.publicOfO_tau_H
#print axioms VerifiableInference.PlanWritten.publicOfO_tau_A
#print axioms VerifiableInference.PlanWritten.publicOfO_tau
#print axioms VerifiableInference.PlanWritten.publicOfO_floor
