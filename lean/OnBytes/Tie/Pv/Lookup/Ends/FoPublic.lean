-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPublic.lean.
The plans in the byte-level verifier's record of public numbers come from the plans' own makers.

Verify.publicOf (OnBytes/Model/VerifyPublic.lean) makes, from the three configuration files, the
record Public with the plan of every sub-proof. This file walks through it: if it returns X, then
the members of X.G and the head's plan X.H (but for its field Fp, which publicOf trims) are what
Layer.planG and Head.planH2 return, at arguments that are named in X's own fields.

* plansFrom_at, plansG_at: member number g of the list that Layer.plansG returns is what Layer.planG
  returns at g and at the member before it (none for g = 0).
* pubOf_y: Layer.Pub.of keeps the layout.
* publicOf_cut: a run of Verify.publicOf that returns X: the run equations of polLayout, scalesOf,
  Layer.plansG, the attention sub-proofs' config (at profile 4), attentionOwners, ownerOf and
  Head.planH2, each at X's own fields where X keeps the value; how X.hS, X.A and X.H are made of
  what these return. Of Layer.Pub.of no more is kept than that X.layers has the layout of
  polLayout; of publicOf's tests, of Head.layout and of the digests nothing is kept.
* public_G, public_H: the members of X.G, and X.H, from their makers.
* public_G_rows, public_H_rows: so the number of rows of the batching round that the plan names is
  the plan's field nLin plus the smallness test's equationsF (planG_rows, planH2_rows,
  OnBytes/Tie/Pv/Lookup/Ends/BatRows.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.BatRows
import OnBytes.Model.VerifyPublic

set_option autoImplicit false

namespace Fo.Pub
open OnBytes OnBytes.Model Fo.BatRows

/-- Member number i of the list is the plan at g + i and at the member before it. -/
theorem plansFrom_at (P : Layer.Pub) : ∀ (n g : Nat) (O : Option Layer.HPlan2)
    (l : List Layer.HPlan2), Layer.plansFrom P n g O = .ok l → ∀ (i : Nat) (hp : Layer.HPlan2),
    l[i]? = some hp → Layer.planG P (g + i) (if i = 0 then O else l[i - 1]?) = .ok hp
  | 0, g, O, l, h, i, hp, hi => by
    obtain rfl : [] = l := Except.ok.inj h
    cases hi
  | n + 1, g, O, l, h, i, hp, hi => by
    unfold Layer.plansFrom at h
    obtain ⟨p, h1, h⟩ := bindE_ok h
    obtain ⟨l', h2, h⟩ := bindE_ok h
    obtain rfl : p :: l' = l := Except.ok.inj h
    cases i with
    | zero =>
      obtain rfl : p = hp := Option.some.inj hi
      exact h1
    | succ j =>
      have ih := plansFrom_at P n (g + 1) (some p) l' h2 j hp hi
      have e1 : g + 1 + j = g + (j + 1) := by omega
      rw [e1] at ih
      rw [if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel]
      cases j with
      | zero => exact ih
      | succ k =>
        rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel] at ih
        exact ih

/-- Member number g of the layers' plans. -/
theorem plansG_at (P : Layer.Pub) (G : Array Layer.HPlan2) (h : Layer.plansG P = .ok G) (g : Nat)
    (hp : Layer.HPlan2) (hg : G[g]? = some hp) :
    Layer.planG P g (if g = 0 then none else G[g - 1]?) = .ok hp := by
  unfold Layer.plansG at h
  obtain ⟨l, h1, h⟩ := bindE_ok h
  obtain rfl : l.toArray = G := Except.ok.inj h
  have e := plansFrom_at P P.y.NGr 0 none l h1 g hp (by simpa using hg)
  rw [Nat.zero_add] at e
  simpa using e

/-- Layer.Pub.of keeps the layout. -/
theorem pubOf_y {y : Layer.Lay} {sc : Layer.Scales} {rope : Array Nat} {wsLay : WsLay} {V : Nat}
    {tokv : Array Nat} {set : Settings} {L : Layer.Pub}
    (h : Layer.Pub.of y sc rope wsLay V tokv set = .ok L) : L.y = y := by
  unfold Layer.Pub.of at h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨rd, _, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  rfl

/-- A test that is made in one branch alone; both branches go on alike. -/
theorem ite_unit_ok {c : Prop} [Decidable c] {ε β : Type} {x : Except ε PUnit}
    {K : PUnit → Except ε β} {b : β}
    (h : (if c then x >>= K else pure PUnit.unit >>= K) = .ok b) : K PUnit.unit = .ok b := by
  rcases ite_ok h with ⟨_, h⟩ | ⟨_, h⟩
  · obtain ⟨_, _, h⟩ := bindE_ok h
    exact h
  · exact h

/-- A value that one branch computes and the other sets; both branches go on alike. -/
theorem ite_pure_ok {c : Prop} [Decidable c] {ε α γ β : Type} {x : Except ε α} {g : α → γ} {v : γ}
    {K : γ → Except ε β} {b : β}
    (h : (if c then x >>= fun a => pure (g a) >>= K else pure v >>= K) = .ok b) :
    ∃ y, ((c ∧ ∃ a, x = .ok a ∧ y = g a) ∨ (¬ c ∧ y = v)) ∧ K y = .ok b := by
  rcases ite_ok h with ⟨hc, h⟩ | ⟨hc, h⟩
  · obtain ⟨a, h1, h⟩ := bindE_ok h
    exact ⟨g a, .inl ⟨hc, a, h1, rfl⟩, h⟩
  · exact ⟨v, .inr ⟨hc, rfl⟩, h⟩

/-- The number that names group g's matrix qa, as publicOf hands it to the attention sub-proofs'
config. -/
def midQ (y : Layer.Lay) (g : Nat) : Nat :=
  (((Layer.tailsOf y).getD g {}).mats.getD (Layer.matIx y).iQA {}).aId

/-- What publicOf shows of a layer's plan, and of an attention's, to the tests across plans. -/
def seenG (G : Array Layer.HPlan2) : Array Verify.SubPlan := G.map fun O => ⟨O.tl, O.Fp, O.Tp⟩
def seenA0 (A0 : Array Attention.Plan) : Array Verify.SubPlan :=
  A0.map fun X => ⟨X.seam.tl, X.seam.Fp, X.seam.Tp⟩

/-- A run of publicOf that returns, in X's own fields. -/
theorem publicOf_cut (pol KL : ByteArray) (layout : Option ByteArray) (X : Verify.Public)
    (h : Verify.publicOf pol KL layout = .ok X) :
    Verify.polLayout pol = .ok (X.P, X.layers.y) ∧
    X.hS = Verify.headShape X.P X.layers.y ∧
    Layer.plansG X.layers = .ok X.G ∧
    Verify.ownerOf X.layers.y X.G = .ok X.owner ∧
    (∃ H0, Head.planH2 X.P.settings X.hS X.HLy (Verify.borderOf X.layers.y) X.owner
        X.layers.y.NGr X.P.lkW = .ok H0 ∧ X.H = { H0 with Fp := H0.Fp.trimL }) ∧
    ∃ (sc : Layer.Scales) (A0 : Array Attention.Plan) (seen : Array Verify.SubPlan),
      Layer.scalesOf X.layers.y.h (fileWords KL) = .ok sc ∧
      ((X.layers.y.h.p4 = true ∧
          ∃ c, Attention.config X.P X.layers.y sc (midQ X.layers.y) = .ok c ∧ A0 = c.plans) ∨
        (X.layers.y.h.p4 = false ∧ A0 = #[])) ∧
      Verify.attentionOwners X.layers.y.h.p4 X.layers.y.NGr (seenG X.G) (seenA0 A0) = .ok seen ∧
      X.A = A0.zipWith (fun X s => { X with seam := { X.seam with tl := s.tl } }) seen := by
  unfold Verify.publicOf at h
  obtain ⟨⟨P, y⟩, k1, h⟩ := bindE_ok h
  dsimp only at h
  obtain ⟨sc, k2, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have h := ite_unit_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨wsLay, _, h⟩ := bindE_ok h
  obtain ⟨rope, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨HLy, _, h⟩ := bindE_ok h
  obtain ⟨y2, k3, h⟩ := ite_pure_ok h
  obtain ⟨layers, k4, h⟩ := bindE_ok h
  obtain ⟨G, k5, h⟩ := bindE_ok h
  obtain ⟨seen, k6, h⟩ := bindE_ok h
  obtain ⟨owner, k7, h⟩ := bindE_ok h
  obtain ⟨H0, k8, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  have hy : layers.y = y := pubOf_y k4
  dsimp only
  rw [hy]
  refine ⟨k1, rfl, k5, k7, ⟨H0, k8, rfl⟩, sc, y2.1, seen, k2, ?_, k6, rfl⟩
  rcases k3 with ⟨hp, c, k9, e⟩ | ⟨hp, e⟩
  · exact .inl ⟨hp, c, k9, by rw [e]⟩
  · exact .inr ⟨by simpa using hp, by rw [e]⟩

/-- The members of X.G come from Layer.planG. -/
theorem public_G {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) :
    Layer.planG X.layers g (if g = 0 then none else X.G[g - 1]?) = .ok hp :=
  plansG_at X.layers X.G (publicOf_cut pol KL layout X h).2.2.1 g hp hg

/-- So the rows of a layer's batching round. -/
theorem public_G_rows {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) :
    hp.nBatched = hp.nLin + hp.tl.equationsF (Layer.readsCount X.layers.y X.layers.rd g) :=
  planG_rows X.layers g _ hp (public_G h g hp hg)

/-- X.H comes from Head.planH2. -/
theorem public_H {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) :
    ∃ H0, Head.planH2 X.P.settings X.hS X.HLy (Verify.borderOf X.layers.y) X.owner
      X.layers.y.NGr X.P.lkW = .ok H0 ∧ X.H = { H0 with Fp := H0.Fp.trimL } :=
  (publicOf_cut pol KL layout X h).2.2.2.2.1

/-- So the rows of the head's batching round. -/
theorem public_H_rows {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) :
    X.H.rows = X.H.nLin +
      X.H.tl.equationsF (Head.readsH X.hS X.HLy (Verify.borderOf X.layers.y)) := by
  obtain ⟨H0, h1, h2⟩ := public_H h
  rw [h2]
  exact planH2_rows _ _ _ _ _ _ _ H0 h1

end Fo.Pub
