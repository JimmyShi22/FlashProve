-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/HeardNone.lean: the parameters of every approximate range proof in what
`Verify.publicOf` returns have heard nothing: their field `heard` is `none`. Statements and proofs.
NO SOUNDNESS IS CLAIMED. ("Link" here: a member of the proof's first chain; not a proof that two
committed tables encode the same weights.)

Why. At thirteen of the 25 links a step without a round lays the PLAN's tl into the verifier's state
(Johnson/Desc/K8/ReadsQuiet.lean), and two public items of kind K3 read tl.heard. They hold behind
that step just if the plan's tl has heard nothing. No test asks it.

How. `HTailF2.piecesF` (OnBytes/Model/Tail.lean) writes heard := none, and no later step of the
three planners writes the field. The walk is that of OnBytes/Tie/Pv/Lookup/Ends/FoZPlaced1.lean and
of FoZMade.lean | FoZPublic.lean beneath it, step for step, with "b.heard = a.heard" in the place of
`SameP a b`, which does not hold that field.

Main names (namespace Fo.ZPlan):
  `piecesF_heard`, `shapeF_heard`: what piecesF | shapeF returns has heard nothing.
  `addTreesF_heard`, `ownerIs_heard`, `borderMeans_heard`, `ownerHeld_heard`, `ownerPlace_heard`,
    `owners_heard`: these steps leave the field.
  `planG_heard`, `planA_heard`, `planH2_heard`: at the three planners' returns.
  **`public_heard`**: from Verify.publicOf pol KL layout = .ok X: at hp.tl for every member hp of
    X.G, at a.seam.tl for every member a of X.A, and at X.H.tl.
(namespace VerifiableInference.Desc.First.Look):
  `HeardNoneAll X`: public_heard's conclusion, as a premise with a name.
  **`heard_none_at`**: under it: tlAt X i = some tl → tl.heard = none, at every link.

OBJECT: Verify.publicOf and the three planners beneath it (what they return).
USER: Johnson/Desc/K1/Law/HeardAtReads.lean, Johnson/Desc/AtSeats/PlanZeroInScope.lean,
  Johnson/P1K2R/PlanBoolsScope.lean, Johnson/P1K2R/LastLineTests.lean.
LETTERS: pol, KL, layout, X; i, tl.
Compiled with the whole library.


Limits. The parameters are the plans'. Nothing is said of the tl with which a run goes on.
Nor is it claimed that publicOf returns.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoZPlaced1
import Johnson.Desc.First.Look.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.ZPlan
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Tie.Pv.Tail.Port Fo.Pub
open Fo.BatRows (bindE_ok ite_ok)

/-! ### the plans' steps -/

/-- The maker of the two calls writes heard := none. -/
theorem piecesF_heard {tl tl' : HTailF2} (h : tl.piecesF = .ok tl') : tl'.heard = none := by
  unfold piecesF at h
  obtain ⟨bz, _, h⟩ := bindX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨f9, _, h⟩ := bindX h
  obtain ⟨pub, _, h⟩ := bindX h
  obtain ⟨_, _, h⟩ := bindX h
  have e := (Except.ok.inj h).symm
  subst e
  rfl

theorem shapeF_heard {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (e : tl.shapeF m txOf f hasU tau = .ok tl') : tl'.heard = none := by
  obtain ⟨tl0, hp⟩ := shapeF_pieces e
  exact piecesF_heard hp

theorem addTreesF_heard {tl tl' : HTailF2} {F F' : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', F', T')) :
    tl'.heard = tl.heard := by
  obtain ⟨-, -, e⟩ := addTreesF_fits tl tl' F F' T T' nU aTX hb hbLine h
  rw [e]

theorem ownerIs_heard (tl : HTailF2) (no : Nat) : (tl.ownerIs no).heard = tl.heard := rfl

theorem borderMeans_heard {tl tl' : HTailF2} {iF ownerNo index : Nat}
    (e : tl.borderMeans iF ownerNo index = .ok tl') : tl'.heard = tl.heard := by
  unfold HTailF2.borderMeans at e
  split at e
  · cases e
  · split at e
    · cases e
    · cases e
      rfl

theorem ownerHeld_heard {O : Head.Owner} {NGr : Nat} {tl tl' : HTailF2} {Fp : Fork} {Tp : Tail2}
    (e : Head.ownerHeld O NGr tl Fp Tp = .ok tl') : tl'.heard = tl.heard := by
  unfold Head.ownerHeld at e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hB, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain rfl := pureE_ok e
    exact borderMeans_heard hB
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

/-- Behind shapeF and addTreesF, and whatever leaves the field: nothing is heard. -/
theorem heard_made {tl₀ tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (hs : tl₀.shapeF m txOf f hasU tau = .ok tl) {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (ha : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T'))
    {tlc : HTailF2} (hr : tlc.heard = tl'.heard) : tlc.heard = none := by
  rw [hr, addTreesF_heard ha]
  exact shapeF_heard hs

/-! ### the three plans -/

theorem planG_heard (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : hp.tl.heard = none := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain rfl := pureE_ok hy
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact heard_made hS hA (ownerIs_heard tl1 g)
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      exact heard_made hS hA ((borderMeans_heard hB).trans (ownerIs_heard tl1 g))
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

theorem planA_heard (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) : P.seam.tl.heard = none := by
  obtain ⟨seam0, h0, h1, -⟩ := BatRows.planA_rows0 settings i cf P e
  obtain ⟨tl₀, m1, txOf, f, hasU, hS⟩ := seamShape_cut h0
  obtain ⟨T, hA⟩ := seamPlan_cut h1
  exact heard_made hS hA rfl

theorem planH2_heard (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) : hp.tl.heard = none := by
  unfold Head.planH2 at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl, hS, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨⟨tl1, Fp, Tp⟩, hA, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hO, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    cases e
    exact heard_made hS hA (ownerHeld_heard hO)
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

/-! ### the owners' loop over the attention plans -/

theorem ownerPlace_heard {g : Nat} {O X X' : Verify.SubPlan}
    (h : Verify.attentionOwnerPlace g O X = .ok X') : X'.tl.heard = X.tl.heard := by
  unfold Verify.attentionOwnerPlace at h
  obtain ⟨tl, h1, h⟩ := bindE_ok h
  obtain ⟨own, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Except.ok.inj h
    exact borderMeans_heard h1

/-- What the loop keeps. -/
def HeardKept (A out : Array Verify.SubPlan) : Prop :=
  ∀ (i : Nat) (s : Verify.SubPlan), out[i]? = some s →
    ∃ s0, A[i]? = some s0 ∧ s.tl.heard = s0.tl.heard

theorem ownerPlaces_heard (G A : Array Verify.SubPlan) : ∀ (l : List Nat)
    (out r : Array Verify.SubPlan), HeardKept A out →
    l.foldlM (fun (out : Array Verify.SubPlan) g =>
      match G[g]?, out[g]? with
      | some O, some X => do pure (out.set! g (← Verify.attentionOwnerPlace g O X))
      | _, _ => throw "internal-a-owner-shape") out = .ok r → HeardKept A r
  | [], out, r, hk, h => by
    obtain rfl : out = r := Except.ok.inj h
    exact hk
  | g :: l, out, r, hk, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨out1, h1, h⟩ := bindE_ok h
    refine ownerPlaces_heard G A l out1 r ?_ h
    split at h1
    · rename_i O X hO hX
      obtain ⟨X', h2, h1⟩ := bindE_ok h1
      obtain rfl := Except.ok.inj h1
      intro i s hi
      by_cases hig : i = g
      · subst hig
        obtain ⟨s0, e0, a0⟩ := hk i X hX
        have hlt : i < out.size := by
          obtain ⟨hl, _⟩ := Array.getElem?_eq_some_iff.1 hX
          exact hl
        have e : (out.set! i X')[i]? = some X' := by
          simp [Array.set!, hlt]
        rw [e] at hi
        obtain rfl := Option.some.inj hi
        exact ⟨s0, e0, (ownerPlace_heard h2).trans a0⟩
      · have e : (out.set! g X')[i]? = out[i]? := by
          simp [Array.set!, Ne.symm hig]
        rw [e] at hi
        exact hk i s hi
    · cases h1

theorem owners_heard {p4 : Bool} {NGr : Nat} {G A r : Array Verify.SubPlan}
    (h : Verify.attentionOwners p4 NGr G A = .ok r) : HeardKept A r := by
  unfold Verify.attentionOwners at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    exact ownerPlaces_heard G A _ A r (fun i s hi => ⟨s, hi, rfl⟩) h
  · obtain rfl : A = r := Except.ok.inj h
    exact fun i s hi => ⟨s, hi, rfl⟩

/-! ### the members of X -/

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem public_G_heard (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) : hp.tl.heard = none :=
  planG_heard X.layers g _ hp (public_G h g hp hg)

theorem public_H_heard (h : Verify.publicOf pol KL layout = .ok X) : X.H.tl.heard = none := by
  obtain ⟨H0, h0, e⟩ := public_H h
  rw [e]
  exact planH2_heard _ _ _ _ _ _ _ H0 h0

theorem public_A_heard (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a) : a.seam.tl.heard = none := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := publicOf_cut pol KL layout X h
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  obtain ⟨s0, f1, f2⟩ := owners_heard k6 g s e2
  have f3 : s0 = ⟨a0.seam.tl, a0.seam.Fp, a0.seam.Tp⟩ := by
    unfold seenA0 at f1
    rw [Array.getElem?_map, e1] at f1
    exact (Option.some.inj f1).symm
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := config_at k9
    obtain ⟨cf, m1, m2⟩ := group_plan (l2 g a0 e1)
    subst e3
    show s.tl.heard = none
    rw [f3] at f2
    rw [f2]
    exact planA_heard _ _ _ a0 m2
  · simp at e1

/-- **The parameters of every approximate range proof in what publicOf returns have heard
nothing.** -/
theorem public_heard (h : Verify.publicOf pol KL layout = .ok X) :
    (∀ (g : ℕ) (hp : Layer.HPlan2), X.G[g]? = some hp → hp.tl.heard = none) ∧
    (∀ (g : ℕ) (a : Attention.Plan), X.A[g]? = some a → a.seam.tl.heard = none) ∧
    X.H.tl.heard = none :=
  ⟨public_G_heard h, public_A_heard h, public_H_heard h⟩

end

end Fo.ZPlan

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- The parameters of every approximate range proof in the public parameters have heard nothing. -/
def HeardNoneAll (X : Verify.Public) : Prop :=
  (∀ (g : ℕ) (hp : Layer.HPlan2), X.G[g]? = some hp → hp.tl.heard = none) ∧
  (∀ (g : ℕ) (a : Attention.Plan), X.A[g]? = some a → a.seam.tl.heard = none) ∧
  X.H.tl.heard = none

/-- It holds at whatever publicOf returns. -/
theorem heardNoneAll_of_public {pol KL : ByteArray} {layout : Option ByteArray}
    {X : Verify.Public} (h : Verify.publicOf pol KL layout = .ok X) : HeardNoneAll X :=
  _root_.Fo.ZPlan.public_heard h

/-- **At every link: what tlAt returns has heard nothing.** -/
theorem heard_none_at {X : Verify.Public} (Z : HeardNoneAll X) {i : ℕ} {tl : HTailF2}
    (h : tlAt X i = some tl) : tl.heard = none := by
  unfold tlAt at h
  cases hH : (i == (if X.p4 then 2 else 1) * X.NGr) with
  | true =>
    simp only [hH, ↓reduceIte] at h
    obtain rfl := Option.some.inj h
    exact Z.2.2
  | false =>
    cases hE : (i % (if X.p4 then 2 else 1) == 0) with
    | true =>
      simp only [hH, hE, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hp, hg, rfl⟩ := Option.map_eq_some_iff.1 h
      exact Z.1 _ hp hg
    | false =>
      simp only [hH, hE, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨a, hg, rfl⟩ := Option.map_eq_some_iff.1 h
      exact Z.2.1 _ a hg

end VerifiableInference.Desc.First.Look

#print axioms Fo.ZPlan.public_heard
#print axioms VerifiableInference.Desc.First.Look.heard_none_at
