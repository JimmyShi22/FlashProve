-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/LookInByMake.lean: THE NAMED TEST lookIn OF K4's ROW (lookInPlanB,
Johnson/Road/K4/Riders/LookInPlanB.lean) IS A THEOREM, BY THE MAKE OF THE PUBLIC PARAMETERS: it
accepts wherever publicOf returns X, at profile 4, at each group g below X.NGr, at a structure of
K4's parameters par whose P is X's layers (any tokens), whose group is g and whose list of numbers
is X.G[g]. Four statements with their proofs. NO NUMERAL OF THE SCOPE IS READ.

  `planG_slots`: what planG returns has lamS := lamSOf y, NCL := nclOf y g, and its number of slots
    is slotsOf at the number of elements of ITS OWN approximate range proof's lookup's shape (f9
    is kept by addTrees, ownerIs, borderMeans: SameP). Premise: planG returns.
  `slots_add`: slotsOf is its value at 0 and the last argument.
  `lookAt_dig`: the place of a layers' segment's lookup on the digits is there, with the range
    proof's two calls, its padding numbers, its cap; its first slot is ns - 0 - elems f9.
    Premises: i is a layers' segment's number, X.G has hp there, elems f9 ≤ ns.
  **`lookIn_public`**: the test accepts at n := Forest.elems X.y.fo and ns := par.hp.ns. Premises:
    h (publicOf returns X) · k4 (X.p4 = true) · hg (g < X.NGr) · hP · eg · hG (par's three lines:
    K4Here's fields P, hg, G have them at an opening). WHO PAYS: the head's field pubOne |
    Meaning.scope_plans | K4Here.
By: Hd.public_plans, Fo.Pub.plansFrom_at, Fo.ZPlan.public_shapeZ, shape_of_made, and the converse
lookInPlanB_of. The walk through planG is that of Fo.ZPlan.planG_u.
CAN IT BE EMPTY? Its premises are met wherever K4Here is (a theorem in scope at an opening:
IM.k4_of). The test itself was evaluated true x12 at the full size, n + 1 rejecting (a sheet).
Limits. A test on public data: at no meaning. K04_law, the law of K4's sub-protocol itself, IS NOT
PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.Riders.LookInPlanB
import Johnson.Desc.First.Look.K3CallerCellsLaw
import Johnson.Desc.First.Look.K3PlaceAt
import Johnson.Road.HeadDict
import OnBytes.Tie.Pv.Lookup.Ends.FoShapeZ
import OnBytes.Tie.Pv.Lookup.Ends.FoPublic
import OnBytes.Tie.Pv.Lookup.Ends.FoZMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (lamSOf nclOf slotsOf)
open OnBytes.Desc.First.K4 (Par)
open Fo (pureE_ok SameP)
open Fo.ZPlan (addTreesF_sameP ownerIs_sameP borderMeans_sameP public_shapeZ)
open Fo.BatRows (bindE_ok)
open VerifiableInference.Desc.First.Look (lookAt placeAt placeAt_iff digitsNext shape_of_made)

/-- **Three numbers of a layers' plan, by its make.** -/
theorem planG_slots (P : Layer.Pub) (g : ℕ) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) :
    hp.lamS = lamSOf P.y ∧ hp.NCL = nclOf P.y g ∧
      hp.ns = slotsOf P.y P.rd g P.wsLay.lk (Forest.elems hp.tl.f9) := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have N1 : SameP tl tl1 := addTreesF_sameP hA
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain rfl := pureE_ok hy
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    refine ⟨rfl, rfl, ?_⟩
    show slotsOf P.y P.rd g P.wsLay.lk (Forest.elems tl.f9) =
      slotsOf P.y P.rd g P.wsLay.lk (Forest.elems (tl1.ownerIs g).f9)
    rw [(N1.trans (ownerIs_sameP tl1 g)).f9]
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      refine ⟨rfl, rfl, ?_⟩
      rw [((N1.trans (ownerIs_sameP tl1 g)).trans (borderMeans_sameP hB)).f9]
      rfl
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

/-- slotsOf is its value at 0 and the last argument. -/
theorem slots_add (y : Layer.Lay) (rd : Layer.Reads) (g lk e : ℕ) :
    slotsOf y rd g lk e = slotsOf y rd g lk 0 + e := by
  simp only [slotsOf, Nat.add_zero]

/-- **The place of a layers' segment's lookup on the digits.** -/
theorem lookAt_dig {X : Verify.Public} {i : ℕ} {hp : Layer.HPlan2}
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) = 0)
    (hg : X.G[i / (if X.p4 then 2 else 1)]? = some hp) (hr : Forest.elems hp.tl.f9 ≤ hp.ns) :
    ∃ x, lookAt X i true = some x ∧ x.calls = #[hp.tl.z1.call, hp.tl.z2.call] ∧
      x.pub = hp.tl.f9.pub ∧ x.lid = hp.tl.lidb ∧
      x.F.next = hp.ns - 0 - Forest.elems hp.tl.f9 := by
  have hd : digitsNext hp.ns 0 (Forest.elems hp.tl.f9) =
      some (hp.ns - 0 - Forest.elems hp.tl.f9) := by
    unfold digitsNext
    rw [if_pos (by rw [Nat.zero_add]; exact hr)]
  unfold lookAt
  dsimp only
  rw [if_neg (by simpa using hn), if_pos (by simpa using h0), hg]
  show ∃ x, Option.map _ (digitsNext hp.ns 0 (Forest.elems hp.tl.f9)) = some x ∧ _
  rw [hd]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- **THE TEST lookIn ACCEPTS, BY THE MAKE OF THE PUBLIC PARAMETERS.** -/
theorem lookIn_public {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) (k4 : X.p4 = true) {g : ℕ} (hg : g < X.NGr)
    {par : Par} {tk : Array ℕ} (hP : par.P = { X.layers with tokv := tk }) (eg : par.g = g)
    (hG : X.G[g]? = some par.hp) :
    lookInPlanB par X (2 * g) (Forest.elems X.y.fo) par.hp.ns = true := by
  obtain ⟨sc, rope, wsLay, V, tokv, set, -, hPl⟩ := OnBytes.Road.Hd.public_plans h
  unfold Layer.plansG at hPl
  obtain ⟨l, hl, e⟩ := bindE_ok hPl
  have eG : l.toArray = X.G := Except.ok.inj e
  have hl' : l[g]? = some par.hp := by
    rw [← eG] at hG
    simpa using hG
  have hp0 := Fo.Pub.plansFrom_at X.layers _ 0 none l hl g par.hp hl'
  rw [Nat.zero_add] at hp0
  obtain ⟨e1, e2, e3⟩ := planG_slots _ _ _ _ hp0
  have e3' : par.hp.ns = slotsOf X.layers.y X.layers.rd g X.layers.wsLay.lk 0 +
      Forest.elems par.hp.tl.f9 := e3.trans (slots_add _ _ _ _ _)
  have hr : Forest.elems par.hp.tl.f9 ≤ par.hp.ns := by
    rw [e3']
    exact Nat.le_add_left _ _
  have hn : 2 * g ≠ (if X.p4 then 2 else 1) * X.NGr := by
    rw [k4, if_pos rfl]
    omega
  have h0 : 2 * g % (if X.p4 then 2 else 1) = 0 := by
    rw [k4, if_pos rfl]
    exact Nat.mul_mod_right 2 g
  have hd : 2 * g / (if X.p4 then 2 else 1) = g := by
    rw [k4, if_pos rfl]
    exact Nat.mul_div_cancel_left g (by decide : 0 < 2)
  obtain ⟨x, ex, c1, c2, c3, c4⟩ := lookAt_dig hn h0 (by rw [hd]; exact hG) hr
  have ef : x.F.next = slotsOf X.layers.y X.layers.rd g X.layers.wsLay.lk 0 := by
    rw [c4, Nat.sub_zero, e3', Nat.add_sub_cancel]
  refine lookInPlanB_of
    (p := VerifiableInference.Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x)
    (h3 := par.hp.tl.f9)
    { place := placeAt_iff.2 ⟨x, ex, rfl⟩
      shape := ?_
      digits := rfl
      lamS := ?_
      ncl := ?_
      count := ?_
      room := ?_ }
  · refine shape_of_made ?_
    show _root_.Fo.ShapeOf x.calls x.pub x.lid par.hp.tl.f9
    rw [c1, c2, c3]
    exact (public_shapeZ h).1 g par.hp hG
  · rw [hP]
    exact e1
  · rw [hP, eg]
    exact e2
  · rw [hP, eg]
    show Forest.elems X.layers.y.fo + slotsOf X.layers.y X.layers.rd g X.layers.wsLay.lk 0 =
      x.F.next + Forest.elems X.layers.y.fo
    rw [ef]
    exact Nat.add_comm _ _
  · show x.F.next + Forest.elems par.hp.tl.f9 ≤ par.hp.ns
    rw [ef, e3']

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.planG_slots
#print axioms OnBytes.Road.K4.Riders.slots_add
#print axioms OnBytes.Road.K4.Riders.lookAt_dig
#print axioms OnBytes.Road.K4.Riders.lookIn_public
