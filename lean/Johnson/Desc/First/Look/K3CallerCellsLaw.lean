-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerCellsLaw.lean: THE TEST «THE PLANES' CELLS LIE IN THE LIST's MATRIX»
(Johnson/Desc/First/Look/K3CallerCellsIn.lean: planesAtB) SAYS YES AT EVERY RECORD THAT
Verify.publicOf RETURNS, at the lookups on the calls of all three sorts of link; and there the
record of the lookup is made of the calls by the kind's own parameters. Statements and proofs: each
is the library's own theorems, put together. NO SOUNDNESS IS CLAIMED.

Why. A closed caller reads a cell of the planes' matrix that the list has not as 0. planesAtB shuts
that. It need be no test of a running text: the library shows of every record that publicOf returns
that the planes' matrix has the rows of one block of its tables and the planes' columns or more
(OnBytes/Tie/Pv/Lookup/Ends/FoPlaneMatPub.lean, FoPlaneMatPubG.lean), that the record's number of
matrices is its list's length (FoPublicNM.lean), and the two bounds on the planes' packing (the
records LookPubOK of FoLookPubA.lean, FoLookPubH.lean, FoLookPubGX0.lean).

Main names:
  `planesAtB_of_nums`: arithmetic: the two bounds, NM = the list's length, «rows / 2 ^ lm = 1» and
    «planeCols ≤ columns» give planesAtB.
  `planesAtB_lay | planesAtB_att | planesAtB_head`: so planesAtB holds at every group's plan, every
    attention plan and the head's plan of such a record, at the plan's own record of the smallness
    test, shape of the lookup, lm and number of the planes' matrix.
  `shape_of_made`: where the library's ShapeOf holds, the kind's parameters make that very record.
  `made_lay | made_att | made_head`: ShapeOf at the three plans' own calls, padding numbers and cap.

Limits. One direction: from publicOf's equation. Nothing on the lookup's mask entries (masksAtB).
Nothing on the cells that the keys read. That matrix iB is the planes' matrix of the programs is
here the library's word too: its tests name the same number.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerCellsIn
import Johnson.Desc.First.Look.LookKindAgrees
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicNM
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPub
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPubGX0
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPubH

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- Arithmetic: from the library's numbers to the test. -/
theorem planesAtB_of_nums {tl : HTailF2} {fs : Forest.Shape} {lm iB : ℕ} (h5 : 5 ≤ lm)
    (hlm : lm ≤ fs.kT + 5) (hN : tl.NM = tl.mats.size)
    (h1 : (tl.mats.getD iB {}).m / 2 ^ lm = 1)
    (h2 : _root_.Fo.planeCols fs lm ≤ (tl.mats.getD iB {}).k) :
    planesAtB tl fs lm iB = true := by
  have hp : 0 < 2 ^ lm := Nat.two_pow_pos lm
  have hm : 2 ^ lm ≤ (tl.mats.getD iB {}).m := by
    have a := Nat.div_add_mod (tl.mats.getD iB {}).m (2 ^ lm)
    rw [h1, Nat.mul_one] at a
    omega
  have hi : iB < tl.NM := by
    rw [hN]
    by_contra hn
    have e : tl.mats.getD iB {} = {} := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl
    rw [e] at hm
    have hm' : 2 ^ lm ≤ 0 := hm
    omega
  exact planesAtB_iff.2 ⟨h5, hlm, hi, hm, h2⟩

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

/-- **At every group of layers' plan.** -/
theorem planesAtB_lay (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) :
    planesAtB hp.tl X.layers.y.fo X.layers.y.h.lmb (Layer.matIx X.layers.y).iB = true := by
  have k := _root_.Fo.Pub2.lookPubGX_ok0 (M₀ := Unit) (fun _ _ => 0) h g hp hg 0 0 0 0 0 Unit
  have p := _root_.Fo.PlaneMatG.public_planeMatB h g hp hg
  simp only [_root_.Fo.planeMatB, Bool.and_eq_true, decide_eq_true_eq] at p
  exact planesAtB_of_nums k.lm5 k.lmT (_root_.Fo.PubNM.public_G_NM h g hp hg) p.1.2 p.2

/-- **At every attention plan.** -/
theorem planesAtB_att (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (a : Attention.Plan)
    (hg : X.A[g]? = some a) :
    planesAtB a.seam.tl a.fs a.S.cf.lmb (a.S.cf.NAs + 2) = true := by
  have k := _root_.Fo.Pub2.lookPubA_ok (M₀ := Unit) (fun _ _ => 0) h g a hg 0 0 Unit
  have p := _root_.Fo.PlaneMat.public_planeMatAB h g a hg
  simp only [_root_.Fo.planeMatAB, Bool.and_eq_true, decide_eq_true_eq] at p
  exact planesAtB_of_nums k.lm5 k.lmT (_root_.Fo.PubNM.public_A_NM h g a hg) p.1.2 p.2

/-- **At the head's plan.** -/
theorem planesAtB_head (h : Verify.publicOf pol KL layout = .ok X) :
    planesAtB X.H.tl X.HLy.fs X.hS.lmbH (X.hS.NHf + 2) = true := by
  obtain ⟨_, s2, s3⟩ := _root_.Fo.Pub2.shapeOf_headLayout (_root_.Fo.Pub.publicOf_headLayout h)
  have p := _root_.Fo.PlaneMat.public_planeMatHB h
  simp only [_root_.Fo.planeMatHB, Bool.and_eq_true, decide_eq_true_eq] at p
  rw [show X.hS.NHf + 2 = X.hS.NHf + 1 + 1 from rfl]
  exact planesAtB_of_nums s2 s3 (_root_.Fo.PubNM.public_H_NM h) p.1.2 p.2

/-- The library's ShapeOf at a group's lookup. -/
theorem made_lay (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) :
    _root_.Fo.ShapeOf X.layers.y.cl X.layers.y.fo.pub X.layers.y.h.lidb X.layers.y.fo :=
  (_root_.Fo.Pub2.lookPubGX_ok0 (M₀ := Unit) (fun _ _ => 0) h g hp hg 0 0 0 0 0 Unit).shape

/-- At an attention plan's. -/
theorem made_att (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (a : Attention.Plan)
    (hg : X.A[g]? = some a) :
    _root_.Fo.ShapeOf (a.S.calls.map (·.call)) a.fs.pub a.lid a.fs :=
  (_root_.Fo.Pub2.lookPubA_ok (M₀ := Unit) (fun _ _ => 0) h g a hg 0 0 Unit).shape

/-- At the head's. -/
theorem made_head (h : Verify.publicOf pol KL layout = .ok X) :
    _root_.Fo.ShapeOf X.HLy.cl X.HLy.fs.pub X.hS.LIDB X.HLy.fs :=
  (_root_.Fo.Pub2.shapeOf_headLayout (_root_.Fo.Pub.publicOf_headLayout h)).1

end

/-- **Where ShapeOf holds, the kind's own parameters make that very record.** -/
theorem shape_of_made {p : P} {fs : Forest.Shape}
    (m : _root_.Fo.ShapeOf p.calls p.pub p.lid fs) : p.shape = some fs := by
  obtain ⟨h0, e1, e2, e3⟩ := m
  rw [P.shape_older, e1]
  simp only [e2, Except.toBool, if_true, e3]

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.planesAtB_of_nums
#print axioms VerifiableInference.Desc.First.Look.planesAtB_lay
#print axioms VerifiableInference.Desc.First.Look.planesAtB_att
#print axioms VerifiableInference.Desc.First.Look.planesAtB_head
#print axioms VerifiableInference.Desc.First.Look.made_lay
#print axioms VerifiableInference.Desc.First.Look.made_att
#print axioms VerifiableInference.Desc.First.Look.made_head
#print axioms VerifiableInference.Desc.First.Look.shape_of_made
