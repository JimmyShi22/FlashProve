-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoMadePub.lean.
The public half of MadeH, at the record that the byte-level verifier runs the head's check with.

MadeH (OnBytes/Tie/Pv/Lookup/Ends/FoKeysH.lean) says that the record of a run of the output head's
check is made as the check makes it. Four of its clauses speak of public numbers alone. The verifier
runs the head's check at X.hS, X.HLy, Verify.borderOf X.y, X.H and cov, where X is what
Verify.publicOf returns and cov what Head.coveredOf returns at X.T and X.P.h.V (so read
Verify.headPlanOf, Verify.requestRun and Verify.lean; no statement of this file says it). This file
gets the four clauses there.

* layoutBase_T, layout_T: the layers' layout keeps its shape, and its number of positions is 2^lt.
* polLayout_T: so X's number of positions is the head's shape's.
* publicOf_headLayout: Head.layout X.hS X.layers.y.tauFC = .ok X.HLy.
* public_T, public_V: X.T = X.hS.T and X.P.h.V = X.hS.V.
* public_mats: X.H's list of matrices is Head.matsH's, at numbers that are named, and is counted.
* madeH_public: the four clauses together.
* madeH_at: with made_of_run (OnBytes/Tie/Pv/Lookup/Ends/FoMadeH.lean): from the run equations of
  Head.hear, on a view, and of Head.tablesOf, at these public numbers: MadeH of the record.
Premises of madeH_public and madeH_at: Verify.publicOf returned X; Head.coveredOf returned cov at
X.T and X.P.h.V.
Not shown here: that the head's check runs Head.hear and Head.tablesOf at these arguments, from
which states (h_run_tied, OnBytes/Tie/Pv/Lookup/Ends/FoTiedH.lean, has that); that the context is a
view there, and that the X and the cov of a call of the verifier are these (passed_head,
OnBytes/Tie/Pv/Lookup/Ends/FoPassedHead.lean, has both of a passing call).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPublic
import OnBytes.Tie.Pv.Lookup.Ends.FoPlanH
import OnBytes.Tie.Pv.Lookup.Ends.FoMadeH

set_option autoImplicit false

namespace Fo.Pub
open OnBytes OnBytes.Model Fo.BatRows

theorem layoutBase_T (S : Layer.Shape) (pc : List (List String)) (y : Layer.Lay)
    (e : Layer.layoutBase S pc = .ok y) : y.T = 2 ^ S.lt ∧ y.h = S := by
  unfold Layer.layoutBase at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  obtain rfl := Except.ok.inj e
  exact ⟨rfl, rfl⟩

theorem layout_T (S : Layer.Shape) (pc : List (List String)) (y : Layer.Lay)
    (e : Layer.layout S pc = .ok y) : y.T = 2 ^ S.lt ∧ y.h = S := by
  unfold Layer.layout at e
  obtain ⟨y0, h0, e⟩ := bindE_ok e
  obtain ⟨a1, a2⟩ := layoutBase_T S pc y0 h0
  unfold Layer.layoutLook at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  obtain rfl := Except.ok.inj e
  exact ⟨a1, a2⟩

theorem polLayout_T (pol : ByteArray) (P : PolScan) (y : Layer.Lay)
    (e : Verify.polLayout pol = .ok (P, y)) : y.T = 2 ^ P.h.lt := by
  unfold Verify.polLayout at e
  obtain ⟨P0, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨y0, h0, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e)
  exact (layout_T _ _ _ h0).1

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

/-- The head's layout in X is what Head.layout returns. -/
theorem publicOf_headLayout (h : Verify.publicOf pol KL layout = .ok X) :
    Head.layout X.hS X.layers.y.tauFC = .ok X.HLy := by
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
  obtain ⟨HLy, kL, h⟩ := bindE_ok h
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
  exact kL

theorem public_T (h : Verify.publicOf pol KL layout = .ok X) : X.T = X.hS.T := by
  obtain ⟨k1, k2, _⟩ := publicOf_cut pol KL layout X h
  show X.layers.y.T = 2 ^ X.hS.lt
  rw [polLayout_T pol X.P X.layers.y k1, k2]
  rfl

theorem public_V (h : Verify.publicOf pol KL layout = .ok X) : X.P.h.V = X.hS.V := by
  rw [(publicOf_cut pol KL layout X h).2.1]
  rfl

/-- The list of matrices in X.H. -/
theorem public_mats (h : Verify.publicOf pol KL layout = .ok X) :
    ∃ stream, X.owner.tl.mats[X.owner.iXO]? = some stream ∧
      X.H.tl.mats = Head.matsH X.hS X.HLy (Verify.borderOf X.layers.y) (1 + X.layers.y.NGr)
        stream.aId ∧
      X.H.tl.NM = X.H.tl.mats.size := by
  obtain ⟨H0, h1, h2⟩ := public_H h
  obtain ⟨stream, a1, a2, a3⟩ := planH2_mats _ _ _ _ _ _ _ H0 h1
  rw [h2]
  exact ⟨stream, a1, a2, a3⟩

/-- The four public clauses of MadeH at the verifier's own record. -/
theorem madeH_public (h : Verify.publicOf pol KL layout = .ok X) (so : Head.StOwn)
    (cov : Head.Covered) (hc : Head.coveredOf so X.T X.P.h.V = .ok cov) :
    (∃ tau, Head.layout X.hS tau = .ok X.HLy) ∧
    (∃ so, Head.coveredOf so X.hS.T X.hS.V = .ok cov) ∧
    (∃ gid sid, X.H.tl.mats = Head.matsH X.hS X.HLy (Verify.borderOf X.y) gid sid) ∧
    X.H.tl.NM = X.H.tl.mats.size := by
  obtain ⟨stream, _, a2, a3⟩ := public_mats h
  refine ⟨⟨_, publicOf_headLayout h⟩, ⟨so, ?_⟩, ⟨_, _, a2⟩, a3⟩
  rw [← public_T h, ← public_V h]
  exact hc

/-- MadeH of the record, from the two run equations at the verifier's own public numbers. -/
theorem madeH_at (h : Verify.publicOf pol KL layout = .ok X) (so : Head.StOwn)
    (cov : Head.Covered) (hc : Head.coveredOf so X.T X.P.h.V = .ok cov) (plain : Array E)
    (iU3 : Nat) (F G : Fork) (c c' : Ctx) (x : Head.Heard) (hd : c.ch.dry = false)
    (hr : Head.hear X.hS X.HLy X.H cov plain F c = .ok ((x, G), c'))
    (F2 F3 : Fork) (c2 c3 : Ctx) (t : Head.Tables)
    (ht : Head.tablesOf X.hS X.HLy X.H cov x F2 c2 = .ok ((t, F3), c3)) :
    MadeH { h := X.hS, L := X.HLy, b := Verify.borderOf X.y, hp := X.H, cov := cov, x := x, t := t,
            iU3 := iU3 } := by
  obtain ⟨a1, a2, a3, a4⟩ := madeH_public h so cov hc
  exact made_of_run _ _ _ _ _ plain iU3 F G c c' x hd hr F2 F3 c2 c3 t ht a1 a2 a3 a4

end
end Fo.Pub
