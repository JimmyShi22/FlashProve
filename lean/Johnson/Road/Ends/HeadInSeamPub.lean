-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Ends/HeadInSeamPub.lean: the public premises of the bridge at the output head
(headBridge_of_layout, Johnson/Road/Ends/HeadInSeam.lean) at ONE record: the public part X that the
verifier's own function publicOf returns on the parameter file and the scale file; and as ONE test
that a program can run, with its theorem: if the test says true, the premises hold.

Main definitions and theorems:
  headPubB X: the test: the 46 numbers and two switches of PublicAt (Johnson/Road/HeadL5Pub.lean);
    F = 24; the nine numbers of the shape of the weights are the reference's (SizedW); the switch
    p3; the number of column bits is the library's; the stream has five limbs.
  headBridge_of_test: publicOf has returned X, the test says true, R is a run's record with the
    head's shape and layout of X, and ReqFits holds of R and the request: then HeadBridge at X's own
    letters, at the final normalisation npOf X.hS and the layout of the weights X.layers.wsLay.

Limits: those of Johnson/Road/Ends/HeadInSeam.lean. ReqFits stays a premise: it speaks of a request;
no run builds an R. The bridge stands at the final normalisation npOf X.hS: a user that wants it at
the final normalisation s.nf of a table of scales s owes npOf X.hS = s.nf (at s := scalesAt X,
Johnson/Flat/ScalesAt.lean, it holds by definition). A verifier takes other parameter files than
those that pass the test (other sizes; another F): of these this file says nothing.

-/
import Johnson.Road.HeadL5Pub
import Johnson.Road.HeadMade
import Johnson.Road.Ends.HeadInSeam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model.Verify (Public publicOf borderOf weightShape)
open Inst.Model (Mat ppref AcceptancePolicy Instance)
open Inst.Model.Layout (kRef)

/-- The public premises of the bridge at the head, as one test. -/
def headPubB (X : Public) : Bool :=
  decide (PublicAt X.P) && X.hS.famF == 24 &&
    ((weightShape X.P X.y).L == ppref.layers && (weightShape X.P X.y).d == ppref.d &&
      (weightShape X.P X.y).dh == ppref.ch && (weightShape X.P X.y).dq == ppref.nq * ppref.ch &&
      (weightShape X.P X.y).dkv == ppref.nkv * ppref.ch && (weightShape X.P X.y).f == ppref.f &&
      (weightShape X.P X.y).fe == ppref.fe && (weightShape X.P X.y).NE == ppref.nexp &&
      (weightShape X.P X.y).V == ppref.V) &&
    X.y.h.p3 && X.P.lkW == kRef && (borderOf X.y).nl == 5

/-- **The bridge at the head, at one record and one test.** -/
theorem headBridge_of_test {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOf pol KL lay = .ok X) (t : headPubB X = true) {R : Model.Head.Run}
    (e1 : R.h = X.hS) (e2 : R.L = X.HLy) {pl : AcceptancePolicy} {x : Instance ppref}
    (Rq : ReqFits R HeadSizes.ref (Inst.Model.Head.Req.of pl x)) (Wz : Mat) (Mh : Mats ℤ) :
    L5.HeadBridge X.hS X.HLy X.y (npOf X.hS) pl Wz x Mh
      (callsH R (borderOf X.y) X.layers.wsLay Mh Wz) := by
  simp only [headPubB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at t
  obtain ⟨⟨⟨⟨⟨A, hF⟩, ⟨⟨⟨⟨⟨⟨⟨⟨z1, z2⟩, z3⟩, z4⟩, z5⟩, z6⟩, z7⟩, z8⟩, z9⟩⟩, hp3⟩, hlk⟩, hnl⟩ := t
  have B := public_of_publicOf h A
  have hws := (publicH_of_public h).ws
  rw [hp3, hlk] at hws
  have hy : Model.Head.layout R.h tauFCw = .ok R.L := by
    rw [e1, e2, ← tauFC_of_layout B.lay]
    exact B.head
  have key := headBridge_of_layout (R := R) hy (by rw [e1]; exact B.full) (by rw [e1]; exact hF)
    (by rw [e1]; exact B.sT) (by rw [e1]; exact B.sh) (np := npOf X.hS) (by rw [e1]; rfl)
    (y := X.y) hnl (⟨z1, z2, z3, z4, z5, z6, z7, z8, z9⟩ : SizedW (weightShape X.P X.y) ppref) hws
    Rq Wz Mh
  rw [e1, e2] at key
  exact key

end OnBytes.Road.Hd

#print axioms OnBytes.Road.Hd.headBridge_of_test
