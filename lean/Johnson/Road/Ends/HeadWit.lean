-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Ends/HeadWit.lean: the two premises with content of the seam before the output head's
lookup hold together of some matrices: the head's meaning without its clause on keys (HeadR0,
Johnson/Road/Lane5SplitH.lean) and the clause ForInH (Johnson/Road/Ends/HeadForIn.lean), at the
public part X that the verifier's function publicOf returns.

Main definitions and theorems:
  covReq x, runReq R0 x: a run's record R0 with the covered positions, the positions with a cost and
    the checked tokens of the request x laid in. covReq x is not what Head.coveredOf returns: three
    of its fields are blank; kvH reads none of the three. runReq has the request's checked token at
    uncovered positions too, where Head.winOf has 0: there kvH multiplies what it reads by 0
    (H.real).
  reqFits_runReq: ReqFits (Johnson/Road/HeadLines.lean) holds of runReq R0 x and x, for every x.
  headOrd_iff_forIn_test: headOrd_iff_forIn (Johnson/Road/Ends/HeadBack.lean) at X, under the test
    headPubB (Johnson/Road/Ends/HeadInSeamPub.lean), for every request x, every Wz and Mh.
  headForIn_met: some index i, some request x and some matrices Mh have HeadR0 and ForInH together,
    at Wz := i.mat.
  blankRun X, headForIn_met_blank: the same at a written record R0: X's shape, layout and plan, and
    nothing heard: so a record with the two equations exists.

WHICH WITNESS IT IS: that of ordsL_met_public (Johnson/Road/Lane5TopPub.lean): all weights and all
tokens 0, r = 1,023, e = 1,024: a request with no counted position; Mh are the matrices of the
library's honest trace, laid out by these files' dictionary (Hd.zOf, Johnson/Road/HeadZ.lean;
Hd.mzH, Johnson/Road/HeadDict.lean), whose labels are those of the verifier's plans; no function of
the verifier's makes them, and they are no prover's.

Limits: it shows that the two premises are not contradictory at the verifier's own shapes, and no
more. That the keys of a prover's cells lie in their tables is not shown. HeadR0 reads no weight:
the product with the output matrix stands in the clause ForInH (the head of
Johnson/Road/Ends/HeadInSeam.lean, "What the bridge holds"). How a field element is lifted to an
integer is not said. That the scale file's words are scalesKF (Johnson/Road/FormsKeysRunK.lean) is a
premise. Of R0 only the shape and the layout are read. Nothing on a form or a protocol.

-/
import Johnson.Road.Lane5TopPub
import Johnson.Road.Ends.HeadInSeamPub
import Johnson.Road.Ends.HeadBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model.Verify (Public publicOf borderOf weightShape)
open Inst.Model (Mat ppref AcceptancePolicy Instance)
open Inst.Model.Layout (kRef)

/-- The covered positions and the positions with a cost of a request. -/
def covReq (x : Instance ppref) : Model.Head.Covered where
  tokv := #[]
  hOn := (Array.range 1024).map fun t => decide (x.r ≤ t ∧ t < x.e)
  hWin := #[]
  hOnC := (Array.range 1024).map fun t => decide (x.r ≤ t ∧ t < min x.e 1023)
  hRC := 0

/-- A run's record with the request's positions and checked tokens laid in. -/
def runReq (R0 : Model.Head.Run) (x : Instance ppref) : Model.Head.Run :=
  { R0 with cov := covReq x, x := { R0.x with win := (Array.range 1024).map x.w } }

/-- The record of the request holds of it. -/
theorem reqFits_runReq (R0 : Model.Head.Run) (pol : AcceptancePolicy) (x : Instance ppref) :
    ReqFits (runReq R0 x) HeadSizes.ref (Inst.Model.Head.Req.of pol x) where
  rho := fun i hi => by
    have e : (runReq R0 x).cov.hOn.getD i false = decide (x.r ≤ i ∧ i < x.e) :=
      getD_map_rangeT _ 1024 i false hi
    rw [e]
    show (if x.r ≤ i ∧ i < x.e then (1 : ℤ) else 0) = _
    by_cases h : x.r ≤ i ∧ i < x.e <;> simp [h]
  rhoC := fun i hi => by
    have e : (runReq R0 x).cov.hOnC.getD i false = decide (x.r ≤ i ∧ i < min x.e 1023) :=
      getD_map_rangeT _ 1024 i false hi
    rw [e]
    show (if x.r ≤ i ∧ i < min x.e 1023 then (1 : ℤ) else 0) = _
    by_cases h : x.r ≤ i ∧ i < min x.e 1023 <;> simp [h]
  win := fun i hi _ => (getD_map_rangeT x.w 1024 i 0 hi).symm

section At

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}

/-- **The head is in order if and only if its meaning without the clause on keys and the clause
ForInH hold**, at one record and one test, for every request. -/
theorem headOrd_iff_forIn_test (h : publicOf pol KL lay = .ok X) (t : headPubB X = true)
    {R0 : Model.Head.Run} (e1 : R0.h = X.hS) (e2 : R0.L = X.HLy) (pl : AcceptancePolicy) (x : Instance ppref)
    (Wz : Mat) (Mh : Mats ℤ) :
    HeadOrdLB X.hS X.HLy X.y (npOf X.hS) pl Wz x Mh ↔
      L5.HeadR0 X.hS X.HLy X.y (npOf X.hS) pl x Mh ∧
        ForInH (runReq R0 x) (callsH (runReq R0 x) (borderOf X.y) X.layers.wsLay Mh Wz).K := by
  simp only [headPubB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at t
  obtain ⟨⟨⟨⟨⟨A, hF⟩, ⟨⟨⟨⟨⟨⟨⟨⟨z1, z2⟩, z3⟩, z4⟩, z5⟩, z6⟩, z7⟩, z8⟩, z9⟩⟩, hp3⟩, hlk⟩, hnl⟩ := t
  have B := public_of_publicOf h A
  have hws := (publicH_of_public h).ws
  rw [hp3, hlk] at hws
  have f1 : (runReq R0 x).h = X.hS := e1
  have f2 : (runReq R0 x).L = X.HLy := e2
  have hy : Model.Head.layout (runReq R0 x).h tauFCw = .ok (runReq R0 x).L := by
    rw [f1, f2, ← tauFC_of_layout B.lay]
    exact B.head
  have key := headOrd_iff_forIn (R := runReq R0 x) hy (by rw [f1]; exact B.full)
    (by rw [f1]; exact hF) (by rw [f1]; exact B.sT) (by rw [f1]; exact B.sh) (np := npOf X.hS)
    (by rw [f1]; rfl) (y := X.y) hnl
    (⟨z1, z2, z3, z4, z5, z6, z7, z8, z9⟩ : SizedW (weightShape X.P X.y) ppref) hws
    (reqFits_runReq R0 pl x) Wz Mh
  rw [f1, f2] at key
  exact key

/-- **The two premises hold together of some matrices.** -/
theorem headForIn_met (h : publicOf pol KL lay = .ok X) (t : headPubB X = true)
    (hW : Model.fileWords KL = scalesKF.toArray) {pl : AcceptancePolicy} (hpol : Policy.PolCond pl)
    {R0 : Model.Head.Run} (e1 : R0.h = X.hS) (e2 : R0.L = X.HLy) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (Mh : Mats ℤ), x.r = 1023 ∧ x.e = 1024 ∧
      L5.HeadR0 X.hS X.HLy X.y (npOf X.hS) pl x Mh ∧
        ForInH (runReq R0 x)
          (callsH (runReq R0 x) (borderOf X.y) X.layers.wsLay Mh i.mat).K := by
  have A : PublicAt X.P := by
    simp only [headPubB, Bool.and_eq_true, decide_eq_true_eq] at t
    exact t.1.1.1.1.1
  obtain ⟨i, x, Z, ZA, hr, he, O⟩ := L5.ordsL_met_public h A hW hpol
  exact ⟨i, x, _, hr, he, (headOrd_iff_forIn_test h t e1 e2 pl x i.mat _).1 O.head⟩

/-- A run's record with the shape, the layout and the plan of X, and nothing heard. -/
def blankRun (X : Public) : Model.Head.Run where
  h := X.hS
  L := X.HLy
  b := borderOf X.y
  hp := X.H
  cov := default
  x := { win := #[],
         g1 := { shape := X.HLy.fs, leaves := {}, zx := #[], zy := #[], zk := #[], zb0 := #[],
                 zb1 := #[] },
         Zl := #[], PV := #[], sW := 0, gp := #[], wpl := default, sPv := 0, omV := #[], tV := {},
         tN := {}, tH := {}, rs := #[], qN := 0, qH := 0 }
  t := {}
  iU3 := 0

/-- **The same at a written record**: so the statement is about something. -/
theorem headForIn_met_blank (h : publicOf pol KL lay = .ok X) (t : headPubB X = true)
    (hW : Model.fileWords KL = scalesKF.toArray) {pl : AcceptancePolicy} (hpol : Policy.PolCond pl) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (Mh : Mats ℤ), x.r = 1023 ∧ x.e = 1024 ∧
      L5.HeadR0 X.hS X.HLy X.y (npOf X.hS) pl x Mh ∧
        ForInH (runReq (blankRun X) x)
          (callsH (runReq (blankRun X) x) (borderOf X.y) X.layers.wsLay Mh i.mat).K :=
  headForIn_met h t hW hpol (R0 := blankRun X) rfl rfl

end At

end OnBytes.Road.Hd

#print axioms OnBytes.Road.Hd.reqFits_runReq
#print axioms OnBytes.Road.Hd.headOrd_iff_forIn_test
#print axioms OnBytes.Road.Hd.headForIn_met
#print axioms OnBytes.Road.Hd.headForIn_met_blank
