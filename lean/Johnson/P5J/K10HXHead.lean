-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K10HXHead.lean (kind K10): THE FIELD hX OF `K10Heavy`
(Johnson/Desc/First/Close/Law/K10Heavy.lean) AT THE CLOSED CONSTANT's LETTERS, AT ALL 25 LINKS,
FROM THE HEAD: THE PREMISES FoldFacts AND hLd OF K10SeatsAt.lean AND K10SeatsFive.lean FALL.
Theorems: two calls each.

By: atMgR_rch_of_head (Johnson/P5J/StartAtHead.lean): from the head alone there is
a list L with AtMgR .. h.toAtMg.rch (fun a => a.1) L, whose field fold is FoldFacts at At.foldD Zp
cF L and whose field listed says that L is what the plan's sendings lay (At.laid? Zp = some L: by
definition laidAtCodes at the constant's codes and the first chain's sendings).

What is said.
  `AtMgA.hX_head`: **hX at l < 25, at the written lists** (lo := loAt l, seat := seatK10 .., no :=
    noK10 ..): spent at l = 1 .. 24.
  `AtMgA.hX_five_head`: **hX at link 0, at the five-list** (lo := loFive, seat := seatFiveAt .., no
    := noFiveAt ..).

PREMISES THAT ARE LEFT. h : AtMgA OnBytes.secondHashFunction .. (THE HEAD) · hp : the place at K10's number of
the constant's list · hM, hZ: the typed group's own two (at link 0 also at the six-list: hM₆, hZ₆).
NO PREMISE ON ANY STATE.

Limits. THE HEAD IS A PREMISE: whether it can be met at the release's own files is not shown here.
At the second hash function alone. The head's "verify() accepts" stands with the entry tests that
the sealed version carries. Nothing on soundness.

-/
import Johnson.P5J.K10SeatsFive
import Johnson.P5J.StartAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (groupLayK namesOf RowAsks noK10 seatK10 loFive kbFive
  noFiveAt)
open VerifiableInference.Desc.LinkJoin (loAt kbW gsAt seatFiveAt)
open OnBytes.Params Johnson.Pack Johnson.G Johnson.Top.H
open LPFK10 (ixK10)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
/-- The first chain's frame at the seated term. -/
local notation "FR" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **K10Heavy's FIELD hX FROM THE HEAD, AT THE WRITTEN LISTS.** -/
theorem AtMgA.hX_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (l : ℕ) (hl : l < 25) (p : Place) (hp : At.ps[ixK10 l]? = some p)
    (hM : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.mainRows ≠ 0 →
      cMain (At.cs Zp) ((loAt l).get i).1 = (stageOf (gsAt l) 219).C)
    (hZ : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.maskRows ≠ 0 →
      cMask (At.cs Zp) ((loAt l).get i).1 = (stageOf (gsAt l) 219).Z) :
    ∀ z (a : TS × (Frame.E FR).Str), XK h l ((z, a.1), a.2) →
      RowAsks (At.cs Zp) (loAt l) (seatK10 (loAt l) (At.pseats Zp) l) (kbW l)
        (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ)
        (namesOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ
          (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l))
        (At.N Zp cF) (p.link.getD 0) (oAt (ixK10 l))
        (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l) a.1 := by
  obtain ⟨L, R⟩ := atMgR_rch_of_head h
  exact h.hX_paid L R.listed R.fold l hl p hp hM hZ

/-- **K10Heavy's FIELD hX FROM THE HEAD, AT LINK 0, AT THE FIVE-LIST.** -/
theorem AtMgA.hX_five_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (p : Place) (hp : At.ps[ixK10 0]? = some p)
    (hM : ∀ i, memMain loFive i → (loFive.get i).1.mainRows ≠ 0 →
      cMain (At.cs Zp) (loFive.get i).1 = (stageOf (gsAt 0) 219).C)
    (hZ : ∀ i, memMain loFive i → (loFive.get i).1.maskRows ≠ 0 →
      cMask (At.cs Zp) (loFive.get i).1 = (stageOf (gsAt 0) 219).Z)
    (hM₆ : ∀ i, memMain (loAt 0) i → ((loAt 0).get i).1.mainRows ≠ 0 →
      cMain (At.cs Zp) ((loAt 0).get i).1 = (stageOf (gsAt 0) 219).C)
    (hZ₆ : ∀ i, memMain (loAt 0) i → ((loAt 0).get i).1.maskRows ≠ 0 →
      cMask (At.cs Zp) ((loAt 0).get i).1 = (stageOf (gsAt 0) 219).Z) :
    ∀ z (a : TS × (Frame.E FR).Str), XK h 0 ((z, a.1), a.2) →
      RowAsks (At.cs Zp) loFive (seatFiveAt (At.pseats Zp)) kbFive
        (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ)
        (namesOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ
          (noFiveAt (At.seats Zp) (At.pseats Zp)))
        (At.N Zp cF) (p.link.getD 0) (oAt (ixK10 0))
        (noFiveAt (At.seats Zp) (At.pseats Zp)) a.1 := by
  obtain ⟨L, R⟩ := atMgR_rch_of_head h
  exact h.hX_five_paid L R.listed R.fold p hp hM hZ hM₆ hZ₆

end P5J

#print axioms P5J.AtMgA.hX_head
#print axioms P5J.AtMgA.hX_five_head
