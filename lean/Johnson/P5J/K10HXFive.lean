-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K10HXFive.lean (kind K10): THE FIELD hX OF `K10Heavy` AT THE CLOSED CONSTANT's LETTERS,
AT LINK 0, AT THE FIVE-LIST. Beside K10HXAt.lean, whose statement stands at the written lists (at
link 0: the six-list). Statements and proofs: a join.

Why a second theorem at link 0. K10's typed group at link 0 is cut over loFive (the written list's
messages with a main row), because at the six-list another field of the same structure asks a
witness for the index masks' message that the relation behind lacks; the
structure's fields must stand at one list.

The letters at link 0. lo := loFive · kb := kbFive · no := noFiveAt (At.seats Zp) (At.pseats Zp)
(HingeFiveAtMg.lean) · gs := gsAt 0 · the rest as in K10HXAt.lean.

What is joined. rowAsks_whole (general in the list) with: shapes :=
AtMg.hinge_five_at_border · hinj := hinj_five, carried to the constant's letters
(`AtMg.hinj_five_at`) · hA := five_layout, hk := five_kLay with kh_at 0 (LinkZeroFive.lean;
K10HXAt.lean) · **hc := the third conjunct of five_of_facts CALLED AT THE SIX-LIST with the hinge
there: its end names no list** (the layout of the begun statement, and the stage).

What is said. `AtMg.noFive_is_at`: the five-list's numbering at the constant's letters is the one
at the written plan's. `AtMg.hinj_five_at`. `AtMgA.hX_five`: **the field.**

PREMISES. As K10HXAt.lean's, at l = 0: h · Fo · hp · hM, hZ AT THE FIVE-LIST · **hM₆, hZ₆: the same
two AT THE SIX-LIST (five_of_facts takes them)** · seats (on the state).

Limits. AtMgA and FoldFacts are premises. secondHashFunction alone. Nothing on soundness.

-/
import Johnson.P5J.K10HXAt
import Johnson.P5J.HingeFiveAtMg

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
open VerifiableInference.Desc.First (ModelPart Numbers start Item FoldFacts FoldData)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (groupLayK namesOf RowAsks rowAsks_whole membersOf
  seatsPlanW loFive kbFive noFive noFiveAt hinj_five five_layout five_kLay link_of_stand)
open VerifiableInference.Desc.LinkJoin (loAt kbW gsAt five_of_facts)
open OnBytes.Params Johnson.Pack Johnson.G Johnson.Top.H
open LPFK10 (ixK10)
open IM (subAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
/-- The first chain's frame at the seated term. -/
local notation "FR" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- The five-list's numbering at the constant's letters is the one at the written plan's. -/
theorem AtMg.noFive_is_at {o : ProofFile.SecondHashFunctionArgument} (h : AtMg o Z D r Zp Np cF) :
    noFiveAt (At.seats Zp) (At.pseats Zp) = noFive := by
  have e1 : At.pseats Zp = P5T.psFull := h.laid.seats h.scope
  have e2 : At.seats Zp = seatsPlanW := by
    unfold At.seats
    rw [e1]
  rw [e1, e2]
  rfl

/-- That numbering parts the five-list's members. -/
theorem AtMg.hinj_five_at {o : ProofFile.SecondHashFunctionArgument} (h : AtMg o Z D r Zp Np cF) :
    ∀ i ∈ membersOf loFive, ∀ j ∈ membersOf loFive,
      noFiveAt (At.seats Zp) (At.pseats Zp) i = noFiveAt (At.seats Zp) (At.pseats Zp) j →
        i = j := by
  rw [h.noFive_is_at]
  exact hinj_five

/-- **K10Heavy's FIELD hX AT LINK 0, AT THE FIVE-LIST.** -/
theorem AtMgA.hX_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Ld : VerifiableInference.Desc.K12.Door.Laid)
    (Fo : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps)
    (p : Place) (hp : At.ps[ixK10 0]? = some p)
    (hM : ∀ i, memMain loFive i → (loFive.get i).1.mainRows ≠ 0 →
      cMain (At.cs Zp) (loFive.get i).1 = (stageOf (gsAt 0) 219).C)
    (hZ : ∀ i, memMain loFive i → (loFive.get i).1.maskRows ≠ 0 →
      cMask (At.cs Zp) (loFive.get i).1 = (stageOf (gsAt 0) 219).Z)
    (hM₆ : ∀ i, memMain (loAt 0) i → ((loAt 0).get i).1.mainRows ≠ 0 →
      cMain (At.cs Zp) ((loAt 0).get i).1 = (stageOf (gsAt 0) 219).C)
    (hZ₆ : ∀ i, memMain (loAt 0) i → ((loAt 0).get i).1.maskRows ≠ 0 →
      cMask (At.cs Zp) ((loAt 0).get i).1 = (stageOf (gsAt 0) 219).Z)
    (seat : Fin loFive.length → ℕ × ℕ)
    (seats : ∀ s, XK h 0 s → ∀ i, memMain loFive i →
      seatBy noFirst s.1.2.book (noFiveAt (At.seats Zp) (At.pseats Zp) i) = some (seat i)) :
    ∀ z (a : TS × (Frame.E FR).Str), XK h 0 ((z, a.1), a.2) →
      RowAsks (At.cs Zp) loFive seat kbFive
        (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ)
        (namesOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ
          (noFiveAt (At.seats Zp) (At.pseats Zp)))
        (At.N Zp cF) (p.link.getD 0) (oAt (ixK10 0))
        (noFiveAt (At.seats Zp) (At.pseats Zp)) a.1 := by
  intro z a hX
  obtain ⟨hon, hr, hu'⟩ := hX
  have hu : a.1.failed = none := not_not.1 hu'
  have hl : 0 < 25 := by omega
  obtain ⟨e1, e2, e3⟩ := k10_place 0 hl p hp
  have H₆ := h.toAtMg.hinge_all Fo rfl hl ((z, a.1), a.2) hr hu
  have hr' := hr
  rw [ixK10_is 0 hl] at hr'
  have H₅ := h.toAtMg.hinge_five_at_border Fo rfl ((z, a.1), a.2) hr' hu
  have hsh := VerifiableInference.Desc.First.K8.shapeAt_of_onQ (At.N Zp cF) (mgAtAll h) fullLinks
    At.ps (fun a => a) (ixK10 0) ((z, a.1), a.2) hon hu
  rw [hp] at hsh
  unfold VerifiableInference.Desc.First.shapeAt at hsh
  simp only [Bool.and_eq_true, beq_iff_eq] at hsh
  obtain ⟨Lk, hLk⟩ := link_of_stand a.1 (subAt 0) (hsh.1.1.trans e2)
  have h5 := five_of_facts Fo ((z, a.1), a.2) hr hu hl p hp e1 e3 Lk hLk h.toAtMg.codes_full rfl
    h.toAtMg.shapeAt_full hM₆ hZ₆ [] H₆
  rw [e1]
  exact rowAsks_whole (At.cs Zp) loFive seat (stageOf (gsAt 0) 219) radFull kbFive hM hZ
    (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) (ixK10 0) 0 Fo _ ((z, a.1), a.2) hon hr
    hu p hp e1 (subAt 0) e2 rfl rfl five_layout h.toAtMg.hinj_five_at
    (five_kLay.trans (kh_at 0 hl).1) (kh_at 0 hl).2 h5.2.2.1 (seats _ ⟨hon, hr, hu'⟩) H₅

end P5J

#print axioms P5J.AtMg.noFive_is_at
#print axioms P5J.AtMg.hinj_five_at
#print axioms P5J.AtMgA.hX_five
