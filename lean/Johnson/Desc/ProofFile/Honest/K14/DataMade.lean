-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/DataMade.lean: kind K14: AT EVERY LIST THAT BEGINS WITH THE SHARED
CHAIN's FRONT SUB-PROTOCOL AND EIGHT MORE (FlatOf, Johnson/Desc/K14/Honest/FlatForm.lean), WHERE THE
EIGHT ARE THOSE THAT blocks P RETURNS AT A PLAN P (hb), dataOf MAKES THE NUMBERS 0 AND 6: "LIN
point" is the chain's round number 0, "LIN zeta" its round number 6. These are the two numbers that
the fields point and zeta of K14Asks (Honest/K14/Asks.lean) write out; no statement of this file
names that structure. Statements with their proofs.

hb IS A PREMISE OF ALL FOUR STATEMENTS: FlatOf by itself holds of any eight sub-protocols; that the
eight are the plan's is blocks P = some [b1, …, b8].

  places2         the places of "(rec_gamma)" and of the joinings, among the eight that blocks P
                  returns
  dataOf_flat     **dataOf shape xs = some { S := shape, atPoint := 0, atZeta := 6 }**, under FlatOf
                  and hb, at every shape
  tiedTo_flat     under FlatOf and hb the list begins as the plan's chain does (tiedTo,
                  Honest/K14/Six.lean)
  sixOf_flat      so sixOf returns there, with these numbers, where its two tests on the shapes
                  (linOk, sendingsFit) accept

What is not claimed. That blocks P returns eight at any plan. Anything on what the halves send.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.Six
import Johnson.Desc.ProofFile.Honest.K14.PaidAll
import Johnson.Desc.K14.Honest.FlatForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes.Params (LinShape)
open VerifiableInference.Desc (Block)
open Desc.K14 (P14 St blocks)
open Desc.K14.Honest (FlatOf)

variable {W₀ Rc Ky X Cl : Type}

/-- The places of "(rec_gamma)" and of the joinings, among the eight that blocks P returns (hb). -/
theorem places2 (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    b3.place = place 3 ∧ b6.place = place 6 := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  exact ⟨rfl, rfl⟩

/-- **At a list that begins with the shared chain's front sub-protocol and the eight (FlatOf), where
the eight are those that blocks P returns at a plan P (hb), dataOf makes 0 and 6**, at every
shape. -/
theorem dataOf_flat {xs : List (Block St Cl)} {c : OnBytes.Model.Verify.Chains} {P : P14}
    {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit} (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (shape : LinShape) :
    dataOf shape xs = some { S := shape, atPoint := 0, atZeta := 6 } := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  obtain ⟨p1, p4, p7, -⟩ := places4 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨p3, p6⟩ := places2 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨⟨_, _, _, rU, -⟩, pU, ⟨_, _, _, rO, -⟩, pO⟩ :=
    send_declares P 0 b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, -, -, r1, -, r4, -, -, -⟩ := declares3 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨r3, -, r6, -, -⟩ := declares_none P b1 b2 b3 b4 b5 b6 b7 b8 hb
  have q0 : x0.place = ⟨2, none, 0, .frame⟩ := l0.place
  have s0 : x0.rounds = [] := l0.rounds
  simp [dataOf, roundsInFront, q0, s0, l1.place, l2.place, l3.place, l4.place, l5.place, l6.place,
    l7.place, l1.rounds, l2.rounds, l3.rounds, l4.rounds, l5.rounds, l6.rounds, p1, pU, p3, p4,
    pO, p6, p7, r1, rU, r3, r4, rO, r6, place, sendPlace]

/-- Such a list (FlatOf, with the eight that blocks P returns: hb) begins as the plan's chain
does. -/
theorem tiedTo_flat {xs : List (Block St Cl)} {c : OnBytes.Model.Verify.Chains} {P : P14}
    {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit} (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) : tiedTo P xs = true := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  obtain ⟨p1, p4, p7, p8⟩ := places4 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨p3, p6⟩ := places2 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, pU, -, pO⟩ := send_declares P 0 b1 b2 b3 b4 b5 b6 b7 b8 hb
  have q0 : x0.place = ⟨2, none, 0, .frame⟩ := l0.place
  simp [tiedTo, hb, q0, l1.place, l2.place, l3.place, l4.place, l5.place, l6.place, l7.place,
    l8.place, l1.rounds, l2.rounds, l3.rounds, l4.rounds, l5.rounds, l6.rounds, l7.rounds,
    l8.rounds, p1, pU, p3, p4, pO, p6, p7, p8, place, sendPlace]

/-- So sixOf returns there (FlatOf and hb), with these numbers, where its two tests on the shapes,
linOk and sendingsFit, accept. -/
theorem sixOf_flat {xs : List (Block St Cl)} {c : OnBytes.Model.Verify.Chains} {P : P14}
    {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit} (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hok : OnBytes.linOk P.codes P.S = true) (hfit : sendingsFit P = true)
    (weights : W₀ → Weights) (rand : Rc → TableRand) :
    (sixOf P xs weights rand : Except String (List (Placed Empty (Common W₀ Rc Ky) X))) =
      .ok (proverSidesOfSharedRounds { S := P.S, atPoint := 0, atZeta := 6 } weights ++
        proverSidesOfSharedSendings { P := P, atPoint := 0 } weights rand) := by
  unfold sixOf rejection
  rw [hok, hfit, tiedTo_flat F hb, dataOf_flat F hb]
  rfl

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.places2
#print axioms ProofFile.Honest.K14.dataOf_flat
#print axioms ProofFile.Honest.K14.tiedTo_flat
#print axioms ProofFile.Honest.K14.sixOf_flat
