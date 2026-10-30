-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/K6SeatsScope.lean: IN THE GOALS' SCOPE THE TEST seatsK6C (Law/K6SeatsTest.lean)
ACCEPTS AT Z's OWN VALUES, WHERE THREE MORE VALUES ARE AS NAMED. One theorem: five calls.


What is proved. Let W be in the goals' scope, Z the public part of the IOP as written in Lean at W's
three files and any o, let the public test on the sizes, the lists of rounds, the
request's layout and the sendings accept (madePinnedAt ... = true), let the proof file's value be
laid, and let Z's public parameters be publicOf's. Then the four premises of seatsK6C_of_seats
(Law/K6SeatsWritten.lean) that other files' theorems give are given:
  SeatsWritten Z (seatsWritten_in_scope) · Z.made.proof = proofSendsFull (sends_in_scope) ·
  XPart Z.p.X (xPart_in_scope) · readsOf Z.p.X = 0 (public_third).
  **seatsK6C_in_scope**   so the test accepts.

WHAT IS LEFT IN FRONT OF IT.
  hb, h0: TWO NUMBERS, GIVEN BY NOTHING YET: how many oracle messages the sub-protocols tell in
          front of segment 24's first sending (179) and in front of border 341 (183).
  hA: the entry number 0 of the list of arrays is (24, "U3"): at the built segments' own list
          another file's theorem gives it in scope (Law/ReadsRoomInScope.lean: reads_room_in_scope,
          first clause): not imported here.
  hN, hL: how the table's list "sent" and the listed seats are made: see Law/K6SeatsWritten.lean.

reads_zero (the array of the reads is number 0 wherever the maker of the public parameters returns)
was sought by its conclusion before it was kept: it lies nowhere but at one toy constant.
No existential quantifier in this statement.
Not proved here. That the test madePinnedAt accepts at any files, or stands in a verifier's list.
That the value is laid. XPart at the public parameters that another o gives. Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.K6SeatsWritten
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Desc.Kinds.Law.ReadsNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold

open OnBytes OnBytes.Params
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.PlanWritten (madePinnedAt)
open VerifiableInference.PlanWritten.Joined (sends_in_scope)
open P5T (planSeats planSeatsAll numbersOf)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.FillSent (sentDataOf TreeLook)
open VerifiableInference.Desc.Kinds.Head.Law.OffPad (seatsWritten_in_scope xPart_in_scope)

/-- Wherever the maker of the public parameters returns, the array of the reads is number 0. -/
theorem reads_zero {pol KL : ByteArray} {lay : Option ByteArray} {X : OnBytes.Model.Verify.Public}
    (h : publicOf pol KL lay = .ok X) : readsOf X = 0 := by
  have h3 : X.H.tl.ix.U.getD 2 none = some 0 := ReadsNamed.public_third h
  unfold readsOf
  rw [h3]
  rfl

/-- **In scope the test accepts.** -/
theorem seatsK6C_in_scope {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {pp : Inst.Model.ScalesAndPolicy}
    {lay' : Option ByteArray} (hW : VerifierAndGoals.InScope W = true) (hR : VerifierAndGoals.readFiles W = .ok pp)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r))
    (hp : publicOf W.pol W.KL lay' = .ok Z.p.X) (N : Numbers)
    (hN : N.sent 24 0 = (numbersOf (planSeats Z Z.D.1)).sent 24 0) (base : Nat → Nat)
    (trees : Nat → List TreeLook) (hb : base 24 = 179) (n0 : Nat) (h0 : n0 = 183)
    (Lp : K12.Door.Laid) (hL : K12.Door.laidOf Z.first.codes (sentsOf Z.made.proof.1) = some Lp)
    (arrs : Array (Nat × String)) (hA : arrs[0]? = some (24, "U3")) :
    seatsK6C (P5T.arrOf (planSeatsAll Z Z.D)) N Z.p.X Z.first.layout
      (P5T.numOfPlan (planSeatsAll Z Z.D)) (P5T.numOfPlan (planSeatsAll Z Z.D) 24 0) 0
      Z.first.codes Z.first.shape (sentDataOf Z.first.shape base trees) Lp
      (K12.Door.msgsOfChain Z.made.proof.1) arrs n0 = true :=
  seatsK6C_of_seats (seatsWritten_in_scope hW h hy hl) (sends_in_scope hW h hy)
    (xPart_in_scope hW hR hp) (reads_zero hp) N hN base trees hb n0 h0 Lp hL arrs hA

end VerifiableInference.Desc.Kinds.Head.Law.AtFold

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.seatsK6C_in_scope
