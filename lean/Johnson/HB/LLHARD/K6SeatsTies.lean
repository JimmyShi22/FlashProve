-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/K6SeatsTies.lean: what the law on the test `seatsK6C`
(`seatsK6C_in_scope`, Johnson/Goal/Meaning/K6SeatsScope.lean) leaves in front of itself as "given by
nothing yet", at the head's own terms: the two numbers of oracle messages (179 in front of segment
24's first sending, 183 in front of border 341), and that the listed seats and the data on what is
sent are the terms that the law names. In scope, wherever the value is laid; no test's accept is a
premise.

Row or tool. Closed facts with negative tests, laws in scope by calls of named laws, and two
equations by definition. Payers for premises of another law. The law's file is not imported here.

Who pays what. What the sub-protocols tell is the written cut's: `told_of_laid`
(Johnson/HB/LLHARD/K6NumbersAtName.lean). The counts at the borders: `countsAre_at_toldCut`
(OwedTies.lean) and `told_at` (ToldCounts.lean).

What is here.
  `find_24`: in the written list of places, the place of segment 24's first sending, as
    `FillSent.baseAt` seeks it (Johnson/Desc/First/SentTerms.lean), is number 339. `find_23_not`:
    the negative test: segment 23's is not.
  `counts_339`: at border 339 the closed list of counts has (179, 73). `counts_340_not`: the
    negative test: at border 340 there are no longer 179 oracle messages.
  `msgs_of`: at all numbers laid off the written cut over the written places: the number of oracle
    messages at a border is the closed list's.
  `msgs_341_at_name`: `(At.N Zp cF).msgsAt PS[341]? = 183`. `base_24_at_name`: `baseAt (At.N Zp cF)
    Sound.linksFull PS 24 = 179`.
  `laid_text`: `At.laid? Zp` is `K12.Door.laidOf` at the first chain's codes and at its sendings'
    notices in the order of their entries. By definition.
  `dS_text`: at the head, the composed meaning's data on what is sent are `sentDataOf` at the
    letters' shape, at `baseAt` of the letters' numbers, and at the built segments' looks. By
    definition.
By evaluations in Lean's kernel (`decide +kernel`): `find_24`, `find_23_not`, `counts_339`,
`counts_340_not`.

Limits. The law's fifth premise, on the first entry of the built segment 24's list of arrays, is not
touched. Nothing on soundness.


-/
import Johnson.HB.LLHARD.K6NumbersAtName
import Johnson.Desc.First.SentTerms
import Johnson.P5J.LettersAt2

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open VerifiableInference.Desc
open VerifiableInference.Desc.First (Numbers flatPlacesOf toldCut shift)
open VerifiableInference.Desc.First.FillSent (baseAt sentDataOf treesAt)
open VerifiableInference.Desc.K13.Law (countsFull told_at countsAre_at_toldCut)

set_option maxRecDepth 1000000 in
/-- **The place of segment 24's first sending is number 339.** -/
theorem find_24 :
    ((flatPlacesOf Sound.linksFull true).find? fun p =>
      p.link == some 24 && p.piece == 1 + ((Sound.linksFull[24]?).map shift).getD 0) =
      (flatPlacesOf Sound.linksFull true)[339]? := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: segment 23's is not. -/
theorem find_23_not :
    ¬ ((flatPlacesOf Sound.linksFull true).find? fun p =>
      p.link == some 23 && p.piece == 1 + ((Sound.linksFull[23]?).map shift).getD 0) =
      (flatPlacesOf Sound.linksFull true)[339]? := by decide +kernel

set_option maxRecDepth 1000000 in
theorem counts_339 : countsFull[339]? = some (179, 73) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test. -/
theorem counts_340_not : ¬ (countsFull[340]?).map (·.1) = some 179 := by decide +kernel

/-- At all numbers laid off the written cut over the written places. -/
theorem msgs_of (M : Numbers) {k m t : ℕ} (hk : k ≤ 358) (h : countsFull[k]? = some (m, t)) :
    (M.withTold (flatPlacesOf Sound.linksFull true) toldCut).msgsAt
      (flatPlacesOf Sound.linksFull true)[k]? = m :=
  (Prod.mk.inj (Option.some.inj (h.symm.trans (told_at M countsAre_at_toldCut hk)))).1.symm

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **183 oracle messages in front of border 341.** -/
theorem msgs_341_at_name (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    (At.N Zp cF).msgsAt (flatPlacesOf Sound.linksFull true)[341]? = 183 := by
  unfold At.N
  rw [told_of_laid hZ L]
  exact msgs_of _ (by omega) counts_341.1

/-- **179 in front of segment 24's first sending.** -/
theorem base_24_at_name (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    baseAt (At.N Zp cF) Sound.linksFull (flatPlacesOf Sound.linksFull true) 24 = 179 := by
  unfold baseAt
  rw [find_24]
  unfold At.N
  rw [told_of_laid hZ L]
  exact msgs_of _ (by omega) counts_339

/-- The listed seats' term. -/
theorem laid_text (Zp : ProofFile.Pub) :
    At.laid? Zp = K12.Door.laidOf (At.cs Zp)
      ((Zp.made.proof.1.sends.mergeSort fun a b => a.entry ≤ b.entry).map (·.sent)) := rfl

/-- The term of the data on what is sent, at the head. -/
theorem dS_text (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    h.𝔇.pubD.dS = sentDataOf (At.shape Zp)
      (baseAt (At.N Zp cF) Sound.linksFull (flatPlacesOf Sound.linksFull true))
      (treesAt Zp.made.p.built.links) := rfl

end

end P5J

#print axioms P5J.find_24
#print axioms P5J.find_23_not
#print axioms P5J.counts_339
#print axioms P5J.counts_340_not
#print axioms P5J.msgs_of
#print axioms P5J.msgs_341_at_name
#print axioms P5J.base_24_at_name
#print axioms P5J.laid_text
#print axioms P5J.dS_text
