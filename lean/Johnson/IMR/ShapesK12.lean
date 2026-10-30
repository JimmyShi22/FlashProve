-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/ShapesK12.lean: FoldFacts' field «msgShapes»: THE ONE DEBT THAT
STAYED FOR THE SHAPES, AT NUMBER 354 (the proximity test at the first chain's finish): the premise
k12 of shapeDebts_fenced (ShapesK2.lean), to its letter, under two premises on the plan.
Statements and proofs.

What is joined.
  the law            K12.Coin.k12_shapes (Johnson/Desc/K12/Coin/
                     ShapesAppend.lean): a yes of the test's decision leaves the shapes of the
                     statement's oracle messages and lays behind them the shapes of the notices
                     of its sendings
  from step to yes   as in the proof of K12.Coin.sends_atFinish (Coin/SendsAtFinish.lean), whose
                     first lines are repeated here with another end
  the sub-protocol   k12_names · what the list says: snAt_k12 · place_354 (
                     Johnson/IMR/SendsK12.lean; Door/SentAtPlace.lean), called

  noticesOf_coin     IM.noticesOf (ShapesFold.lean) is K12.Coin.noticesOf
  shapes_atFinish    at EVERY state in front: an accepting step of (atFinish π).retype appends the
                     shapes of the notices of sendsFrom π 0 π.nums.stages.tail, and turns none
  k12_shape_debt     **shapeDebts_fenced's premise k12**, at every fence G (so at ReachedAt … 354)

THE TWO PREMISES, both on the plan alone: hp: the proximity test's test on the plan accepts at
p12OfMade Z.made · ho: nums.ownMask = false there. (Both fall in scope under the tests on the plan:
hp_of_planOk, Johnson/IMR/SendsFinal.lean · H2K.Made.p12OfMade_own.)
What is not claimed. The arm in which the test sends its own mask. A sub-protocol that rejects
everything has the debt for nothing. No soundness.

-/
import Johnson.IMR.SendsK12
import Johnson.IMR.ShapesFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open OnBytes (OracleNotice)
open VerifiableInference.Desc (Block Place KindName OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12 (atFinish proximityTestKind guardedProximityTestParts P12 enterFinish leaveFinish)
open VerifiableInference.Desc.K12.Door (snAt snAt_k12)
open VerifiableInference.Desc.K12.Coin (sendsFrom k12_shapes)
open H2K.JointK H2K.Out
open ProofFile (Cl)

/-- IM.noticesOf, the list of the notices' shapes, is K12.Coin.noticesOf. -/
theorem noticesOf_coin (snd : List (Array OracleNotice)) :
    noticesOf snd = VerifiableInference.Desc.K12.Coin.noticesOf snd := by
  unfold noticesOf VerifiableInference.Desc.K12.Coin.noticesOf
  rw [List.map_flatMap]

section
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Coin

/-- **What an accepting step of the proximity test at the first chain's finish does to the
shapes.** -/
theorem shapes_atFinish (π : P12) (hp : (proximityTestKind guardedProximityTestParts π : Blk').planOk = true)
    (ho : π.nums.ownMask = false) (ft : ℕ) (s s' : First.S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (n : ℕ)
    (hY : ((atFinish π).retype : Block First.S ProofFile.Cl).step ft s rs cols = .ok (s', n)) :
    shapesOf s'.st = shapesOf s.st ++ IM.noticesOf (sendsFrom π 0 π.nums.stages.tail) := by
  have hS : Sits ((atFinish π).retype : Block First.S ProofFile.Cl) (proximityTestKind guardedProximityTestParts π : Blk') enterFinish
      leaveFinish := (sits_inside enterFinish (proximityTestKind guardedProximityTestParts π : Blk') leaveFinish).retype
  obtain ⟨t, t', e1, e2, e3⟩ := hS.step ft s s' rs cols n hY
  obtain ⟨o, _, _, _, ht⟩ := Seat.enterFinish_ok s t e1
  obtain ⟨gs, hd⟩ := step_decide (proximityTestKind guardedProximityTestParts π : Blk') ft _ t' rs cols n e2
  have he := early_of_planOk π hp
  have ha := answers_of_planOk π hp
  have hm : t.mask.isSome = true := mask_of_yes π hp ho t t' ft n rs cols e2
  have hl := laysOnly_finish s t' s' e3
  have h1 : s'.st = t'.st := by rw [hl]
  have h3 : t.st = s.st := by rw [ht]
  obtain ⟨first, rest, hs, hSh⟩ := k12_shapes π he ha t t' _ gs hm hd
  have htail : π.nums.stages.tail = rest := by rw [hs]; rfl
  rw [htail, noticesOf_coin, h1, ← h3]
  exact hSh

end

/-- **shapeDebts_fenced's premise k12.** -/
theorem k12_shape_debt {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {ft : ℕ} {G : S → Prop}
    (hp : (proximityTestKind guardedProximityTestParts (H2U.p12OfMade Z.made) : Blk').planOk = true)
    (ho : (H2U.p12OfMade Z.made).nums.ownMask = false) :
    ∀ b' : Block S Cl, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) →
      b'.place = { chain := 1, link := none, piece := 2, kind := .K12 } →
      ShapesOn ft G (snAt Z G₀ placesW 354) b' := by
  intro b' hL ep
  rw [k12_names hL ep, snAt_k12 Z G₀ placesW 354 2 none place_354]
  exact fun s s' rs cols n _ hy => shapes_atFinish _ hp ho ft s s' rs cols n hy

end IM

#print axioms IM.noticesOf_coin
#print axioms IM.shapes_atFinish
#print axioms IM.k12_shape_debt
