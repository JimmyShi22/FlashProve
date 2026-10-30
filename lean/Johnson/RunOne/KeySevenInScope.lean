-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySevenInScope.lean: THEOREMS. **THE JOIN: in the goals' scope, seven public tests on the key file's own description hold**: the library's test on a seat finds no fault at the three sampled messages' seats (0, 0) · (1, 0) · (5, 0) · the frame holds the trees 0 · 1 · 5 at the depths of these messages' codes · the ranges' test has a stage; and the blocks in front of the three sendings tell 0 · 1 · 5 trees.
OBJECT: Key.descriptionFromSource X N P and its data. USER: none yet (meant: the seven premises of member_fk₁, Johnson/RunOne/KeyFillMeet.lean, a theorem on a member of PIN · hasSmp · NoColl at the woven tables' reading; and one line for the hand-laid table of seats atSix, Johnson/RunOne/KeyFillBaseAt.lean). LETTERS: o (a function in the hash's place: see «What is not claimed») · the public files Zp.
CALLS ALONE: this file proves nothing of its own: it joins: five_in_scope (Johnson/RunOne/Law/KeyInScope.lean) · rounds_in_scope (Johnson/RunOne/Sound/KeyListsInScope.lean) · laid_data_written (Johnson/Goal/Numbers/KeySeatLaidAt.lean) · Key.laidFixed_is · and n01_scope · n2_scope · seats_scope · holds0 | holds1 | holds5 · hst_full (Johnson/RunOne/KeySeatScope.lean · KeySeatScopeW2.lean · KeyScopeNums.lean).
  Seven X N P D    the seven tests and the three counts, as one sentence
  roundsL₁_eq      two lists of the first chain's numbers of rounds, typed apart, are one (rfl)
  seven_at         **X N P AS LETTERS**: in scope, where the source is made of the public files at any digest, the description passes its two tests on the plan and its data are the written data
  seven_in_scope   **from the yes of the two in a row** (the public files are read; the key file's piece is laid at the fixed digest): ONE ∃ for the run, the data, the three lists and the seven
What is not claimed. "AT EVERY o" IS WORTH "AT EVERY o AT WHICH THE PUBLIC PART IS ACCEPTED". In scope publicOfO o returns only at an o whose digests of the four public tables are the format's: scope fixes these words as plain numbers, and Johnson/Desc/Ok/PlanWritten/PublicAt.lean holds o's own digests against them. At every other o seven_in_scope, which has the yes among its premises, holds of nothing. (seven_at has no o.) THAT THE TWO IN A ROW RETURN AT ANY FILES: no theorem says it. [RAN] at publicOf's reading alone: at the stored full-size public files the piece is laid and the scope's test says yes; NO RUN HAS EVALUATED publicOfO AT ANY o. The conclusion of the theorem whose premises these seven are (Johnson/RunOne/KeyFillMeet.lean). That the verifier lays this piece. Nothing on soundness.

-/
import Johnson.RunOne.KeySeatScopeW2
import Johnson.RunOne.Sound.KeyListsInScope
import Johnson.Goal.Numbers.KeySeatLaidAt

set_option autoImplicit false

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Maker
open VerifiableInference.Desc
open Johnson.RunOne.KeyRows23 (fr₁ oneAt)
open Johnson.Pack (aOf)
open Johnson.Top.H (csKey shIdx shMul)
open Johnson.G (writtenKFull)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.KeyInScope (five_in_scope)
open Johnson.RunOne.Sound (L₁ L₂ L₃ rounds_in_scope)

/-- The seven public tests, and the three counts. -/
def Seven (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) (D : WholeD) : Prop :=
  (∀ t0 t1 t2 : String, seatFaultAt (Key.descriptionFromSource X N P) csKey t0 shIdx 0 0 = none ∧ seatFaultAt (Key.descriptionFromSource X N P) csKey t1 shMul 1 0 = none ∧
    seatFaultAt (Key.descriptionFromSource X N P) csKey t2 Johnson.Top.H.shW 5 0 = none) ∧
  ((fr₁ D).all.any fun t => t.no == 0 && decide (aOf csKey shIdx ≤ t.a)) = true ∧
  ((fr₁ D).all.any fun t => t.no == 1 && decide (aOf csKey shMul ≤ t.a)) = true ∧
  ((fr₁ D).all.any fun t => t.no == 5 && decide (aOf csKey Johnson.Top.H.shW ≤ t.a)) = true ∧
  0 < (oneAt X).ranges.stages.length ∧
  (oraclesOf ((Key.descriptionFromSource X N P).first.blocksInOrder.take 0)).length = 0 ∧ (oraclesOf ((Key.descriptionFromSource X N P).first.blocksInOrder.take 1)).length = 1 ∧
  (oraclesOf ((Key.descriptionFromSource X N P).first.blocksInOrder.take 17)).length = 5

theorem roundsL₁_eq : roundsL₁ = L₁ := rfl

/-- **The seven, X N P as letters.** -/
theorem seven_at {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z)
    {cfg : ByteArray} {m : Johnson.G.OfPlan.Made} {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}
    (hm : Key.madeAt Z Zp.lay cfg = .ok m) (hX : Key.sourceOf m = .ok X) (hp : (Key.descriptionFromSource X N P).planOk = true)
    (hw : (Key.descriptionFromSource X N P).wantedOk = true) (hD : (Key.descriptionFromSource X N P).data "key file" = .ok writtenKFull) : Seven X N P writtenKFull := by
  obtain ⟨-, hr, hl, hi, hc⟩ := five_in_scope hZ hP hm hX hp
  have hL : (Key.descriptionFromSource X N P).first.blocksInOrder.map (·.rounds.length) = roundsL₁ := (rounds_in_scope hZ hP hm hX hp hw).1
  have hs := seats_scope X N P hp hD hL
  refine ⟨fun t0 t1 t2 => ⟨(n01_scope X N P hi hc hr t0 t1).1, (n01_scope X N P hi hc hr t0 t1).2,
    n2_scope X N P (hc.trans codes_full) hl hp hD hL t2⟩, holds0, holds1, holds5, ?_, hs.1, hs.2.1, hs.2.2⟩
  show 0 < X.Y.k.oneTime.ranges.stages.length
  rw [hr]
  exact hst_full

/-- **The seven, from the yes of the two in a row**: one ∃ for the run, the data, the three lists and the seven. -/
theorem seven_in_scope {o : Nat → ByteArray → ByteArray} {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {D : WholeD} {r : Key.KeyRun}
    (h : ((VerifiableInference.PlanWritten.publicOfO o Zp.pol Zp.KL (some Zp.lay)).bind fun Z => Key.keyDataAndDecisionAtFixedDigest Z Zp.lay) = .ok (D, r)) :
    ∃ X N P, r = ((Key.descriptionFromSource X N P).pull Key.keyInstanceOfOutOfDomainSample).run ∧ (Key.descriptionFromSource X N P).data "key file" = .ok D ∧ D = writtenKFull ∧
      ((Key.descriptionFromSource X N P).first.blocksInOrder.map (·.rounds.length) = L₁ ∧ (Key.descriptionFromSource X N P).shared.blocksInOrder.map (·.rounds.length) = L₂ ∧
        (Key.descriptionFromSource X N P).second.blocksInOrder.map (·.rounds.length) = L₃) ∧ Seven X N P D := by
  have hW : D = writtenKFull := VerifiableInference.PlanWritten.laid_data_written hZ h
  cases hZ' : VerifiableInference.PlanWritten.publicOfO o Zp.pol Zp.KL (some Zp.lay) with
  | error e =>
    rw [hZ'] at h
    cases h
  | ok Z =>
    rw [hZ'] at h
    obtain ⟨m, X, N, P, hm, hX, -, -, -, hp, hw, -, -, hd, hr⟩ := Key.laidFixed_is Z Zp.lay D r h
    have hP := Johnson.RunOne.Law.ReadAtO.readOf_publicOfO hZ'
    subst hW
    exact ⟨X, N, P, hr, hd, rfl, rounds_in_scope hZ hP hm hX hp hw, seven_at hZ hP hm hX hp hw hd⟩

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.roundsL₁_eq
#print axioms Johnson.RunOne.KeyLetters.seven_at
#print axioms Johnson.RunOne.KeyLetters.seven_in_scope
