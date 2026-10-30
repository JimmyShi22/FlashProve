-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/Part4/FreshTableOfASending.lean: A PROXIMITY TEST WHOSE FIRST
FOLD's FRESH TABLE WAS SENT BY A SENDING OF THE KIND K1 (so at the last chain's test, the place W):
WHERE THE TEST's COINS FOR THAT TABLE ARE THE SENDER's OWN, NUMBER BY NUMBER, THE TEST's FRESH TABLE
AND ITS TAILS ARE THE MASK ROWS AND TAILS OF THE SENDER's MESSAGE.

WHAT IT IS NOT.
  * THAT THE COINS ARE THE SAME IS A PREMISE (held): no book, no lending, no run stands here. At the
    maker's book another author's law has it (fresh_held, AtFullSide/K12/HeldAtHeadW.lean).
  * The public facts on the message (it rides at the stage's two numbers; it has no main row and
    2 ^ h mask rows; its mask code is the stage's; the rows have room) are premises, gathered in one
    structure. They are shown at no place here.
  * Within the table alone: rows below 2 ^ h, places below the mask code's message length, tails
    below its tail's length.
  * It says nothing of a column, a tree or a thread.
  * Nothing on completeness, soundness or what a proof hides.

WORDS. A fold's fresh table is laid of 2 k + 1 coins, the coefficients of a hiding polynomial; its
2 ^ h rows' tails are further coins, which follow them. The test lays it by packedN at hideAt
(TestJob.first, K12/Test.lean); a sending of the kind K1 lays a message that "rides" by Ride.lay
(K1/Coins.lean). That the two layings are one is lay_is_packed (K12/AtProof/FreshAtL.lean).

WHAT IT IS. One definition, a premise's form; four theorems.

  RidesAtTheStage            the public facts on the message
  hidingCoefficientsAgree    hideAt reads its coins below 2 k + 1 alone
  noCoinInFrontOfTheMask     at such a message no coin of a main row stands in front of the mask's
  freshTableIsTheSendersRows **the test's fresh table is the message's mask rows**
  freshTailsAreTheSenders    **its tails are the message's mask rows' tails**

CALLED. lay_is_packed; coefU_byName (K12/FreshAtJob.lean).
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.FreshAtL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Part4
open OnBytes.Slice (GE GF ofE toE_ofE readE_ofTriple codeOf)
open Johnson.Prover.Link (packedN)
open Johnson.Prover.Send (shapeAt)
open Fmt.M1 (Stage)
open H2K.Pub (sgOf)
open VerifiableInference.Desc (K1.Par)
open ProofFile.Honest.K12.Light (coefU_byName)
open ProofFile.Honest.K12.AtProof (lay_is_packed)

/-- **The public facts on a message that is a stage's fresh table.** -/
structure RidesAtTheStage (s : Stage) (P : K1.Par) (ride : ℕ → Option K1.Ride) (k : ℕ) : Prop where
  rides : ride k = some ⟨s.k, s.h⟩
  stage : s.h ≤ s.k
  room : 2 * s.k + 1 ≤ s.h + s.Z.l
  noMainRow : (shapeAt P k).mainRows = 0
  maskRows : (shapeAt P k).maskRows = 2 ^ s.h
  code : codeOf (P.codes.mask.getD (shapeAt P k).maskCode default) = s.Z

/-- **hideAt reads its coins below 2 k + 1 alone.** -/
theorem hidingCoefficientsAgree (k : ℕ) (c c' : ℕ → GE) (same : ∀ n < 2 * k + 1, c n = c' n) :
    hideAt k c = hideAt k c' := by
  have one := coefU_byName k k rfl (fun n => OnBytes.E.ofTriple (ofE (c n))) c
    (fun n _ => by rw [readE_ofTriple, toE_ofE])
  have two := coefU_byName k k rfl (fun n => OnBytes.E.ofTriple (ofE (c n))) c'
    (fun n below => by rw [readE_ofTriple, toE_ofE]; exact same n below)
  exact one.symm.trans two

variable {s : Stage} {P : K1.Par} {ride : ℕ → Option K1.Ride} {k : ℕ}

/-- **At such a message no coin of a main row stands in front of the mask's.** -/
theorem noCoinInFrontOfTheMask (fits : RidesAtTheStage s P ride k) :
    (K1.stepsOf P.codes (shapeAt P k) (ride k)).main = 0 ∧
      (K1.stepsOf P.codes (shapeAt P k) (ride k)).mask = 2 * s.k + 1 := by
  have positive : (shapeAt P k).maskRows ≠ 0 := by
    rw [fits.maskRows]
    exact Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos s.h)
  refine ⟨?_, ?_⟩
  · unfold K1.Steps.main K1.stepsOf
    simp [fits.noMainRow, positive]
  · unfold K1.stepsOf
    rw [fits.rides]
    rfl

/-- **The test's fresh table is the message's mask rows.** hide: the test's coins for the table. c₀:
the sender's. held: they are the same, number by number, below 2 k + 1: a premise. -/
theorem freshTableIsTheSendersRows (fits : RidesAtTheStage s P ride k)
    (data : ℕ → ℕ → ℕ → Option (GF ⊕ GE)) (c₀ : Cs (K1.dueR P ride)) (hide : ℕ → GE)
    (held : ∀ i < 2 * s.k + 1, K1.ce c₀ ((K1.startR P ride k).e + i) = hide i) :
    ∀ r < 2 ^ s.h, ∀ j < s.Z.l,
      packedN (sgOf s) (hideAt ((sgOf s).h + (sgOf s).g) hide) r j =
        (K1.rowsR P ride data c₀ k).mask r j := by
  intro r isRow j isPlace
  have inFront := (noCoinInFrontOfTheMask fits).1
  have length : (P.codes.mask.getD (shapeAt P k).maskCode default).ell = s.Z.l :=
    congrArg Fmt.M1.Code.l fits.code
  have rounds : (sgOf s).h + (sgOf s).g = s.k := Light.sg_k fits.stage
  have inside : r < (shapeAt P k).maskRows ∧
      j < (P.codes.mask.getD (shapeAt P k).maskCode default).ell := by
    rw [fits.maskRows, length]
    exact ⟨isRow, isPlace⟩
  have sent : (K1.rowsR P ride data c₀ k).mask r j =
      (⟨s.k, s.h⟩ : K1.Ride).lay (fun i => if i < 2 * s.k + 1 then
        K1.ce c₀ ((K1.startR P ride k).e + (if (shapeAt P k).mainDeg == 3 then
          (K1.stepsOf P.codes (shapeAt P k) (ride k)).main else 0) + i) else 0) r j := by
    unfold K1.rowsR
    simp only [fits.rides, if_pos inside]
    rfl
  rw [sent, lay_is_packed s fits.stage fits.room _ r j isRow isPlace]
  refine congrArg (fun coefficients => packedN (sgOf s) coefficients r j)
    (hidingCoefficientsAgree _ _ _ fun n isCoin => ?_)
  have below : n < 2 * s.k + 1 := by
    rw [rounds] at isCoin
    exact isCoin
  rw [if_pos below, inFront, ite_self, Nat.add_zero]
  exact (held n below).symm

/-- **Its tails are the message's mask rows' tails.** held: the coins are the same below the fresh
table's whole count, 2 k + 1 + 2 ^ h times the tail's length: a premise. -/
theorem freshTailsAreTheSenders (fits : RidesAtTheStage s P ride k)
    (data : ℕ → ℕ → ℕ → Option (GF ⊕ GE)) (c₀ : Cs (K1.dueR P ride)) (hide : ℕ → GE)
    (held : ∀ i < dueFresh s, K1.ce c₀ ((K1.startR P ride k).e + i) = hide i) :
    ∀ r < 2 ^ s.h, ∀ q < s.Z.r,
      tailsIn s hide r q = (K1.rowsR P ride data c₀ k).maskTl r q := by
  intro r isRow q isPlace
  obtain ⟨inFront, maskCoins⟩ := noCoinInFrontOfTheMask fits
  have length : (P.codes.mask.getD (shapeAt P k).maskCode default).r = s.Z.r :=
    congrArg Fmt.M1.Code.r fits.code
  have inside : r < (shapeAt P k).maskRows ∧
      q < (P.codes.mask.getD (shapeAt P k).maskCode default).r := by
    rw [fits.maskRows, length]
    exact ⟨isRow, isPlace⟩
  have sent : (K1.rowsR P ride data c₀ k).maskTl r q =
      K1.ce c₀ ((K1.startR P ride k).e + (if (shapeAt P k).mainDeg == 3 then
        (K1.stepsOf P.codes (shapeAt P k) (ride k)).main else 0) +
        (K1.stepsOf P.codes (shapeAt P k) (ride k)).mask +
        r * (P.codes.mask.getD (shapeAt P k).maskCode default).r + q) := by
    unfold K1.rowsR
    simp only [if_pos inside]
  have below : 2 * s.k + 1 + r * s.Z.r + q < dueFresh s := by
    have rows : (r + 1) * s.Z.r ≤ 2 ^ s.h * s.Z.r := Nat.mul_le_mul_right _ isRow
    have next : (r + 1) * s.Z.r = r * s.Z.r + s.Z.r := Nat.succ_mul r s.Z.r
    unfold dueFresh
    omega
  rw [sent, inFront, ite_self, Nat.add_zero, maskCoins, length]
  unfold tailsIn
  rw [← held _ below]
  congr 1
  omega

end ProofFile.Honest.K12.Part4

#print axioms ProofFile.Honest.K12.Part4.hidingCoefficientsAgree
#print axioms ProofFile.Honest.K12.Part4.noCoinInFrontOfTheMask
#print axioms ProofFile.Honest.K12.Part4.freshTableIsTheSendersRows
#print axioms ProofFile.Honest.K12.Part4.freshTailsAreTheSenders
