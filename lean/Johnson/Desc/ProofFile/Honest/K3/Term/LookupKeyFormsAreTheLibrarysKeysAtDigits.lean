-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT ANY SCRIPT AND ANY WITNESS: no filling, prover or thread is named.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupKeyFormsAreTheLibrarysKeysAtDigits.lean: the honest side
of the kind "lookup" (K3): at the lookup on the digits of a smallness test, the key vectors that the
table of joints' item reads off a witness (the field fills of `AtDigits`,
Honest/K3/Law/Thread/ExchangeOuts.lean) have the joint vector of the key vectors on which the honest
lookup runs (`fills_digits`, Honest/K3/Law/Thread/ExchangeFillAt.lean: `kvZ` at the array ZZ, carried
into the extension field). Two theorems, both conditional.

  `lookupKeyFormsAreTheLibrarysKeysAtDigits`   from one tie on values: the witness's entries of ZZ are
        the digits, ASKED AT THE SHAPE's OWN CALLS ALONE (call below shape.NC) and at the entries that
        a key of such a call reads
  `lookupKeyFormsAtDigitsFromTheScript`        that tie from `ScriptHoldsTheDigitArrays`
        (Honest/K3/Term/ScriptHoldsTheHonestValues.lean), at the tail's own shape

Why the bound on the call. The library's `digInCall` answers at calls from 2 on too, where the column
call * mz + c lies outside ZZ's 2 * mz columns: a tie asked at every call could not be paid from the
array. The joint vector below 2 ^ v reads the calls below NC alone (`jointKey_congr`,
Honest/K3/Law/JointKeyOfCalls.lean).

Limits. The tie is a hypothesis of the first theorem; the second moves it to a premise on the Script,
which no file shows of any Script. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeOuts
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeTies
import Johnson.Desc.ProofFile.Honest.K3.Law.JointKeyOfCalls
import Johnson.Desc.ProofFile.Honest.K3.Term.ScriptHoldsTheHonestValues

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (kvZ)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First.Look (Sent enOf mkOf)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (K3Letters digMu)
open ProofFile.Honest.FirstThread (Script)

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

/-- **At the digits the item's key vectors have the joint vector of the library's.** digits: the
honest side's array ZZ. witnessDigitsAreTheSmallnessTests: THE ONE TIE ON VALUES, asked at the calls
below shape.NC and there at the entries of ZZ that a key reads, and at no other. shapeIsLawful: the
library's test on the shape's numbers: public. -/
theorem lookupKeyFormsAreTheLibrarysKeysAtDigits {Cells Tok : Type}
    (sent : Sent) (letters : K3Letters Cells Tok) (place : PlaceL) (tail : HTailF2)
    (witness : Wit Cells Tok MsgT) (digits : Nat → Nat → Cb.Gl.F)
    (shape : OnBytes.Model.Forest.Shape) (shapeIsLawful : FoNums.ok shape = true)
    (witnessDigitsAreTheSmallnessTests : ∀ (call key : Nat) (t : Nat × Nat × Nat),
      call < shape.NC → OnBytes.DgP.digInCall tail call key = some t →
      digMu place sent letters.rad (fun j => letters.seat place.link true j.1) letters.arr witness
        (enOf place.arrays (tail.ix.ZZ, t.2.2, call * tail.mz + t.2.1)) =
      inExt digits t.2.2 (call * tail.mz + t.2.1))
    (theta : OnBytes.Slice.GE) :
    ∀ n, n < 2 ^ shape.v →
      OnBytes.Ends.jointKey shape
        (Cb.Fo.forK Cb.Gl.E
          (OnBytes.DgP.digL5 Cb.Gl.E tail (enOf place.arrays) (mkOf place.arrays) place.F.next Unit)
          ()
          (Cb.Fo.zext (digMu place sent letters.rad
            (fun j => letters.seat place.link true j.1) letters.arr witness))) theta n =
      OnBytes.Ends.jointKey shape (kvZ tail (inExt digits)) theta n := by
  refine jointKey_congr shape shapeIsLawful _ _ theta fun call callIsTheShapes key _ => ?_
  show OnBytes.DgP.Kp tail (fun e => digMu place sent letters.rad
    (fun j => letters.seat place.link true j.1) letters.arr witness (enOf place.arrays e)) call
    key = kvZ tail (inExt digits) call key
  unfold OnBytes.DgP.Kp OnBytes.HonestTrace.kvZ
  cases h : OnBytes.DgP.digInCall tail call key with
  | none => rfl
  | some t => exact witnessDigitsAreTheSmallnessTests call key t callIsTheShapes h

/-- **The same from the premise on the Script**, at the tail's own shape. tailIsLawful: the library's
`TailOK`: public (`tailOK_Z`, Johnson/HonestTrace/CountsDigits.lean, from `FromPieces`). Conditional on
the premise arrays, which no file shows of any Script. -/
theorem lookupKeyFormsAtDigitsFromTheScript {Bk : ProverCoinCounts} {W Cells Tok : Type}
    {Q : Script Bk W Cells Tok MsgT} {sent : Sent} {letters : K3Letters Cells Tok}
    {valid : W → Prop} {challengesHeard : Nat} {place : PlaceL} {tail : HTailF2}
    {digitsOfTheTrace : W → List Fmt.Drawn → Nat → Nat → Cb.Gl.F}
    (arrays : ScriptHoldsTheDigitArrays Q sent letters valid challengesHeard place tail
      digitsOfTheTrace)
    (tailIsLawful : OnBytes.DgP.TailOK tail) (shapeIsLawful : FoNums.ok tail.f9 = true)
    (k : Coins Bk) {w : W} (isValid : valid w) {heard : List Fmt.Drawn}
    (enough : challengesHeard ≤ heard.length) (theta : OnBytes.Slice.GE) :
    ∀ n, n < 2 ^ tail.f9.v →
      OnBytes.Ends.jointKey tail.f9
        (Cb.Fo.forK Cb.Gl.E
          (OnBytes.DgP.digL5 Cb.Gl.E tail (enOf place.arrays) (mkOf place.arrays) place.F.next Unit)
          ()
          (Cb.Fo.zext (digMu place sent letters.rad
            (fun j => letters.seat place.link true j.1) letters.arr (Q.wit k w heard)))) theta n =
      OnBytes.Ends.jointKey tail.f9 (kvZ tail (inExt (digitsOfTheTrace w heard))) theta n := by
  refine lookupKeyFormsAreTheLibrarysKeysAtDigits sent letters place tail (Q.wit k w heard)
    (digitsOfTheTrace w heard) tail.f9 shapeIsLawful (fun call key t callIsTheShapes h => ?_) theta
  have callBelowTwo : call < 2 := by
    rw [← tailIsLawful.nc]
    exact callIsTheShapes
  obtain ⟨q', c, u⟩ := t
  obtain ⟨_, columnInside, rowInside, _⟩ := OnBytes.DgP.inCall_bwd tailIsLawful callBelowTwo h
  refine arrays.digits k w heard isValid enough u (call * tail.mz + c) rowInside ?_
  have : call * tail.mz ≤ 1 * tail.mz := Nat.mul_le_mul_right _ (Nat.le_of_lt_succ callBelowTwo)
  omega

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupKeyFormsAreTheLibrarysKeysAtDigits
#print axioms ProofFile.Honest.K3.Term.lookupKeyFormsAtDigitsFromTheScript
