-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/FrontSetOwnAt.lean: a value of `FrontSet` (Johnson/Top/FrontSet.lean) that has
EVERY instance, UNDER PREMISES ON THE OBJECT ((i) below; none speaks of a hash), with no set of
requests named and nothing counted: at a spelling whose second string is the request file's bytes.

THE LETTERS MEET; THIS IS NO TIE.

The first chain's statement takes two strings of a request: the value of the item `request`, which
holds the request through a digest of the second hash function, and the request file's bytes. Where
the window is below 2 ^ 32 (hT) and the vocabulary at most 2 ^ 32 (hV') and not empty (hV), two
instances with one request file have one early part (`early_of_requestBytes`,
Johnson/Flat/EarlyApart.lean): so there the pair is one to one on early parts by its second half
alone.

The instances are read through a one-to-one map enc into the model's instances (the identity; or the
value of a sub-type); `he`: the interface's early part is "the reply laid 0".

  `isOwn hV enc x`: the test: the reply of enc x is 0.
  `early_of_isOwn`: what passes it is its own early part.
  `isOwn_early`: every early part passes it.
  `FrontSet.ownRaw`: the general form, UNDER A HYPOTHESIS `hraw`: among the instances that are their
    own early parts and pass a test okI, two with one spelling have one request file.
  `FrontSet.has_ownRaw`: it has i wherever the early part of i passes okI.
  `FrontSet.ownWords item`, `has_ownWords`: at sp x := (item x, the request file's bytes of enc x)
    and okI := always: `hraw` is the equation of the second halves, and the set has every instance.
    item is a letter: nothing is asked of it.

WHAT `hraw` WOULD BE ELSEWHERE. At a spelling that held the request through a digest of the second
hash function alone, `hraw` would say that this hash has no collision among the request files of
these early parts: false by counting where they are more than its values, and given by no proof
below that: a value could then be had only at an okI so narrow that it names a set again (as
`FrontSet.single` does). (An argument in words; no theorem of this library states it.)

WHAT THIS FILE LEAVES OWED FOR THE TEST ON THE FIRST QUERY AT A CALL (`FrontSet.front`), IN ONE
PLACE. (i) The premises at a written object: hT, hV', hV, henc (of a map enc), he, and a test isR
that lets the fixed record alone through (`one`, `self`). (ii) That the page's letter is this
spelling: where a page lays the two strings from an instance's public input (`HoldsPub.req2`,
Johnson/Maker/Page/ReqBoth.lean): another file's; not on this file's ground. (iii) That the call's
request file IS `requestBytesOf` of the call's instance (`insOf_bytes`,
Johnson/Flat/WordsBytes.lean, has it of the instance that `insOf` builds, under the two premises of
`insOf_words` and two on whole words). (iv) The three bounds: on the two strings' sizes and on the
copy's number. (v) `hrest`, `tableSmall` (Johnson/Top/FrontSet.lean).

Not claimed. Any of these five. item is a letter: at use it is meant as the second hash's item, a
fixed public function; laid as a function of the drawn hash function, the spelling and every
encoding made of the set would hang on that function. Nothing on any hash. Nothing on soundness.


-/
import Johnson.Top.FrontSetOwn
import Johnson.Flat.EarlyApart

set_option autoImplicit false

namespace OnBytes.K.Arm.ProofFront

open Iop Inst.Model OnBytes.Flat

variable {I X : Type} {L : HolographicProtocol I X} {r₀ : L.Rec} {P : Params} (hT : P.T < 2 ^ 32)
  (hV' : P.V ≤ 2 ^ 32) (hV : 0 < P.V) (enc : X → Instance' P) (henc : Function.Injective enc)
  (he : ∀ x, enc (L.early x) = withoutReply hV (enc x))

/-- The reply of enc x is 0. -/
def isOwn (x : X) : Bool := decide ((enc x).y = ⟨0, hV⟩)

include henc he in
/-- Under henc and he: what passes the test is its own early part. -/
theorem early_of_isOwn (x : X) (h : isOwn hV enc x = true) : L.early x = x := by
  have e : (enc x).y = ⟨0, hV⟩ := of_decide_eq_true h
  refine henc ((he x).trans ?_)
  unfold withoutReply
  rw [← e]

include he in
/-- Under he: every early part passes the test. -/
theorem isOwn_early (i : X) : isOwn hV enc (L.early i) = true := by
  unfold isOwn
  rw [he]
  exact decide_eq_true rfl

variable {sp : X → ByteArray × ByteArray} (okI : X → Bool) (isR : L.Rec → Bool)
  (one : ∀ r, isR r = true → r = r₀) (self : isR r₀ = true)

/-- **The set of the early parts that pass okI**, under `hraw` and the section's premises (hT, hV',
hV, henc, he; `one`, `self`). -/
def FrontSet.ownRaw
    (hraw : ∀ x y, isOwn hV enc x = true → isOwn hV enc y = true → okI x = true → okI y = true →
      sp x = sp y → requestBytesOf (enc x) = requestBytesOf (enc y)) : FrontSet L sp r₀ :=
  FrontSet.ownEarly (isOwn hV enc) okI (early_of_isOwn hV enc henc he) isR one self
    fun x y a b c d e => henc (((he x).trans
      (early_of_requestBytes hT hV' hV (hraw x y a b c d e))).trans (he y).symm)

/-- **It has i wherever the early part of i passes okI**, under the same. -/
theorem FrontSet.has_ownRaw
    (hraw : ∀ x y, isOwn hV enc x = true → isOwn hV enc y = true → okI x = true → okI y = true →
      sp x = sp y → requestBytesOf (enc x) = requestBytesOf (enc y)) (i : X)
    (h₂ : okI (L.early i) = true) :
    (FrontSet.ownRaw hT hV' hV enc henc he okI isR one self hraw).Has i :=
  FrontSet.has_ownEarly (isOwn hV enc) okI (early_of_isOwn hV enc henc he) isR one self _ i
    (isOwn_early hV enc he i) h₂

/-- **The set of ALL early parts**, under the section's premises (hT, hV', hV, henc, he; `one`,
`self`), at a spelling whose second string is the request file's bytes;
the first string is a letter. `hraw` is the second halves' equation. -/
def FrontSet.ownWords (item : X → ByteArray) :
    FrontSet L (fun x => (item x, requestBytesOf (enc x))) r₀ :=
  FrontSet.ownRaw hT hV' hV enc henc he (fun _ => true) isR one self
    fun _ _ _ _ _ _ e => congrArg Prod.snd e

/-- **It has every instance**, under the section's hT, hV', hV, henc, he, `one`, `self`. -/
theorem FrontSet.has_ownWords (item : X → ByteArray) (i : X) :
    (FrontSet.ownWords hT hV' hV enc henc he isR one self item).Has i :=
  FrontSet.has_ownRaw hT hV' hV enc henc he (fun _ => true) isR one self _ i rfl

end OnBytes.K.Arm.ProofFront

#print axioms OnBytes.K.Arm.ProofFront.early_of_isOwn
#print axioms OnBytes.K.Arm.ProofFront.isOwn_early
#print axioms OnBytes.K.Arm.ProofFront.FrontSet.has_ownRaw
#print axioms OnBytes.K.Arm.ProofFront.FrontSet.has_ownWords
