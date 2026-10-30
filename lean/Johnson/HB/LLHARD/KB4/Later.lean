-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/Later.lean: the key file's three chains as functions of just what they read.
General: no value is treated.

Key.descriptionFromSource (Johnson/Desc/Key/Desc.lean) makes its first chain of the one-time chain's values as read
back, and its two later chains of what the planner holds of all seven chains. Of these values the
chains read a few fields. Here each chain is shown to be the same chain at a value that holds these
fields alone: by unfolding.

Main names.
  oneAt a im x co S: a one-time chain's values with the number of answers, the index-mask message's
  notice, the item "ranges", the codes and the shape; no bytes, no digest, no item, no entry.
  firstChain_at: Key.firstChain at any values is Key.firstChain at oneAt of their five fields.
  parZ, sharedZ, thirdZ: the texts of Key.sharedPar, Key.sharedChain and Key.thirdChain with the
  sized key z, and the front's answer, as letters. sharedChain_eq, thirdChain_eq.
Limits. Equations between descriptions' parts alone. Nothing on soundness.

-/
import Johnson.Desc.Key.Desc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params OnBytes.Plan

/-- A one-time chain's values that hold just what the first chain reads. -/
def oneAt (a : Nat) (im : OracleNotice) (x : WfPublic) (co : Codes) (S : LinShape) : OneTime :=
  ⟨⟨.empty, ⟨.two, 0, 0, 0, a, 0, []⟩, .empty, []⟩, im, x, ⟨0, 0⟩, co, S⟩

theorem firstChain_at (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
    (set : Setting) (N : H2U.PlaceNums) :
    firstChain one D told set N =
      firstChain (oneAt one.given.plan.samples one.indexMasks one.ranges one.codes one.lin)
        D told set N := rfl

/-- Key.sharedPar's text at the sized key. -/
def parZ (z : KeySized) (beforePoint : List (Nat × Nat)) : _root_.Desc.K14.P14 :=
  { set := z.set, scope := if z.once.lines.oneTime then .once else .shared, codes := z.codes,
    S := z.once.shape, item := 0, beforePoint := beforePoint }

/-- Key.sharedChain's text at the sized key and the front's answer. -/
def sharedZ (z : KeySized) (front : Bool) (N : LaterPlaces) : Chain _root_.Desc.K14.St Unit :=
  let inFront := _root_.Desc.K14.blocksOr (parZ z (beforeSharedPoint N)) ++ sharedTests N
  { first := { roundlessBlock "the shared chain's front" 2 none 0 .ok with planOk := front }
    front := [], links := [], back := inFront
    last := VerifiableInference.Desc.K12.Seat.last inFront }

theorem sharedChain_eq (c : Model.Verify.Chains) (N : LaterPlaces) :
    sharedChain c N = sharedZ c.made.sized.key (sharedFrontOk c) N := rfl

/-- Key.thirdChain's text at the sized key. -/
def thirdZ (z : KeySized) (N : LaterPlaces) : Chain VerifiableInference.Desc.Third.S₃ Unit :=
  VerifiableInference.Desc.Third.lastChainWithOwnTest
    (VerifiableInference.Desc.Third.p₁₄Z z.set z.codes z.once) (ownTest N)

theorem thirdChain_eq (c : Model.Verify.Chains) (N : LaterPlaces) :
    thirdChain c N = thirdZ c.made.sized.key N := rfl

end Johnson.KB4

#print axioms Johnson.KB4.firstChain_at
#print axioms Johnson.KB4.sharedChain_eq
#print axioms Johnson.KB4.thirdChain_eq
