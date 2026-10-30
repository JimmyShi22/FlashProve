-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/DoorSocketsFilled.lean: THREE FIELDS OF `TheThreadsHalf` (TheOneObject.lean of
this folder), IN THAT STRUCTURE's OWN FIELD TYPES, at every tied run and at every value of its two
open letters: `doorFive` (the five items with which the last chain's thread begins hold at the
door), `doorTrees` (the trees that the last chain takes over are at hand there) and `doorRides` (the
riders at the last chain's first border hold at the record that the chain's start returns).
Statements with their proofs: calls alone; no definition.

Main names.
  `doorFive_filled`: **the field `doorFive`**, from the maker's return alone:
    `doorFive_at_the_letters_atRun` (DoorAtTheLetters.lean of this folder); that `ready` returns is
    the run's own field.
  `doorTrees_filled`: **the field `doorTrees`**, from the maker's return alone:
    `doorTrees_at_the_letters_atRun` (the same file).
  `doorRides_filled`: **the field `doorRides`**, with no premise: `door_rides_at_letters`
    (AtFullSide/K14/FivesAtTheLetters.lean).

Limits. NOT IN FRONT OF A LAW OVER COINS. Each field is an implication from the two earlier threads'
invariants at their chains' ends: NOTHING HERE SHOWS THAT ANY THREAD STANDS AT ANY RUN. O, P: the
structure's two open letters; P holds propositions, and that a value of P exists is not shown here.
The full size, and the hash function `OnBytes.secondHashFunction`, alone.

What is not claimed. None of these is one of the library's goals. Nothing on soundness, completeness
or hiding.
-/
import AtFullSide.Honest.DoorAtTheLetters
import AtFullSide.Honest.TheOneObject
import AtFullSide.K14.FivesAtTheLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput matrixFilling)
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm AtPublicFiles.Committed AtPublicFiles.TheFalls
open OnBytes.Slice (frS)
open VerifierAndGoals (PublicFiles readFiles)

/- The three instances that the structure's own file gives by hand. -/
local instance (priority := high) nonemptyPadZ_doorSockets : Nonempty PadZ :=
  pads_nonempty frS 402653181

local instance (priority := high) nonemptyRunValue_doorSockets : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_doorSockets : Inhabited RunValue :=
  ⟨fun _ => 0⟩

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)
  {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) {O : TheLetters.OpenShared A}
  (P : TheLetters.OpenLast h O)

/-- **The field doorFive.** -/
theorem doorFive_filled (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) :
    ∀ r : TiedRun h hr, Socket.doorFive h (TheLetters.first h) (TheLetters.reads h)
      (TheLetters.shared h O) (lastParts h (TheLetters.first h) (TheLetters.last h P)) r.R r.x
      (pursesOf r.c) :=
  fun r => doorFive_at_the_letters_atRun h made P r.R r.ready

/-- **The field doorTrees.** -/
theorem doorTrees_filled (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) :
    ∀ r : TiedRun h hr, Socket.doorTrees h (TheLetters.first h) (TheLetters.reads h)
      (TheLetters.shared h O) (lastParts h (TheLetters.first h) (TheLetters.last h P)) r.R
      (pursesOf r.c) :=
  fun r => doorTrees_at_the_letters_atRun h made P r.R r.ready

/-- **The field doorRides.** -/
theorem doorRides_filled :
    ∀ r : TiedRun h hr, Socket.doorRides h (TheLetters.first h) (TheLetters.reads h)
      (TheLetters.shared h O) (lastParts h (TheLetters.first h) (TheLetters.last h P)) r.R r.x
      (pursesOf r.c) :=
  fun r => AtFullSide.K14.door_rides_at_letters h P r.R r.x (pursesOf r.c)

/-- A check by Lean's elaborator that the three have the fields' types: a value of the structure
with these three fields laid anew by the three statements. It takes a value T for the other fields:
so it shows nothing of the others, and is no payment. -/
example (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (T : TheThreadsHalf h hr) : TheThreadsHalf h hr :=
  { T with
    doorFive := doorFive_filled h hr T.open₃ made
    doorTrees := doorTrees_filled h hr T.open₃ made
    doorRides := doorRides_filled h hr T.open₃ }

end AtFullSide.Honest

#print axioms AtFullSide.Honest.doorFive_filled
#print axioms AtFullSide.Honest.doorTrees_filled
#print axioms AtFullSide.Honest.doorRides_filled
