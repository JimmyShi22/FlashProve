-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/Doors.lean: the three doors by which a filling of the
honest prover (`OnlineProverParts`, Johnson/Desc/ProofFile/Honest/AtPure.lean) takes the half of a proximity test
(the kind K12), general in the job; and the bare job, a stand-in of public numbers. Definitions with
code; no theorem. The definitions stood in Bare.lean in this folder, which now imports this file:
here they stand over Parts.lean and AtPure.lean alone, so that a lot can be laid without the shared
chain's files beneath it.

A BARE HALF IS NOT TO BE LAID INTO A FILLING THAT IS PLAYED, COUNTED OR OF RECORD. It is a stand-in
for a test of the laying: no honest prover's side. Why, and what it does where it is laid all the
same: the head of Bare.lean.

  `idleT12`, `idlePS`   a verifier's state and a first stage's state that hold nothing
  `bareJob`      the bare job: a place's numbers, the group's members, the word on the fresh table;
                 its three functions are idle
  `sharedOf`     the door `OnlineProverParts.shared`: the halves of two jobs, each where it is made
  `lotOf`        the door `OnlineProverParts.lots`: the honest side of the first chain's lot of the kind, under
                 that lot's own name (Johnson/Desc/ProofFile/Lot/K12.lean)
  `secondOf`     the door `OnlineProverParts.second`
  `withShared`   a filling with more halves appended to its shared chain's list

Limits. The doors take any job and compare it with nothing. Nothing on completeness, soundness or
hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Parts
import Johnson.Desc.ProofFile.Honest.AtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc.K12 (P12 T12)
open Johnson.Prover.Link (PS)

variable {V W X W₀ Rc Tr X₀ : Type}

/-- A verifier's state that holds nothing. -/
def idleT12 : T12 :=
  { st := default, book := default, roots := 0, g := 0, pass := .nothing, mask := none }

/-- A first stage's state that holds zeros. -/
def idlePS : PS :=
  ⟨fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => 0,
    fun _ => 0⟩

/-- **The bare job.** -/
def bareJob (p : P12) (members : List (Addr × Nat × Due)) (fresh : Option (Addr × Nat)) :
    TestJob W X :=
  { p := p, members := members, fresh := fresh
    rec₀ := fun _ _ => idleT12, rows₀ := fun _ _ _ => idlePS, trees₀ := fun _ _ _ _ => [] }

/-- **The door `OnlineProverParts.shared`.** -/
def sharedOf (jU jO : Pub → Option (TestJob W X)) (Z : Pub) : List (Placed V W X) :=
  ((jU Z).toList ++ (jO Z).toList).map proverSideOfProximityTest

/-- **The door `OnlineProverParts.lots`.** -/
def lotOf (j : Pub → Ground → Option (TestJob W X)) : HLot V W X :=
  { name := "the proximity test at F:2 (K12)"
    halves := fun Z G => (j Z G).toList.map proverSideOfProximityTest }

/-- **The door `OnlineProverParts.second`.** -/
def secondOf (j : Pub → Ground → Option (TestJob W X)) (Z : Pub) (G : Ground) :
    List (Placed V W X) :=
  (j Z G).toList.map proverSideOfProximityTest

/-- A filling with more halves in the shared chain, behind those that it has. -/
def withShared (P : OnlineProverParts W₀ Rc Tr X₀ X)
    (more : Pub → List (Placed Empty (Common W₀ Rc OnBytes.TableKey) X₀)) :
    OnlineProverParts W₀ Rc Tr X₀ X :=
  { P with shared := fun Z G => P.shared Z G ++ more Z }

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.idleT12
#print axioms ProofFile.Honest.K12.AtProof.idlePS
#print axioms ProofFile.Honest.K12.AtProof.bareJob
#print axioms ProofFile.Honest.K12.AtProof.sharedOf
#print axioms ProofFile.Honest.K12.AtProof.lotOf
#print axioms ProofFile.Honest.K12.AtProof.secondOf
#print axioms ProofFile.Honest.K12.AtProof.withShared
