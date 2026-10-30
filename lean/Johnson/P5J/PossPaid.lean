-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/PossPaid.lean: THE NAMED TEST "poss" OF PlanOk (for every group from 1 to the number of segments a code switch stands among the first chain's sub-protocols) IS A CLOSED FACT ON THE WRITTEN LIST OF PLACES. One definition, three theorems.
  possP ps n: the same test, read off a list of places · possThere_places: possThereB bs n = possP (blockPlaces bs) n: the test reads the sub-protocols' places alone · possP_written: at the written list (At.ps) and the written number of segments it accepts: BY THE KERNEL · At.poss_paid: so, where the first chain's sub-protocols' places ARE the written list, "poss" holds.
Limits. That the places are the written list is the premise (in scope: other files' theorems). The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.PlanOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open VerifiableInference.Desc (Chain Block Place)
open VerifiableInference.Desc.First (possThereB blockPlaces)

/-- The test, off a list of places. -/
def possP (l : List Place) (n : ℕ) : Bool :=
  (List.range n).all fun i => (l.find? fun p => p.kind == .K2 && p.link.getD n == i + 1).isSome

/-- **The test reads the places alone.** -/
theorem possThere_places {St Cl : Type} (bs : List (Block St Cl)) (n : ℕ) :
    possThereB bs n = possP (blockPlaces bs) n := by
  unfold possThereB possP blockPlaces
  congr 1
  funext i
  rw [List.find?_map, Option.isSome_map]
  rfl

/-- **At the written list it accepts**: by the kernel. -/
theorem possP_written : possP ps links.length = true := by decide +kernel

/-- **"poss" holds where the sub-protocols' places are the written list.** -/
theorem poss_paid (cF : Chain TS ProofFile.Cl) (h : blockPlaces cF.blocksInOrder = ps) :
    possThereB cF.blocksInOrder links.length = true := by
  rw [possThere_places, h]
  exact possP_written

end P5J.At

#print axioms P5J.At.possThere_places
#print axioms P5J.At.possP_written
#print axioms P5J.At.poss_paid
