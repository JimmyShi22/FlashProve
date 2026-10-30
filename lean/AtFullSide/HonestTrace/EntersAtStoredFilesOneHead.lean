-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/HonestTrace/EntersAtStoredFilesOneHead.lean

It states no goal. No property of the protocol is claimed.

A HEAD AT A RETURN OF THE MAKER IS ONE. "HeadAtReturn files A"
(Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean) is a structure with data: the places, the first chain and
the output head's lookup's place; the first thread reads them. So two theorems of the form "there is a head H at A
with …(firstThread H …)…" could not be joined unless their heads are the same. They are.

Main theorems:
* "headAtReturn_unique": two heads at one return, at the same public files, are equal. General in the files, the
  return and its five types.
* "description_of_head": the description that the maker returned is the head's, at EVERY head at the return.
* "exists_unique_head": so where there is a head at a return there is exactly one.

How. The places are what "H2U.placesOfMade" returns at the return's public part; the first chain is what the maker's own
"chainBy" returns ("IM.Open.unique", Johnson/IMR/SeatOpen.lean); the lookup's place is what "headAt" returns. The
other two fields are propositions.

Limits. It says nothing on whether a head is there. It does not say that a return is one: that follows where the
filling is named, since the maker is a function. Nothing on completeness, soundness, hiding or any other property of
the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Desc.ProofFile.Honest.AtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.HonestTrace.EntersAtStoredFiles

open ProofFile.Honest (OnlineProverWithDescription atPure_at_laid)
open ProofFile.Honest.FirstThread (HeadAtReturn)

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **Two heads at one return are equal.** -/
theorem headAtReturn_unique (first second : HeadAtReturn files A) : first = second := by
  obtain ⟨returned₁, places₁, chain₁, look₁, head₁⟩ := first
  obtain ⟨returned₂, places₂, chain₂, look₂, head₂⟩ := second
  obtain rfl : places₁ = places₂ := Except.ok.inj (head₁.laid.places.symm.trans head₂.laid.places)
  obtain ⟨Bs₁, base₁, opened₁⟩ := head₁.laid.opened
  obtain ⟨Bs₂, base₂, opened₂⟩ := head₂.laid.opened
  obtain rfl : chain₁ = chain₂ := (opened₁.unique opened₂).2.2.2.1
  obtain rfl : look₁ = look₂ := Option.some.inj (head₁.headAt.symm.trans head₂.headAt)
  rfl

/-- **The description that the maker returned is the head's**, at every head at the return. -/
theorem description_of_head (H : HeadAtReturn files A) : A.F = H.description := by
  obtain ⟨filling, made⟩ := H.returned
  exact (atPure_at_laid H.head.laid made).2

/-- Where there is a head at a return there is exactly one. -/
theorem exists_unique_head (H : HeadAtReturn files A) : ∀ other : HeadAtReturn files A, other = H :=
  fun other => headAtReturn_unique other H

end OnBytes.HonestTrace.EntersAtStoredFiles

#print axioms OnBytes.HonestTrace.EntersAtStoredFiles.headAtReturn_unique
#print axioms OnBytes.HonestTrace.EntersAtStoredFiles.description_of_head
#print axioms OnBytes.HonestTrace.EntersAtStoredFiles.exists_unique_head
