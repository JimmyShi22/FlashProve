-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
A lookup's sums may be written at one input and seated at a half of a wider input: the offline prover's value does so
(`onHalf`, E2E/KeyLookups.lean). The laws on a lookup speak of sums at the narrow input and of a reader into it. Here the two
readings are one row. General in the types. A definition and theorems with proofs.

  `jobsThrough`                     sums at W read at W', through a map from W' to W
  `sumPartReadsThroughAHalf`        at one masked sumcheck: the part at `jobsThrough`, lifted by the reader, is the part at
                                    the sums themselves, lifted by the reader followed by the map
  `ownedSeatReadsThroughAHalf`      **the same of the whole owned seat**

Limits. An equation between two texts of a row. Nothing on whether a part plays or a verifier accepts.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.RowOwned

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Key

variable {V₁ W₁ X₁ W W' : Type}

/-- **Sums at W, read at W'**, through a map from W' to W. -/
def jobsThrough (through : W' → W) (jobs : LookJobs W) : LookJobs W' :=
  ⟨fun s =>
    { round := fun w => (jobs.job s).round (through w)
      inY := fun w => (jobs.job s).inY (through w)
      ends := fun w => (jobs.job s).ends (through w) }⟩

/-- **At one masked sumcheck** the reader may go through the map or the sums may. -/
theorem sumPartReadsThroughAHalf (first second : String) (reads : Reads) (through : W' → W) (jobs : LookJobs W)
    (wit : W₁ → W') (lookup : At) (stage : Stage) (call : VerifiableInference.Desc.Part.MaskedSum.Call) :
    (sumPart (V := Unit) first second (jobOf reads (jobsThrough through jobs) lookup stage call)).lift (V := V₁)
        (X := X₁) (fun _ => ()) wit (fun _ => ()) (fun x _ => x) =
      (sumPart (V := Unit) first second (jobOf reads jobs lookup stage call)).lift (V := V₁) (X := X₁)
        (fun _ => ()) (through ∘ wit) (fun _ => ()) (fun x _ => x) := by
  obtain ⟨lead, summed, ends⟩ := call
  cases ends with
  | none =>
    simp only [Part.lift, sumPart, List.map_append, List.map_map, List.map_cons, List.map_nil]
    rfl
  | some last =>
    simp only [Part.lift, sumPart, List.map_append, List.map_map, List.map_cons, List.map_nil]
    rfl

/-- **THE OWNED SEAT AT SUMS READ THROUGH A MAP IS THE OWNED SEAT AT THE SUMS THEMSELVES**, with the reader followed by the
map. -/
theorem ownedSeatReadsThroughAHalf (owners : Owners) (reads : Reads) (through : W' → W) (jobs : LookJobs W)
    (wit : W₁ → W') (lookup : At) :
    proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) owners reads (jobsThrough through jobs) wit lookup =
      proverSideOfLookupInChain owners reads jobs (through ∘ wit) lookup := by
  unfold proverSideOfLookupInChain lookRowOwned
  congr 1
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro x _
  show Part.lift _ wit _ _ (partOfOwned owners reads (jobsThrough through jobs) lookup x.1 x.2) =
    Part.lift _ (through ∘ wit) _ _ (partOfOwned owners reads jobs lookup x.1 x.2)
  unfold partOfOwned
  cases x.1.call lookup.face with
  | none => rfl
  | some call => exact sumPartReadsThroughAHalf _ _ reads through jobs wit lookup x.1 call

end ProofFile.Honest.K3.Key

#print axioms ProofFile.Honest.K3.Key.sumPartReadsThroughAHalf
#print axioms ProofFile.Honest.K3.Key.ownedSeatReadsThroughAHalf
