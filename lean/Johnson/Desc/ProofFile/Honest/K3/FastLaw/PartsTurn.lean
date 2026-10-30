-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/FastLaw/PartsTurn.lean: at a lookup with several parts of keys,
every stage but two IS a stage of a lookup with one part. Definitions of four turns, and equations
that hold by unfolding.

The matter. Honest/K3/FastLaw/All.lean joins the two fillings of a lookup's summands at ONE part of
keys. The folding filling (`fastJobs`, Honest/K3/JobsFast.lean) is written for any number of parts;
the specification's filling at parts is `Parts.specJobsPAt` (Honest/K3/Parts/Jobs.lean). No level is
proved a second time: a level of part i's tree, at a face f, an input w and points p, is the same
level of part 0's tree at the face, the input and the points TURNED to part i; and the stages that
read no key (the tie's later steps, the table side, the leaves, the bits) are those of the face with
one part laid in the parts' stead.

  `turnF`, `turnW`, `turnP`   face, input, points turned to part i: what was part i's is part 0's,
                             and the face has that part alone
  `oneF`                     the face with one part of two keys: for the stages that read no key
  `fast_key_*`, `spec_key`     a level of part i's tree, in both fillings
  `fast_free_*`, `spec_free`   a stage that reads no key, in both fillings
  `KeyFree`                  which stages these are

Limits. Equations between terms; nothing is said on what the terms come to. The two stages that are
left, the parts' step and the tie's first step, are Honest/K3/FastLaw/PartsAll.lean's.
Nothing on any property of the protocol.

-/
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.All
import Johnson.Desc.ProofFile.Honest.K3.Parts.Jobs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.FastLaw
open OnBytes (E)
open ProofFile.Honest.K3.Parts (specJobsPAt dataP)

/-! ## 1 The turns -/

/-- The face with part i alone, as its part 0. -/
def turnF (f : LFace) (i : Nat) : LFace :=
  { f with parts := [f.parts.getD i 0], orders := fun _ => f.orders i }

/-- The input whose every part's keys are part i's. -/
def turnW (w : Hidden) (i : Nat) : Hidden := { w with key := fun theta _ x => w.key theta i x }

/-- The points whose every part's key points are part i's. -/
def turnP (p : Pts) (i : Nat) : Pts := { p with keyPt := fun _ m => p.keyPt i m }

/-- The face with one part of two keys. -/
def oneF (f : LFace) : LFace := { f with parts := [1] }

/-- The stages that read no key. -/
def KeyFree : Stage → Prop
  | .tie (_ + 1) => True
  | .tab _ => True
  | .leaves => True
  | .bits => True
  | _ => False

section
variable (f : LFace) (row : E → Nat → E) (pads : List (Nat × Nat)) (w : Hidden) (p : Pts)

/-! ## 2 A level of part i's tree -/

theorem fast_key_round (i m : Nat) (rs : List E) :
    ((fastJobs f row).job (.key i m)).round w p rs =
      ((fastJobs (turnF f i) row).job (.key 0 m)).round (turnW w i) (turnP p i) rs := rfl

theorem fast_key_ends (i m : Nat) (rs : List E) :
    ((fastJobs f row).job (.key i m)).ends w p rs =
      ((fastJobs (turnF f i) row).job (.key 0 m)).ends (turnW w i) (turnP p i) rs := rfl

theorem fast_key_inY (i m : Nat) (rs mk : List E) :
    ((fastJobs f row).job (.key i m)).inY w p rs mk =
      ((fastJobs (turnF f i) row).job (.key 0 m)).inY (turnW w i) (turnP p i) rs mk := rfl

/-- Part i's data are the data at one key vector, at the turned face, input and points. -/
theorem part_turn (i : Nat) :
    (dataP (numsOf f row pads) f.parts f.orders w p).part i =
      dataAt (numsOf (turnF f i) row pads) (turnW w i) (turnP p i) := rfl

theorem spec_key_round (i m : Nat) (rs : List E) :
    ((specJobsPAt f row pads).job (.key i m)).round w p rs =
      ((specJobsAt (turnF f i) row pads).job (.key 0 m)).round (turnW w i) (turnP p i) rs := rfl

theorem spec_key_ends (i m : Nat) (rs : List E) :
    ((specJobsPAt f row pads).job (.key i m)).ends w p rs =
      ((specJobsAt (turnF f i) row pads).job (.key 0 m)).ends (turnW w i) (turnP p i) rs := rfl

theorem spec_key_inY (i m : Nat) (rs mk : List E) :
    ((specJobsPAt f row pads).job (.key i m)).inY w p rs mk =
      ((specJobsAt (turnF f i) row pads).job (.key 0 m)).inY (turnW w i) (turnP p i) rs mk := rfl

/-! ## 3 A stage that reads no key -/

/-- The tables that read no key are those of the face with one part. -/
theorem src_free (theta alpha : E) :
    (Fast.srcOf f row w theta alpha).tabLvl = (Fast.srcOf (oneF f) row w theta alpha).tabLvl ∧
    (Fast.srcOf f row w theta alpha).bitTab = (Fast.srcOf (oneF f) row w theta alpha).bitTab ∧
    (Fast.srcOf f row w theta alpha).facTab = (Fast.srcOf (oneF f) row w theta alpha).facTab :=
  ⟨rfl, rfl, rfl⟩

theorem fast_free (s : Stage) (hs : KeyFree s) :
    (fastJobs f row).job s = (fastJobs (oneF f) row).job s := by
  cases s with
  | tie j =>
    cases j with
    | zero => exact absurd hs (by simp [KeyFree])
    | succ j => simp only [fastJobs, Fast.stageJob, Fast.srcOf, oneF]
  | tab l => simp only [fastJobs, Fast.stageJob, Fast.levelJob, Fast.srcOf, oneF]
  | leaves =>
    simp only [fastJobs, Fast.stageJob, Fast.srcOf, oneF]
    rfl
  | bits => simp only [fastJobs, Fast.stageJob, Fast.srcOf, oneF]
  | shift => exact absurd hs (by simp [KeyFree])
  | alpha => exact absurd hs (by simp [KeyFree])
  | split i => exact absurd hs (by simp [KeyFree])
  | join => exact absurd hs (by simp [KeyFree])
  | key i m => exact absurd hs (by simp [KeyFree])
  | keyLine i m => exact absurd hs (by simp [KeyFree])
  | tabLine l => exact absurd hs (by simp [KeyFree])
  | zero => exact absurd hs (by simp [KeyFree])

theorem spec_free (s : Stage) (hs : KeyFree s) :
    (specJobsPAt f row pads).job s = (specJobsAt (oneF f) row pads).job s := by
  cases s with
  | tie j =>
    cases j with
    | zero => exact absurd hs (by simp [KeyFree])
    | succ j => rfl
  | tab l => rfl
  | leaves => rfl
  | bits => rfl
  | shift => rfl
  | alpha => rfl
  | split i => exact absurd hs (by simp [KeyFree])
  | join => rfl
  | key i m => exact absurd hs (by simp [KeyFree])
  | keyLine i m => rfl
  | tabLine l => rfl
  | zero => rfl

end

end ProofFile.Honest.K3.FastLaw

#print axioms ProofFile.Honest.K3.FastLaw.fast_key_round
#print axioms ProofFile.Honest.K3.FastLaw.fast_key_ends
#print axioms ProofFile.Honest.K3.FastLaw.fast_key_inY
#print axioms ProofFile.Honest.K3.FastLaw.part_turn
#print axioms ProofFile.Honest.K3.FastLaw.spec_key_round
#print axioms ProofFile.Honest.K3.FastLaw.spec_key_ends
#print axioms ProofFile.Honest.K3.FastLaw.spec_key_inY
#print axioms ProofFile.Honest.K3.FastLaw.src_free
#print axioms ProofFile.Honest.K3.FastLaw.fast_free
#print axioms ProofFile.Honest.K3.FastLaw.spec_free
