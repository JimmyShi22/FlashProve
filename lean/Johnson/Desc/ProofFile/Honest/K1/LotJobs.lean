-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/LotJobs.lean: THE JOBS AT THE PLACES OF K1's LOT, AS A LIST: A
SECOND TEXT OF THE ENUMERATION IN lotHalves (Honest/K1/PlaceJob.lean), TIED TO ITS FIRST AT ONCE:
lotHalves is placeHalf over lotJobs. What it is for: the list of named tests k1Asks
(Honest/K1/SeatedAsks.lean) takes jobs, and lotHalves hands halves. One definition, one statement
and its proof. No filling calls it.

  lotJobs          the jobs, in the order and by the very terms of lotHalves
  lotHalves_jobs   lotHalves is placeHalf over lotJobs

Limits. W's sending is not among them: its data are another file's. It lays nothing anew: each job
is lotHalves' own term with "placeHalf wit" taken off. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc

variable {Xi X V W : Type}

/-- **The jobs at the places of K1's lot**, in the order and by the very terms of lotHalves: the
first segment's opening; then for each link its reads and its digits. -/
def lotJobs (no : Place → Nat) (D : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) :
    List (SendJob (PlaceIn Xi) X) :=
  placeJob (K1.firstPar G.first (K1.gpOf Z)) (no ⟨1, some 0, 1, .K1⟩) (firstFold G.first)
      (D Z G) ::
    G.built.toList.zipIdx.flatMap fun (Y, l) =>
      match K1.linkNumbers G Y with
      | none => []
      | some (pr, pd, _, _) =>
        [laterJobAt G.first (K1.gpOf Z) l pr 1 (no ⟨1, some l, pr, .K1⟩) (D Z G),
         laterJobAt G.first (K1.gpOf Z) l pd 2 (no ⟨1, some l, pd, .K1⟩) (D Z G)]

/-- lotHalves is placeHalf over lotJobs. -/
theorem lotHalves_jobs (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) :
    lotHalves (V := V) (X := X) wit no D Z G = (lotJobs no D Z G).map (placeHalf wit) := by
  unfold lotHalves lotJobs
  rw [List.map_cons, List.map_flatMap]
  congr 1
  refine List.flatMap_congr fun x _ => ?_
  obtain ⟨Y, l⟩ := x
  dsimp only
  cases K1.linkNumbers G Y with
  | none => rfl
  | some q => rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.lotJobs
#print axioms ProofFile.Honest.K1.lotHalves_jobs
