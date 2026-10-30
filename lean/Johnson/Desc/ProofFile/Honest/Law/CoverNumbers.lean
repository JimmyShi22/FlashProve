-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/CoverNumbers.lean: the numbers of the canonical gates
(`coverGates`, Honest/Law/CoverChain.lean) are the letter `p` at the sub-protocols' numbers. They do
not depend on the falls, the marks, the data, or what the chain's walk starts from.

  1  `coverGates_p`   the list of the gates' numbers

Limits.
  * A fact on one definition of this folder. No description and no prover is named.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open scoped ENNReal
open VerifiableInference.Desc (Block)
open OnBytes.Maker (RDT)

variable {S Cl W Y : Type}

section
variable (all : List (Block S Cl)) (fs : List (Fall S)) (ms : List Mark) (skip : Nat)
  (X : List Fmt.Drawn → ChainAt S Cl W Y) (p : Nat → ℝ≥0∞) (tail : List Fmt.Drawn)

/-- The canonical gates' numbers are the letter p at the members' numbers: whatever the walk starts
from, the falls, the marks and the data are. -/
theorem coverGates_p : ∀ (bs : List (Block S Cl)) (j n : Nat) (ds : List RDT),
    (coverGates all fs ms skip X p tail bs j n ds).map (·.p) =
      (List.range bs.length).map fun i => p (j + i)
  | [], _, _, _ => rfl
  | [_], _, _, _ => rfl
  | b :: b' :: bs, j, n, ds => by
    show p j :: (coverGates all fs ms skip X p tail (b' :: bs) (j + 1) (n + b.rounds.length)
      (ds.drop b.rounds.length)).map (·.p) =
        (List.range ((b' :: bs).length + 1)).map fun i => p (j + i)
    rw [coverGates_p (b' :: bs) _ _ _, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine congrArg (p j :: ·) (List.map_congr_left fun i _ => ?_)
    show p (j + 1 + i) = p (j + (i + 1))
    rw [Nat.add_assoc, Nat.add_comm 1 i]

end

end ProofFile.Honest

#print axioms ProofFile.Honest.coverGates_p
