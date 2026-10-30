-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/PlaceQuiet.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME
FOR THE HONEST SIDE: AT A LINK's READS THE LOT's MEMBER, WITH ITS QUIET STEP JOINED, HAS THE ROUNDS,
ORACLE MESSAGES AND PLACE OF THE JOB's P. One statement and its proof.

  reads_member  the reads' place's block as the kind's lot ProofFile.k1Pure joins it (IM.k1Reads,
                Johnson/IMR/K1Seat.lean: K1's own block with the quiet block IM.k1Quiet behind it):
                its rounds, oracle messages and place are those of laterJobAt's P
                (Honest/K1/PlaceJob.lean)

By joined_rounds, whose two premises are the library's rounds_k1Quiet
(Johnson/Desc/K1/Law/BlocksAtLater.lean) and oracles_k1Quiet
(Johnson/Desc/K1/Law/QuietTellsNothing.lean).

Limits. THE LOT's BLOCK, NOT A DESCRIPTION's: what the lot's own blocks are is the library's
IM.k1_mem's to say; which block stands at the place in a description's chain, where it is carried
over by Block.retype, IM.k1_later's and IM.k1_reads_layers' (all three: Johnson/IMR/K1Seat.lean):
not this file's. Nothing on what the quiet step decides. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob
import Johnson.Desc.K1.Law.BlocksAtLater
import Johnson.Desc.K1.Law.QuietTellsNothing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc

variable {X Xi : Type}

theorem reads_member (Z : Pub) (G : Ground) (l : Nat) (Y : OnBytes.Model.Stages.LinkH) (pr : Nat)
    (reads : Option (List Nat)) (first : Nat) (D : RowDataOf Xi) :
    (IM.k1Reads Z G l Y pr reads).rounds =
        K1.rounds (laterJobAt (X := X) G.first (K1.gpOf Z) l pr 1 first D).P ∧
      (IM.k1Reads Z G l Y pr reads).oracles =
        K1.oracles (laterJobAt (X := X) G.first (K1.gpOf Z) l pr 1 first D).P ∧
      (IM.k1Reads Z G l Y pr reads).place =
        (laterJobAt (X := X) G.first (K1.gpOf Z) l pr 1 first D).P.place :=
  joined_rounds G.first (K1.gpOf Z) l pr 1 first D reads (IM.k1Quiet G l Y)
    (K1.rounds_k1Quiet G l Y) (K1.oracles_k1Quiet G l Y)

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.reads_member
