-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/BlocksAt.lean: the one hypothesis on a number that the tie of the entry file's arm asks
at the three files' own wiring, `KFullAt G + 1 < 2 ^ 48` | `KSmallAt G + 1 < 2 ^ 48`
(Johnson/Flat/WireAt.lean), led back to two tests on the rounds of the key file and of the proof
file.

Statements and proofs. `KFullAt G` is a maximum of five numbers: the greatest number of blocks that
a round of the key file's data asks, of the entry's rounds, of the proof file's data; the entry's
description's own number; the seed's blocks. Three of the five are closed terms, evaluated by Lean's
kernel (OnBytes/Flat/BlocksBelow.lean). The other two hang on G.

Main names (the small size has Small for Full):
  `KFullAt_lt_iff`: KFullAt G + 1 < 2 ^ 48 ↔ BlocksFit .two (dataKFull G) ∧
    BlocksFit .two (dataPFull G), where `BlocksFit f D` says of every round of D's three chains that
    its number of blocks and one more stay below 2 ^ 48.
  `KFullAt_lt_of_tests`: from the two tests `blocksFitB`.
  `blocksFit_KFull_of_not`, `blocksFit_PFull_of_not`: where a maker's guard fails, that file's data
    are those of three empty lists, and the test holds for nothing.

Limits: G is a letter: the two tests are shown at no G. None of the makers' eight tests on the dry
runs (`okAt`, OnBytes/Maker/Files.lean) bounds a round's draws: so the hypothesis does not follow
from them. Nothing on soundness, on bytes or files.


-/
import Johnson.Flat.WireAt
import OnBytes.Flat.BlocksBelow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice OnBytes.Maker _root_.Run

section
variable {X : Type} (G : FilesParameters X RecFull)

/-- **The one wiring's number of blocks and one more stay below 2 ^ 48 exactly if that holds of
every round of the key file's data and of the proof file's.** The entry's rounds, the entry's
description's own number and the seed's blocks are closed terms, evaluated by Lean's kernel. -/
theorem KFullAt_lt_iff :
    KFullAt G + 1 < 2 ^ 48 ↔ BlocksFit .two (dataKFull G) ∧ BlocksFit .two (dataPFull G) := by
  have h1 := kThree_lt_iff .two (dataKFull G) frRds (dataPFull G)
  have h2 := entryFull_blocks
  have h3 := descFull_blocks
  have h4 := seedFull_blocks
  unfold KFullAt
  constructor
  · intro h
    have h5 : kThree .two (dataKFull G) frRds (dataPFull G) + 1 < 2 ^ 48 := by omega
    exact ⟨(h1.1 h5).1, (h1.1 h5).2.2⟩
  · intro h
    have h5 := h1.2 ⟨h.1, h2, h.2⟩
    omega

/-- As two tests. -/
theorem KFullAt_lt_of_tests (hK : blocksFitB .two (dataKFull G) = true)
    (hP : blocksFitB .two (dataPFull G) = true) : KFullAt G + 1 < 2 ^ 48 :=
  (KFullAt_lt_iff G).2 ⟨(blocksFitB_iff _ _).1 hK, (blocksFitB_iff _ _).1 hP⟩

/-- Where the key file's guard fails its data are empty, and the test holds for nothing. -/
theorem blocksFit_KFull_of_not
    (h : ¬ okAt frS.P.T.a (dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀)) = true) :
    BlocksFit .two (dataKFull G) := by
  rw [dataKFull_empty G h]
  intro d hd
  cases hd

/-- The same for the proof file. -/
theorem blocksFit_PFull_of_not
    (h : ¬ okAt frS.P.T.a
      (dryProof G.c (keyOf (fun β : NZ => β.val) G.z₀.2) (G.block G.z₀.1)) = true) :
    BlocksFit .two (dataPFull G) := by
  rw [dataPFull_empty G h]
  intro d hd
  cases hd

end

section
variable {X : Type} (G : FilesParameters X RecSmall)

/-- **The one wiring's number of blocks and one more stay below 2 ^ 48 exactly if that holds of
every round of the key file's data and of the proof file's.** The entry's rounds, the entry's
description's own number and the seed's blocks are closed terms, evaluated by Lean's kernel. -/
theorem KSmallAt_lt_iff :
    KSmallAt G + 1 < 2 ^ 48 ↔ BlocksFit .two (dataKSmall G) ∧ BlocksFit .two (dataPSmall G) := by
  have h1 := kThree_lt_iff .two (dataKSmall G) srRds (dataPSmall G)
  have h2 := entrySmall_blocks
  have h3 := descSmall_blocks
  have h4 := seedSmall_blocks
  unfold KSmallAt
  constructor
  · intro h
    have h5 : kThree .two (dataKSmall G) srRds (dataPSmall G) + 1 < 2 ^ 48 := by omega
    exact ⟨(h1.1 h5).1, (h1.1 h5).2.2⟩
  · intro h
    have h5 := h1.2 ⟨h.1, h2, h.2⟩
    omega

/-- As two tests. -/
theorem KSmallAt_lt_of_tests (hK : blocksFitB .two (dataKSmall G) = true)
    (hP : blocksFitB .two (dataPSmall G) = true) : KSmallAt G + 1 < 2 ^ 48 :=
  (KSmallAt_lt_iff G).2 ⟨(blocksFitB_iff _ _).1 hK, (blocksFitB_iff _ _).1 hP⟩

/-- Where the key file's guard fails its data are empty, and the test holds for nothing. -/
theorem blocksFit_KSmall_of_not
    (h : ¬ okAt srS.P.T.a (dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀)) = true) :
    BlocksFit .two (dataKSmall G) := by
  rw [dataKSmall_empty G h]
  intro d hd
  cases hd

/-- The same for the proof file. -/
theorem blocksFit_PSmall_of_not
    (h : ¬ okAt srS.P.T.a
      (dryProof G.c (keyOf (fun β : NZ => β.val) G.z₀.2) (G.block G.z₀.1)) = true) :
    BlocksFit .two (dataPSmall G) := by
  rw [dataPSmall_empty G h]
  intro d hd
  cases hd

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.KFullAt_lt_iff
#print axioms VerifiableInference.OnPublicFiles.KSmallAt_lt_iff
#print axioms VerifiableInference.OnPublicFiles.KFullAt_lt_of_tests
#print axioms VerifiableInference.OnPublicFiles.KSmallAt_lt_of_tests
