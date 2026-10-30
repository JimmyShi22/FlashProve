-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/FallNumbers.lean: THE SMALLNESS TEST: THE STATED NUMBERS OF ITS TWO
FALLS AT A SEGMENT OF THE FULL SIZE, AS FUNCTIONS WITH CODE OF THE PUBLIC PART, THE GROUND AND THE
SEGMENT's NUMBER. DEFINITIONS ALONE: CODE IN THIS FILE, LAWS IN OTHERS, so that whoever names a
number imports no law's ground. NO LAW IS STATED HERE, AND NONE OF THE LIBRARY's GOALS. NO NUMBER
HERE IS HELD AGAINST ITS TEST.

  `k8ColsAt G l`, `k8TauAt G l` the two numbers of which the first fall's stated share is made
                   (`k8FrontFall`, Johnson/Desc/ProofFile/Honest/K8/Falls.lean): the columns of all
                   matrices of the built segment number l; its number of combinations
  `shareCount nU tl rows` how many values of the batching element the second fall's sentence counts
  `k8CountShare nU tl rows` that count as a stated share
  `k8ShareAt Z G l` the same at the built segment number l and the batching's numbers there
THE LAWS: on the first two: Johnson/Desc/ProofFile/Honest/K8/FrontNumbers.lean; on the other three:
Johnson/P1K8R/ShareStated.lean.
FOUR COUNTS ARE WRITTEN OUT IN PLACE, since the definitions that name them stand in files with laws:
the sum in `k8ColsAt` is `cols` (Johnson/Desc/ProofFile/Honest/K8/FrontCount.lean); in `shareCount`,
in its order: `linkedCount` (Johnson/Desc/K8/Honest/LinkedFew.lean) · `symCount` (SymbolsFew.lean) ·
`secondN` (SecondFew.lean). That each is the named count is said in the files of laws, by rfl.
Limits. WHERE A LOOK-UP LACKS the first two say 0 and the last says 0 of 1: FILLERS, NO CLAIM. It
stands over one file of the frame (Johnson/Desc/ProofFile/Honest/Frame.lean: `Odds`).
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Frame
import Johnson.Desc.ProofFile.Lot.K8
import Johnson.IMR.LinkSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model

/-- The columns of all matrices of the built segment number l. -/
def k8ColsAt (G : ProofFile.Ground) (l : Nat) : Nat :=
  ((G.built[l]?).map fun X => ∑ mu ∈ Finset.range X.tl.NM, (X.tl.mats.getD mu {}).k).getD 0

/-- Its number of combinations. -/
def k8TauAt (G : ProofFile.Ground) (l : Nat) : Nat := ((G.built[l]?).map fun X => X.tl.tau).getD 0

end ProofFile.Honest.K8

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open ProofFile.Honest (Odds)

/-- **How many values of the batching element the second fall's sentence counts**, at a segment's
planned numbers: nU: the plan's lengths of the vectors of reads; tl: the planned data of the
smallness test; rows: the rows that the batching's entry counts. The six summands are those of
`share_fallDebt_last` (Johnson/P1K8R/BehindLast.lean), in its order. -/
def shareCount (nU : Array Nat) (tl : HTailF2) (rows : Nat) : Nat :=
  nU.getD 2 0 * (rows - 1) + (2 * (tl.zzBlocks * tl.mz) * (rows - 1) +
    ((2 * tl.mz + ∑ mu ∈ Finset.range tl.NM, 2 * (tl.mats.getD mu {}).m) * (rows - 1) +
      (3 * tl.bzColumns * (rows - 1) +
        ((∑ mu ∈ Finset.range tl.NM, (tl.shp.getD mu {}).J * (tl.shp.getD mu {}).k) * (rows - 1) +
          (1 + ∑ mu ∈ Finset.range tl.NM,
            (1 + ∑ k ∈ Finset.range (tl.shp.getD mu {}).mS, tl.stepF * k))))))

/-- **A STATED NUMBER FOR THE SECOND FALL: THE ONE THAT IS COUNTED**: `shareCount` of the p ^ 3
elements of the extension field, times ((2 ^ 128 + 1) / 2 ^ 128) ^ 3, written as two natural
numbers, as `frontFallShare` (Johnson/Desc/ProofFile/Honest/K8/Falls.lean) is. -/
def k8CountShare (nU : Array Nat) (tl : HTailF2) (rows : Nat) : Odds :=
  ⟨shareCount nU tl rows * (2 ^ 128 + 1) ^ 3, Code.pGold ^ 3 * 2 ^ 384⟩

/-- **The same as a function of the segment's number alone**: at the built segment of that number
and the batching's numbers there (IM.k9At, Johnson/IMR/LinkSeat.lean); 0 of 1 where either lacks. -/
def k8ShareAt (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) : Odds :=
  match G.built[l]?, IM.k9At Z l with
  | some X, some p => k8CountShare (ProofFile.k8ParW Z G X l).nU X.tl p.rows
  | _, _ => ⟨0, 1⟩

end P1K8

#print axioms ProofFile.Honest.K8.k8ColsAt
#print axioms ProofFile.Honest.K8.k8TauAt
#print axioms P1K8.shareCount
#print axioms P1K8.k8CountShare
#print axioms P1K8.k8ShareAt
