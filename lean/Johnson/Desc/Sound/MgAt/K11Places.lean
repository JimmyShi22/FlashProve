-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K11Places.lean: the seven closed premises on the two places that merge_t2
(Johnson/Top/H0/MergeLaw/TieOneTwo.lean) leaves, at the full size's written lists: links :=
linksFull (Johnson/Desc/Sound/AtDriver.lean), ps := flatPlacesOf linksFull true, k := 346.
Statements with their proofs.

  mergeAt, behindAt   the two places: number 346 is the merge's, ⟨1, some 24, 9, K11⟩; number 347
                      the sub-protocol's behind it, ⟨1, some 24, 10, K9⟩
  k11_hp, k11_hp'     they stand at these numbers of the written list          [the kernel]
  k11_hq              the table's row at the merge's place closes and opens no class of rows and no
                      pin of sampled tenants (quietRow)                        [the kernel]
  k11_hst             the chain stands alike at both: in the output head's open segment
  k11_hlk             both are of segment 24
  k11_htr_hms         THE TWO ON THE NUMBERS, AT EVERY N: from the test with code bookFit N ps told
                      (Johnson/Desc/First/BookFit.lean) and "sub-protocol number 346 tells no oracle
                      message" (told[346]? = some []): bookFit_at twice, told_succ_nil once
  k11_atBlocks        the same at the numbers closed over a list of sub-protocols (Numbers.atBlocks,
                      Johnson/Desc/First/NumbersAtBlocks.lean), without bookFit: UNDER TWO PREMISES,
                      which are not shown here: "their places are the written list" and "number 346
                      tells nothing"
  k11_seven           the seven in merge_t2's own letters
  Negative tests, by the kernel: numbers 345 and 347 are not the merge's place (k11_hp_not_345,
  k11_hp_not_347); the test on the row rejects at 128 of the 358 places (k11_hq_rejects); the chain
  stands otherwise at the head's segment's first place than at the merge (k11_hst_not).
  An example at the file's end lays the seven into merge_t2's binders: so the letters fit, by Lean.

Limits. The full size's written list alone, at the table's rows as imported: any other text of the
table owes the five anew. WHAT IS LEFT OF htr AND hms AT THE COMPOSED MEANING's OWN NUMBERS: that
these are closed over the description's own sub-protocols (or pass bookFit), and that the merge's
sub-protocol tells no oracle message: neither is shown here. Nothing on soundness.

-/
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.First.BordersKeep
import Johnson.Desc.First.NumbersAtBlocks
import Johnson.Top.H0.MergeLaw.TieOneTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound.MgAt
open VerifiableInference.Desc.First

/-- The merge's place. -/
def mergeAt : Place := ⟨1, some 24, 9, .K11⟩

/-- The place behind it. -/
def behindAt : Place := ⟨1, some 24, 10, .K9⟩

theorem k11_hp : (flatPlacesOf linksFull true)[346]? = some mergeAt := by decide +kernel

theorem k11_hp' : (flatPlacesOf linksFull true)[346 + 1]? = some behindAt := by decide +kernel

theorem k11_hq : quietRow (rowOf linksFull mergeAt) = true := by decide +kernel

theorem k11_hst : standAt linksFull behindAt = standAt linksFull mergeAt := by decide +kernel

theorem k11_hlk : behindAt.link = mergeAt.link := rfl

/-! ### Negative tests -/

theorem k11_hp_not_345 : (flatPlacesOf linksFull true)[345]? ≠ some mergeAt := by decide +kernel

theorem k11_hp_not_347 : (flatPlacesOf linksFull true)[347]? ≠ some mergeAt := by decide +kernel

/-- The test on the row can reject: it does so at 128 of the 358 places. -/
theorem k11_hq_rejects :
    ((flatPlacesOf linksFull true).filter fun p => !quietRow (rowOf linksFull p)).length = 128 := by
  decide +kernel

/-- The chain stands otherwise in front of the head's segment's first sub-protocol. -/
theorem k11_hst_not : standAt linksFull ⟨1, some 24, 1, .K7⟩ ≠ standAt linksFull mergeAt := by
  decide +kernel

/-! ### The two on the numbers -/

/-- **At every N that passes the test on the book's numbers.** -/
theorem k11_htr_hms (N : Numbers) (told : List (List Oracle))
    (hB : bookFit N (flatPlacesOf linksFull true) told = true) (hT : told[346]? = some []) :
    N.treesAt (some behindAt) = N.treesAt (some mergeAt) ∧
      N.msgsAt (some behindAt) = N.msgsAt (some mergeAt) := by
  have hl : (flatPlacesOf linksFull true).length = 358 := by decide +kernel
  have a := bookFit_at N _ told hB 346 (by rw [hl]; decide)
  have b := bookFit_at N _ told hB (346 + 1) (by rw [hl]; decide)
  rw [k11_hp] at a
  rw [k11_hp'] at b
  have c := told_succ_nil told 346 hT
  exact ⟨by rw [a.1, b.1, c.1], by rw [a.2, b.2, c.2]⟩

/-- The two places' numbers in the written list, by the search that the numbers' term uses. -/
theorem k11_idx : (flatPlacesOf linksFull true).idxOf mergeAt = 346 ∧
    (flatPlacesOf linksFull true).idxOf behindAt = 346 + 1 := by decide +kernel

/-- **At the numbers closed over a list of sub-protocols.** -/
theorem k11_atBlocks {St Cl : Type} (N : Numbers) (s : OnBytes.Params.ReqShape) (links : List ModelPart)
    (bs : List (Block St Cl)) (hP : blockPlaces bs = flatPlacesOf linksFull true)
    (hT : (toldOf bs)[346]? = some []) :
    (N.atBlocks s links bs).treesAt (some behindAt) =
        (N.atBlocks s links bs).treesAt (some mergeAt) ∧
      (N.atBlocks s links bs).msgsAt (some behindAt) =
        (N.atBlocks s links bs).msgsAt (some mergeAt) := by
  rw [atBlocks_treesAt, atBlocks_treesAt, atBlocks_msgsAt, atBlocks_msgsAt, hP]
  show treesTold _ ((flatPlacesOf linksFull true).idxOf behindAt) =
      treesTold _ ((flatPlacesOf linksFull true).idxOf mergeAt) ∧
    msgsTold _ ((flatPlacesOf linksFull true).idxOf behindAt) =
      msgsTold _ ((flatPlacesOf linksFull true).idxOf mergeAt)
  rw [k11_idx.1, k11_idx.2]
  exact told_succ_nil _ 346 hT

/-- **The seven, in merge_t2's own letters.** -/
theorem k11_seven (N : Numbers) (told : List (List Oracle))
    (hB : bookFit N (flatPlacesOf linksFull true) told = true) (hT : told[346]? = some []) :
    (flatPlacesOf linksFull true)[346]? = some mergeAt ∧
    (flatPlacesOf linksFull true)[346 + 1]? = some behindAt ∧
    quietRow (rowOf linksFull mergeAt) = true ∧
    standAt linksFull behindAt = standAt linksFull mergeAt ∧
    behindAt.link = mergeAt.link ∧
    N.treesAt (some behindAt) = N.treesAt (some mergeAt) ∧
    N.msgsAt (some behindAt) = N.msgsAt (some mergeAt) :=
  ⟨k11_hp, k11_hp', k11_hq, k11_hst, k11_hlk, (k11_htr_hms N told hB hT).1,
    (k11_htr_hms N told hB hT).2⟩

/-- The letters fit: the seven laid into merge_t2's binders. -/
example {Pp W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning Pp W) (told : List (List Oracle))
    (hB : bookFit N (flatPlacesOf linksFull true) told = true) (hT : told[346]? = some [])
    (Pm : Johnson.Desc.First.ForkMerge.HeadMergeP) :=
  MergeLaw.merge_t2 (Fr := Fr) N Mg linksFull (flatPlacesOf linksFull true) 346 Pm mergeAt behindAt
    k11_hp k11_hp' k11_hq k11_hst k11_hlk (k11_htr_hms N told hB hT).1 (k11_htr_hms N told hB hT).2

end VerifiableInference.Desc.Sound.MgAt

#print axioms VerifiableInference.Desc.Sound.MgAt.k11_hp
#print axioms VerifiableInference.Desc.Sound.MgAt.k11_hp'
#print axioms VerifiableInference.Desc.Sound.MgAt.k11_hq
#print axioms VerifiableInference.Desc.Sound.MgAt.k11_hst
#print axioms VerifiableInference.Desc.Sound.MgAt.k11_hlk
#print axioms VerifiableInference.Desc.Sound.MgAt.k11_hp_not_345
#print axioms VerifiableInference.Desc.Sound.MgAt.k11_hp_not_347
#print axioms VerifiableInference.Desc.Sound.MgAt.k11_hq_rejects
#print axioms VerifiableInference.Desc.Sound.MgAt.k11_hst_not
#print axioms VerifiableInference.Desc.Sound.MgAt.k11_htr_hms
#print axioms VerifiableInference.Desc.Sound.MgAt.k11_idx
#print axioms VerifiableInference.Desc.Sound.MgAt.k11_atBlocks
#print axioms VerifiableInference.Desc.Sound.MgAt.k11_seven
