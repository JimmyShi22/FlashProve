-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K11Tells.lean: the merge's sub-protocol tells no oracle message: so of the
two premises under which K11Places.lean has merge_t2's htr and hms, the second falls to "number 346
of the list is the merge's sub-protocol, as far as what it tells goes". Statements and proofs.

  merge_tells_nothing   (headClaimMergeKind P).oracles.flatten = []: off the kind's own text
                        (Johnson/Desc/First/Fork/MergeKind.lean: a list of empty lists)
  told_of_merge         where number 346 of a list of sub-protocols tells what headClaimMergeKind P tells:
                        (toldOf bs)[346]? = some []
  k11_atBlocks_merge    htr and hms at the numbers closed over such a list whose places are the
                        written list
  withTold_next         the like at any list of places and two places at k and k + 1 of it
  k11_withTold          htr and hms at N.withTold ‹the written list› told, at every N and told: from
                        told[346]? = some [] alone. The composed meaning's own numbers have that
                        form (Johnson/P5J/LettersAt.lean: N := (… ).withTold ps (told cF), ps the
                        written list): that file is not imported here

Limits. That number 346 of the description's own list is the merge's sub-protocol, and that the
list's places are the written list, are premises here. Nothing on soundness.

-/
import Johnson.Desc.Sound.MgAt.K11Places
import Johnson.Desc.First.Fork.MergeKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound.MgAt
open VerifiableInference.Desc.First
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind)

/-- The merge's sub-protocol tells no oracle message. -/
theorem merge_tells_nothing (P : HeadMergeP) : (headClaimMergeKind P).oracles.flatten = [] := by
  show (List.replicate (P.lay.lk + 4) ([] : List Oracle)).flatten = []
  induction P.lay.lk + 4 with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, ih]; rfl

/-- Where number 346 of a list tells what the merge's sub-protocol tells. -/
theorem told_of_merge {St Cl : Type} (bs : List (Block St Cl)) (b : Block St Cl)
    (hb : bs[346]? = some b) (P : HeadMergeP) (ho : b.oracles = (headClaimMergeKind P).oracles) :
    (toldOf bs)[346]? = some [] := by
  unfold toldOf
  rw [List.getElem?_map, hb, Option.map_some, ho, merge_tells_nothing]

/-- **htr and hms at the numbers closed over such a list.** -/
theorem k11_atBlocks_merge {St Cl : Type} (N : Numbers) (s : OnBytes.Params.ReqShape)
    (links : List ModelPart) (bs : List (Block St Cl))
    (hP : blockPlaces bs = flatPlacesOf linksFull true) (b : Block St Cl)
    (hb : bs[346]? = some b) (P : HeadMergeP) (ho : b.oracles = (headClaimMergeKind P).oracles) :
    (N.atBlocks s links bs).treesAt (some behindAt) =
        (N.atBlocks s links bs).treesAt (some mergeAt) ∧
      (N.atBlocks s links bs).msgsAt (some behindAt) =
        (N.atBlocks s links bs).msgsAt (some mergeAt) :=
  k11_atBlocks N s links bs hP (told_of_merge bs b hb P ho)

/-- At numbers whose two numbers on the book are laid off what is told (Numbers.withTold): two
places that stand at k and k + 1 of the list have one pair of numbers, where number k tells
nothing. -/
theorem withTold_next (N : Numbers) (ps : List Place) (told : List (List Oracle)) (p p' : Place)
    (k : Nat) (h1 : ps.idxOf p = k) (h2 : ps.idxOf p' = k + 1) (hT : told[k]? = some []) :
    (N.withTold ps told).treesAt (some p') = (N.withTold ps told).treesAt (some p) ∧
      (N.withTold ps told).msgsAt (some p') = (N.withTold ps told).msgsAt (some p) := by
  show treesTold told (ps.idxOf p') = treesTold told (ps.idxOf p) ∧
    msgsTold told (ps.idxOf p') = msgsTold told (ps.idxOf p)
  rw [h1, h2]
  exact told_succ_nil told k hT

/-- **htr and hms at such numbers, at the written list of places**: one premise is left. -/
theorem k11_withTold (N : Numbers) (told : List (List Oracle)) (hT : told[346]? = some []) :
    (N.withTold (flatPlacesOf linksFull true) told).treesAt (some behindAt) =
        (N.withTold (flatPlacesOf linksFull true) told).treesAt (some mergeAt) ∧
      (N.withTold (flatPlacesOf linksFull true) told).msgsAt (some behindAt) =
        (N.withTold (flatPlacesOf linksFull true) told).msgsAt (some mergeAt) :=
  withTold_next N _ told mergeAt behindAt 346 k11_idx.1 k11_idx.2 hT

end VerifiableInference.Desc.Sound.MgAt

#print axioms VerifiableInference.Desc.Sound.MgAt.merge_tells_nothing
#print axioms VerifiableInference.Desc.Sound.MgAt.told_of_merge
#print axioms VerifiableInference.Desc.Sound.MgAt.k11_atBlocks_merge
#print axioms VerifiableInference.Desc.Sound.MgAt.withTold_next
#print axioms VerifiableInference.Desc.Sound.MgAt.k11_withTold
