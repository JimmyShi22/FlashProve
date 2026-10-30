-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/Merge.lean: THE RULE OF COMPOSITION'S SOCKET FOR A STRETCH OF SEVERAL BLOCKS: a
stretch is a `Piece` at the merged block. It stands BESIDE ChainRule.lean, GoodIn.lean and
KnowIn.lean: none of them is turned. One definition of type Prop and its proof, over
Johnson/Desc/Sound/MergeFold.lean.

Main names:
  `foldRun_merges`: the chain's decision is the same function whether or not neighbours are merged.
    `foldRed_merges`: so is the chain's decision as a reduction over the stretches' rounds.
  `mergeAll n b l`: a block and the blocks behind it as one. `merges_mergeAll`: a chain's list with
    such a run of neighbours merges to the list with the one block in their place.
  `ChainKnowInMerged`, `chainKnowInMerged`: **THE RULE FOR ONE CHAIN** (`ChainKnowIn`) with the
    premise "the pieces' blocks ARE the chain's list" weakened to "THE CHAIN'S LIST MERGES TO THE
    PIECES' BLOCKS"; THE CONCLUSION IS OF THE CHAIN'S OWN FOLD, over its own list.

HOW A LAW OVER A STRETCH ENTERS. bAll := `mergeAll` of the stretch's blocks; pAll := the piece
⟨bAll, the first block's base, the stretch's rounds' data appended, back, ext, err⟩. The library's
proved block over the whole stretch is carried to `pAll.GoodIn` by `goodIn_ofBK`
(Johnson/Desc/Sound/K3Good.lean) from its `Know`, its carried condition, the readings G, rd and rw
with their two conditions, and the hypothesis `Hear`, which is proved of no block of the protocol,
NOT from its `Good`
(which ends in `KnowInto`, and that does not give `KnowIn`). In the table of joints the stretch's
row in is its first block's border, its row out its last block's: THE BORDERS BETWEEN ARE NOT ASKED.
What rides past the stretch rides by `goodInBeside`'s one premise, over the whole stretch.

Silly members: `chainKnowInMerged` adds no premise on a verifier to `chainKnowIn`'s: at
`Merges.refl` it is that rule. That a stretch whose second block says yes to all breaks the
carriage's premise: Johnson/Desc/Sound/MergeToy.lean.

Limits: `Tiled` is asked of the merged pieces: that the merged block is owed just the appended
stretch (`Piece.Owed`: two counts) and that its trees are listed is NOT SHOWN HERE: by a reader's
reading the tiling's laws read the blocks' declared rounds appended, which merging does not turn: so
the merged list is cut as any list. A link's batching reads its claims off the UNMERGED hearing
blocks (`claimsIn K.hear K.order`): the fold never reads a block's claims: a piece at a stretch that
holds the batching owes the whole link's law, and `BatchKnows` is then not asked. No law of the
library has been carried through this socket yet. THE FILE'S STOREY DOES NOT TAKE A MERGED LIST AS
IT IS TYPED, IN FOUR PLACES: (i) `OfDesc` asks the pieces' blocks to be the
description's blocks, lifted, one for one; (ii) the laws that cut a plan's data ask the blocks'
declared rounds block by block, where the appended form would serve; (iii) the shared chain's rules
ask of every piece a block that is a lift: that two lifts merged are the lift of the merged block
holds under the two laws of a lens, by a lemma that is owed; (iv) `below`: take the merging of the
two blocks as they stand in the list. UNTIL (i) AND (ii) HAVE MERGED TWINS, A LAW CARRIED THROUGH
THIS SOCKET ENDS AT ONE CHAIN'S `KnowIn`. Nothing on acceptance; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KnowInProofs
import Johnson.Desc.Sound.MergeFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed BadFam Tr)

variable {S Cl W : Type} {C : CK} {F : Frame}

theorem toOption_congr {ε α : Type} {x y : Except ε α} (h : ∀ a, x = .ok a ↔ y = .ok a) :
    x.toOption = y.toOption := by
  cases x with
  | ok a => rw [(h a).1 rfl]
  | error e =>
    cases y with
    | ok b => exact absurd ((h b).2 rfl) (by intro h'; cases h')
    | error e' => rfl

/-- **The chain's decision is the same function whether or not neighbours are merged.** -/
theorem foldRun_merges (F : Frame) (name : String) {l m : List (Block S Cl)} (h : Merges l m)
    (back : List Fmt.RoundView) : foldRun F name l back = foldRun F name m back := by
  funext s v
  exact toOption_congr fun a => h.chainAt name F.ft s a _

/-- So is the chain's decision as a reduction over the stretches' rounds. -/
theorem foldRed_merges (name : String) {bs bs' : List (Block S Cl)} (hm : Merges bs bs')
    (p : Piece C F S Cl W) (l : List (Piece C F S Cl W))
    (h : (rowIOR p l).shape = uLT C (rowData p l)) :
    foldRed name bs p l h = foldRed name bs' p l h := by
  unfold foldRed chainIOR
  rw [foldRun_merges F name hm]

/-- A block and the blocks behind it, as one block. -/
def mergeAll (n : String) : Block S Cl → List (Block S Cl) → Block S Cl
  | b, [] => b
  | b, q :: l => mergeAll n (b.andThen n q) l

theorem merges_mergeAll (n : String) (pre rest : List (Block S Cl)) :
    ∀ (l : List (Block S Cl)) (b : Block S Cl),
      Merges (pre ++ b :: (l ++ rest)) (pre ++ mergeAll n b l :: rest)
  | [], _ => .refl _
  | q :: l, b => .step pre n b q (l ++ rest) _ (merges_mergeAll n pre rest l (b.andThen n q))

/-- **THE RULE FOR ONE CHAIN, WITH STRETCHES OF SEVERAL BLOCKS.** flat: the chain's own list of
blocks. It merges to the pieces' blocks: so a piece may stand at several neighbours of the chain,
merged. The conclusion is of THE CHAIN'S OWN FOLD, over flat. -/
def ChainKnowInMerged : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (name : String) (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (d : W) (flat : List (Block S Cl)) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (h : (rowIOR p l).shape = uLT C (rowData p l)),
    Merges flat ((p :: l).map (·.b)) → Tiled p l → EachGoodIn on R 0 (p :: l) →
    KnowIn (foldRed name flat p l h) (on 0) (on (1 + l.length)) (R 0) (R (1 + l.length))
      (rowExt d p l) (rowErr p l)

theorem chainKnowInMerged : ChainKnowInMerged := by
  intro S Cl W C F name on R d flat p l h hm ht hg
  have key := chainKnowIn S Cl W C F name on R d p l h ht hg
  unfold foldRed chainIOR at key ⊢
  rw [foldRun_merges F name hm]
  exact key

end VerifiableInference.Desc.Sound
