-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MergeSplit.lean: THE RULE OF COMPOSITION WHERE THE CHAIN'S LIST HOLDS A JOINED
BLOCK AND THE LAWS STAND AT ITS PARTS: the twin of Johnson/Desc/Sound/Merge.lean's rule, read the
other way. One definition of type Prop and its proof.

Why. A description may seat two blocks THAT BOTH HAVE ROUNDS as one, by `Block.andThen` (a hearing
and the draw behind it; a place that two kinds share). A kind's law is typed as a `Piece` at ITS
part. The rule for one chain (`ChainKnowIn`) asks that the pieces' blocks ARE the chain's list.
Here: THE PIECES' BLOCKS MERGE TO THE CHAIN'S LIST: each joined block of the list is the joining of
neighbouring pieces' blocks. THE CONCLUSION IS OF THE CHAIN'S OWN FOLD, over its own list.

Main names: `ChainKnowInSplit`, `chainKnowInSplit`.

HOW IT IS USED. flat = pre ++ (p.andThen n q) :: rest; the pieces stand at pre, p, q, rest:
`Merges.step` (Johnson/Desc/Sound/MergeFold.lean) gives the premise in one line. The table of joints
then HAS a border between p and q, with its own promise and relation: it is asked, and each part's
law is owed at its own two borders.

Limits: as Merge.lean's: `Tiled` is asked of the pieces as they stand (the parts): that each part
is owed just its own stretch is its own matter. It rests on `foldRun_merges`: the fold's decision is
one function at both lists: so nothing is said of a joining other than `Block.andThen` (a lift, a
guard, `Block.inside` around the pair). The file's storey (`OfDesc`) asks the pieces' blocks one
for one, as Merge.lean's Limits say: a law carried through this rule ends at one chain's `KnowIn`.
Nothing on acceptance; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.Merge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed BadFam Tr)

/-- **THE RULE FOR ONE CHAIN, WITH PIECES AT THE PARTS OF JOINED BLOCKS.** flat: the chain's own
list of blocks. The pieces' blocks merge to it. The conclusion is of THE CHAIN'S OWN FOLD. -/
def ChainKnowInSplit : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (name : String) (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (d : W) (flat : List (Block S Cl)) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (h : (rowIOR p l).shape = uLT C (rowData p l)),
    Merges ((p :: l).map (·.b)) flat → Tiled p l → EachGoodIn on R 0 (p :: l) →
    KnowIn (foldRed name flat p l h) (on 0) (on (1 + l.length)) (R 0) (R (1 + l.length))
      (rowExt d p l) (rowErr p l)

theorem chainKnowInSplit : ChainKnowInSplit := by
  intro S Cl W C F name on R d flat p l h hm ht hg
  have key := chainKnowIn S Cl W C F name on R d p l h ht hg
  unfold foldRed chainIOR at key ⊢
  rw [← foldRun_merges F name hm]
  exact key


end VerifiableInference.Desc.Sound
