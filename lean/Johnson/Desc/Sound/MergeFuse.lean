-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MergeFuse.lean: SEVERAL PIECES IN A ROW AS ONE PIECE AT THE JOINED BLOCK: what
each part owes (`Piece.GoodIn`) gives what the joined block owes, IN THE SAME COIN. One definition,
one small lemma and the rule.

Why. Johnson/Desc/Sound/MergeSplit.lean ends at a chain's `KnowIn`. A seat that wraps a joined
block (`Block.inside`, a lift) wants ONE piece with `GoodIn` at that block, to carry on from.
`Piece.GoodIn` is `KnowIn` at the piece's own reduction, by definition, and a piece's reduction is
the chain's at the list that holds its one block: so the rule for one chain, at the list [B], IS
that piece's `GoodIn`, but for the way in which the list of rounds is written: the stretches' lists
appended, or the list of the appended data. The equation h (`ShapeIsChain`) carries the one to the
other.

Main names:
  `knowIn_cast`: `KnowIn` along an equation of the lists of rounds.
  `fused d B p l h`: the piece at B: the first part's base, the parts' data appended, the last
    part's rounds behind, the parts' extractors composed and their errors in a row, carried along h.
  **`goodIn_fuse`**: the parts' blocks merge to [B]; the parts are tiled; each has `GoodIn` between
    its two borders: then `fused` has `GoodIn` between the first border and the last.

Limits: as MergeSplit.lean's: B is the joining by `Block.andThen`, to the letter (`Merges`): a block
that is the joining with other words in its name, place or test on the plan is another term. The
borders between the parts are asked. Nothing on acceptance; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MergeSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed BadFam Tr)

/-- Along an equation of the lists of rounds. -/
theorem knowIn_cast {A B WA WB : Type} {s t : Shape} (h : s = t) (out : A → Iop.Tr t → Option B)
    (on : A → Prop) (on' : B → Prop) (RA : A → WA → Prop) (RB : B → WB → Prop)
    (ext : A → Iop.Tr s → WB → WA) (ε : Err s)
    (k : KnowIn (⟨s, fun a τ => out a (cast (congrArg Iop.Tr h) τ)⟩ : Reduction A B) on on' RA RB
      ext ε) :
    KnowIn (⟨t, out⟩ : Reduction A B) on on' RA RB
      (fun a τ w => ext a (cast (congrArg Iop.Tr h.symm) τ) w) (cast (congrArg Err h) ε) := by
  subst h
  exact k

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- **The parts as one piece at the block B.** -/
def fused (d : W) (B : Block S Cl) (p : Piece C F S Cl W) (l : List (Piece C F S Cl W))
    (h : (rowIOR p l).shape = uLT C (rowData p l)) : Piece C F S Cl W :=
  ⟨B, p.base, rowData p l, rowBack p l,
    fun a τ w => rowExt d p l a (cast (congrArg Iop.Tr h.symm) τ) w,
    cast (congrArg Err h) (rowErr p l)⟩

/-- **WHAT THE PARTS OWE GIVES WHAT THE JOINED BLOCK OWES.** -/
theorem goodIn_fuse (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop) (d : W)
    (B : Block S Cl) (p : Piece C F S Cl W) (l : List (Piece C F S Cl W))
    (h : (rowIOR p l).shape = uLT C (rowData p l)) (hm : Merges ((p :: l).map (·.b)) [B])
    (ht : Tiled p l) (hg : EachGoodIn on R 0 (p :: l)) :
    (fused d B p l h).GoodIn (on 0) (on (1 + l.length)) (R 0) (R (1 + l.length)) := by
  have key := chainKnowInSplit S Cl W C F B.name on R d [B] p l h hm ht hg
  exact knowIn_cast h (chainIOR C F B.name [B] p.base (rowData p l) (rowBack p l)).red.out
    _ _ _ _ _ _ key


end VerifiableInference.Desc.Sound
