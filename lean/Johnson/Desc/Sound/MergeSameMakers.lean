-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MergeSameMakers.lean: `Block.Same` (the same declared rounds, the same `decide`:
Johnson/Desc/Sound/MergeSame.lean) GOES THROUGH THE MAKERS OF BLOCKS: the strict reading `below`,
and `Block.andThen` on either side. Small lemmas with their proofs.

Why. What sits at a place of a chain is a value of a kind's maker at an address, known only by an
equation on its rounds and its `decide` (its name, its test on the plan and its lists of claims may
part from those of the block of which the kind's law speaks). A description's piece holds `below` of
it, at times joined with a step. These lemmas carry the equation up to what the piece holds.

Main names:
  `Block.Same.refl`, `.symm`, `.trans`.
  `Block.Same.below`: b.Same b' gives (below b).Same (below b').
  `Block.Same.andThen`: b.Same b' and q.Same q' give (b.andThen n q).Same (b'.andThen n' q').
  `goodIn_of_same`: a piece that holds B owes what the piece with B' in B's place owes, where
    B'.Same B: `goodIn_same`, read from the given piece's side.

Limits: rounds and `decide` alone: nothing on a block's test on the plan, its oracles, `before`, or
its lists of claims. Nothing on acceptance; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MergeSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl : Type}

theorem Block.Same.refl (b : Block S Cl) : b.Same b := ⟨rfl, rfl⟩

theorem Block.Same.symm {b b' : Block S Cl} (h : b.Same b') : b'.Same b := ⟨h.1.symm, h.2.symm⟩

theorem Block.Same.trans {b b' b'' : Block S Cl} (h : b.Same b') (h' : b'.Same b'') : b.Same b'' :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

theorem Block.Same.openings {b b' : Block S Cl} (h : b.Same b') : b.openings = b'.openings := by
  unfold Block.openings
  rw [h.1]

/-- Two blocks as one, of the same on either side. The joint's name is free. -/
theorem Block.Same.andThen {b b' q q' : Block S Cl} (h : b.Same b') (hq : q.Same q')
    (n n' : String) : (b.andThen n q).Same (b'.andThen n' q') := by
  refine ⟨?_, ?_⟩
  · show b.rounds ++ q.rounds = b'.rounds ++ q'.rounds
    rw [h.1, hq.1]
  · show (fun (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) =>
        (b.decide s (rs.take b.rounds.length) (gs.take b.openings)).bind fun s' =>
          q.decide s' (rs.drop b.rounds.length) (gs.drop b.openings)) =
      fun (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) =>
        (b'.decide s (rs.take b'.rounds.length) (gs.take b'.openings)).bind fun s' =>
          q'.decide s' (rs.drop b'.rounds.length) (gs.drop b'.openings)
    rw [h.2, hq.2, h.1, h.openings]

end VerifiableInference.Desc

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- The strict reading of the same is the same. -/
theorem _root_.VerifiableInference.Desc.Block.Same.below {b b' : Block S Cl} (h : b.Same b') :
    (below b).Same (below b') := by
  refine ⟨h.1, ?_⟩
  show (fun (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) =>
      if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide s rs gs
      else .error "a word is not below the prime") =
    fun (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) =>
      if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b'.decide s rs gs
      else .error "a word is not below the prime"
  rw [h.2]

/-- **From the given piece's side**: p holds B; the piece with B' in B's place owes; B'.Same B. -/
theorem goodIn_of_same (p : Piece C F S Cl W) (B' : Block S Cl) (h : B'.Same p.b)
    (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop)
    (g : ({ p with b := B' } : Piece C F S Cl W).GoodIn on on' R R') : p.GoodIn on on' R R' :=
  goodIn_same ({ p with b := B' } : Piece C F S Cl W) p.b h on on' R R' g


end VerifiableInference.Desc.Sound
