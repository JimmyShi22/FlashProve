-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/Leaves/Join.lean: HOW A MEMBER OF `FileDescription.Hears`
(Johnson/Desc/Sound/FoldHeard.lean) IS MADE, AS A RULE: general in the description F, the reading
`heard`, what the rounds name (rd), and the places E that are let off.
  `laysAndThenFront`: a block without a round in front of a block that lays h: the two as one lay h.
  `laysAndThenBehind`: a block that leaves h behind a block that lays h: the two as one lay h, WHERE
    rd READS NO MORE THAN THE FIRST ONE's ROUNDS (hrd).
  `FileDescription.hearsOfLeaves`: **the join**: "every block of the first chain's flat list leaves
    `heard`, but those at E", a cut of that list with no block at E behind it, "the block at the cut
    lays `heard`" and the last test's law ARE a member of `F.Hears asked rd`.
Limits. RULES. No count, no game, no soundness. NO INSTANCE HERE: whether the premises can be met at
a description that rides is shown where one is made (PureHears.lean).
Nearest kin: `foldLays`, `chainLays`, `saidOfEnds` (Johnson/Desc/Sound/FoldHeardProofs.lean): they
take a member of `Hears`; this file makes one. `leavesAndThen` (there): the twin for Leaves.

-/
import Johnson.Desc.Sound.FoldHeardProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

section
variable {S Cl α : Type}

/-- A block without a round in front. -/
theorem laysAndThenFront (h : S → α) (rd : List Fmt.RoundView → α) (name : String) (p q : Block S Cl)
    (hp : p.rounds = []) (hq : q.Lays h rd) : (Block.andThen name p q).Lays h rd := by
  intro s rs gs s' H
  obtain ⟨t, _, H⟩ := bindOk (x := p.decide s (rs.take p.rounds.length) (gs.take p.openings)) H
  have e := hq _ _ _ _ H
  rw [hp] at e
  exact e

/-- A block that leaves h behind. hrd: rd reads no more than the first block's rounds. -/
theorem laysAndThenBehind (h : S → α) (rd : List Fmt.RoundView → α) (name : String) (p q : Block S Cl)
    (hp : p.Lays h rd) (hq : q.Leaves h) (hrd : ∀ rs, rd (rs.take p.rounds.length) = rd rs) :
    (Block.andThen name p q).Lays h rd := by
  intro s rs gs s' H
  obtain ⟨t, ht, H⟩ := bindOk (x := p.decide s (rs.take p.rounds.length) (gs.take p.openings)) H
  rw [hq _ _ _ _ H, hp _ _ _ _ ht, hrd]

end

/-- **THE JOIN.** -/
def FileDescription.hearsOfLeaves {Xi : Type} (F : FileDescription Xi) {Tok : Type} (asked : Xi → Tok)
    (rd : List Fmt.RoundView → Option Tok) (heard : F.S₁ → Option Tok) (E : Place → Prop)
    (pre : List (Block F.S₁ F.Cl)) (blk : Block F.S₁ F.Cl) (post : List (Block F.S₁ F.Cl))
    (cut : F.first.blocksInOrder = pre ++ blk :: post) (hpost : ∀ c ∈ post, ¬ E c.place)
    (hl : ∀ b ∈ F.first.blocksInOrder, ¬ E b.place → b.Leaves heard) (lays : blk.Lays heard rd)
    (fins : ∀ x e₁ e₂ e₃, F.fin x e₁ e₂ e₃ = true → heard e₁ = some (asked x)) :
    F.Hears asked rd where
  heard := heard
  pre := pre
  blk := blk
  post := post
  cut := cut
  lays := lays
  leaves := fun c hc => hl c (by rw [cut]; exact List.mem_append_right _ (List.mem_cons_of_mem _
      hc))
    (hpost c hc)
  fins := fins

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.laysAndThenFront
#print axioms VerifiableInference.Desc.laysAndThenBehind
#print axioms VerifiableInference.Desc.FileDescription.hearsOfLeaves
