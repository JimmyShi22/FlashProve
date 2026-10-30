-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookAlike.lean: NINE OF THE MAKERS OF THE BOOK OF COINS, NAMED BELOW,
EACH GIVE ONE ANSWER AT TWO LISTS OF SUB-PROTOCOLS THAT ARE ALIKE BLOCK BY BLOCK, IN ORDER (the
first of the nine: at two blocks that are alike): nine congruences. Written by the authors of the
honest side of the output head's own rounds (K6), in the frame's folder, not by the frame's authors;
the makers are theirs. CONDITIONAL, each on ONE premise: h: the two blocks, or the two lists, are
alike.

The relation is the library's own, as it stands (Johnson/AtFull/ProofPlan/PlanAlike.lean):
`Alike₂ b b'`: place, rounds, oracles and before are equal, and where b's own test on the plan
passes b' 's does; between blocks of two types of state and of claim. IT ASKS MORE THAN IS SPENT
HERE: "before" and the arrow on the blocks' own tests are idle in every lemma. It is taken all the
same: a weaker relation would be a new definition, and the fields of `PlanAlike` plug in as they
are.

  `partsCut_alike`          at two blocks: the maker's cut. Spends place and rounds
  `planOf_alike`            a chain without its state's type. Place, rounds
  `addrOfRound_alike`       the address of the part that holds a round. Place, rounds
  `seedRounds_alike`        the numbers of the rounds "SEND seed". Rounds
  `maskWordsByRound_alike`  the mask words round by round. Rounds, oracles
  `sentIn_alike`, `ownerOf_alike`, `splitEntry_alike`, `ownFreshIn_alike`   through these

How. All goes through four readers of a list of blocks: `bs.flatMap (·.rounds)` (the library's
`alike₂_rounds` is that one), `addrOfRound`, `planOf`, `maskWordsByRound`: each by an induction on
`List.Forall₂`; the rest by unfolding and rewriting. THE ANSWERS ARE EQUAL AS VALUES, THE REFUSALS'
WORDS TOO: none of these makers reads a block's field `name`, which the relation does not keep.

Limits. NO MAKER'S RETURN IS HAD, AT ANY LIST: an answer is carried from one list to another. That
two lists are alike is not had here. General in the lists: no description is named. The other
makers of the book, and the book's own tests, are not touched. (The library has a file
Johnson/AtFull/ProofPlan/At/No/BookAlike.lean: another folder, another module, another matter.)
Bookkeeping: no new mathematics. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.BookWhole
import Johnson.AtFull.ProofPlan.PlanAlike

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Alike₂ alike₂_rounds)

variable {S Cl S' Cl' : Type}

/-- **The maker's cut at two blocks that are alike.** CONDITIONAL: h. -/
theorem partsCut_alike {b : Block S Cl} {b' : Block S' Cl'} (h : Alike₂ b b') :
    partsCut b = partsCut b' := by
  unfold partsCut
  rw [h.1, h.2.1]

variable {l : List (Block S Cl)} {l' : List (Block S' Cl')} (h : List.Forall₂ Alike₂ l l')
include h

/-- CONDITIONAL: h: the lists are alike. -/
theorem planOf_alike : planOf l = planOf l' := by
  unfold planOf
  induction h with
  | nil => rfl
  | @cons b b' l l' hb _ ih => simp only [List.map_cons, hb.1, hb.2.1, partsCut_alike hb, ih]

/-- CONDITIONAL: h. -/
theorem addrOfRound_alike (i : Nat) : addrOfRound l i = addrOfRound l' i := by
  induction h generalizing i with
  | nil => rfl
  | @cons b b' l l' hb _ ih => simp only [addrOfRound, hb.1, hb.2.1, partsCut_alike hb, ih]

/-- CONDITIONAL: h. -/
theorem seedRounds_alike : seedRounds l = seedRounds l' := by
  unfold seedRounds
  rw [alike₂_rounds l l' h]

/-- CONDITIONAL: h. -/
theorem maskWordsByRound_alike : maskWordsByRound l = maskWordsByRound l' := by
  unfold maskWordsByRound
  induction h with
  | nil => rfl
  | @cons b b' l l' hb _ ih => simp only [List.flatMap_cons, hb.2.1, hb.2.2.1, ih]

/-- CONDITIONAL: h. The same list of messages, or the same refusal. -/
theorem sentIn_alike (c : Johnson.G.ChainSends) (later : List Fmt.DeclaredRound) :
    sentIn l c later = sentIn l' c later := by
  unfold sentIn
  simp only [seedRounds_alike h, alike₂_rounds l l' h, addrOfRound_alike h]

/-- CONDITIONAL: h. -/
theorem ownerOf_alike (name : String) (c : Johnson.G.ChainSends) (later : List Fmt.DeclaredRound)
    (label : String) (pick : OnBytes.OracleNotice → Bool) :
    ownerOf name l c later label pick = ownerOf name l' c later label pick := by
  unfold ownerOf
  simp only [seedRounds_alike h, alike₂_rounds l l' h, addrOfRound_alike h]

/-- CONDITIONAL: h. -/
theorem splitEntry_alike (c : Johnson.G.ChainSends) : splitEntry l c = splitEntry l' c := by
  unfold splitEntry
  simp only [alike₂_rounds l l' h, addrOfRound_alike h, ownerOf_alike h]

/-- CONDITIONAL: h. -/
theorem ownFreshIn_alike : ownFreshIn l = ownFreshIn l' := by
  unfold ownFreshIn
  simp only [planOf_alike h, maskWordsByRound_alike h]

end ProofFile.Honest

#print axioms ProofFile.Honest.partsCut_alike
#print axioms ProofFile.Honest.planOf_alike
#print axioms ProofFile.Honest.addrOfRound_alike
#print axioms ProofFile.Honest.seedRounds_alike
#print axioms ProofFile.Honest.maskWordsByRound_alike
#print axioms ProofFile.Honest.sentIn_alike
#print axioms ProofFile.Honest.ownerOf_alike
#print axioms ProofFile.Honest.splitEntry_alike
#print axioms ProofFile.Honest.ownFreshIn_alike
