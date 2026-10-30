-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FirstPlace.lean. LaidFramed IS OVERTAKEN AT A LINK's FIRST PLACE by Joined (Johnson/IMR/SameSpot.lean: no arm left; the link's own row); it stays for its callers.
Where the rest of this head and the Lean text differ, the Lean text holds.
A LAW ABOUT ProofFile.chainBy AND ProofFile.pureSeat, NO PART OF THEM: what stands at a link's FIRST place
(piece 1) in onlineDescription's first chain: a lot's block, alone or
WITH A BLOCK OF THE FRAMES' LOT JOINED BEHIND IT.
OBJECT. ProofFile.chainBy's joining (Johnson/Desc/ProofFile/Frames1.lean) at onlineDescription's seat, at piece 1. USER. `K1Seat` (link 0's first place) · `K7Seat` (the head's). LETTERS. As in Johnson/IMR/LaidFirst.lean.


THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): WHAT NEEDS NO SCOPE STANDS AT EVERY o; WHAT STANDS ON A LAW OF THE LIBRARY OVER «publicOf … = .ok X» STANDS AT OnBytes.secondHashFunction, where publicOfO_older makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7′ | G7′bits hand every o: for these the in-scope halves are still owed, at PublicCut).

  frame_from        a block of the kind «frame» of a lot of ProofFile.onlineFirstChainBlockTables that stands in a link is a block of the frames' lot (P1L20.blocksOf Z), carried over.
  LaidFramed Z b b' name a   b is b' alone (LaidAlone), OR b = seatedWith sameReply b' (guardMark fb.retype) name a for a block fb ∈ P1L20.blocksOf Z.
  chain_hear_first  chain_hear (Johnson/IMR/PureChain.lean) at onlineDescription's seat, at any index whose
                    kind is not K9, with LaidFramed.
  LaidFramed.laid   it is Laid (Johnson/IMR/SeatForm.lean): so laid_planOk | yes_laid hold of it.

WHAT IS NOT SHOWN, AND WHY. WHICH ARM, AND WHICH fb. chainBy joins BY NAME ALONE: «fr.find? fun x =>
behind b.name x.1» asks that the role is «behind l' m» with m = the place's name, AND NEVER READS
l'. So that the block joined at link l's
first place is link l's own «opened» hangs on «no two places bear one name», which nothing in the term tests (pureFaults asks it of places, not of names) and which I cannot prove without the plan's looks' spelling. fb THEREFORE STANDS UNDER
«there is», TIED BY ITS MEMBERSHIP IN THE FRAMES' LOT ALONE: A CALLER CAN BUILD ON THE FIRST HALF (b''s yes, b''s test on the plan), NOT ON WHAT THE JOINED HALF DOES. A cure in that text would be one conjunct: «n == m && b.place.link == some l».
No soundness.
-/
import Johnson.IMR.LaidFirst

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open ProofFile (Cl)

/-- **A block of the kind «frame» of the seat that stands in a link is the frames' lot's.** -/
theorem frame_from {Z : ProofFile.Pub} {G : ProofFile.Ground} {L : ProofFile.Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z)
    {b : Block S Cl} (hb : b ∈ L.blocks G) (hk : b.place.kind = KindName.frame) {l : ℕ}
    (hl : b.place.link = some l) : ∃ fb ∈ P1L20.blocksOf Z, b = fb.retype := by
  unfold ProofFile.onlineFirstChainBlockTables ProofFile.p4Pure at hL
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl)
  · rcases blocks_mem hb with ⟨x, hx, rfl⟩ | hb
    · exact ⟨x, hx, rfl⟩
    · exact nomatch hb
  · rw [kind_K1 Z G b hb] at hk; cases hk
  · rw [kind_K2 Z G b hb] at hk; cases hk
  · rw [kind_K3 Z G b hb] at hk; cases hk
  · rw [kind_K4 Z G b hb] at hk; cases hk
  · rw [kind_K5 Z G b hb] at hk; cases hk
  · rw [kind_K8 Z G b hb] at hk; cases hk
  · rcases kind_K9 Z G b hb with e | e <;> rw [e] at hk <;> cases hk
  · rw [kind_K11 Z G b hb] at hk; cases hk
  · rw [kind_K12 Z G b hb] at hk; cases hk
  · rw [kind_K13 Z G b hb] at hk; cases hk
  · rw [kind_K13_4 Z G b hb] at hk; cases hk
  · rcases blocks_mem hb with ⟨x, hx, rfl⟩ | hb
    · obtain rfl := List.mem_singleton.1 hx
      cases hl
    · exact nomatch hb
  · rw [kind_K6 Z G b hb] at hk; cases hk
  · rw [kind_K7_lot rfl rfl b hb] at hk; cases hk

/-- Alone, or with a block of the frames' lot joined behind. -/
def LaidFramed (Z : ProofFile.Pub) (b b' : Block S Cl) (name : String) (a : Place) : Prop :=
  LaidAlone ProofFile.sameReply b b' name a ∨
    ∃ fb ∈ P1L20.blocksOf Z, b = seatedWith ProofFile.sameReply b' (ProofFile.guardMark fb.retype) name a

theorem LaidFramed.laid {Z : ProofFile.Pub} {b b' : Block S Cl} {name : String} {a : Place}
    (h : LaidFramed Z b b' name a) : Laid ProofFile.sameReply b b' name a := by
  rcases h with h | ⟨fb, -, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨_, h⟩

theorem LaidFramed.name {Z : ProofFile.Pub} {b b' : Block S Cl} {name : String} {a : Place}
    (h : LaidFramed Z b b' name a) : b.name = name := by
  rcases h with h | ⟨fb, -, h⟩
  · exact alone_name h
  · subst h
    rfl

/-- **A block in front of the batching, at onlineDescription's seat: a lot's block, alone or with a block of the frames' lot behind it.** -/
theorem chain_hear_first {Z : ProofFile.Pub} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B)
    (hb : (ProofFile.partsAt (ProofFile.pureSeat o Z) B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) B).road = .ok c) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : ℕ) (k : KindName)
    (hk : (kindsBeforeBatching sub (l == 0))[i]? = some k) (hk9 : k ≠ KindName.K9) :
    ∃ Lk b, c.links[l]? = some Lk ∧ Lk.hear[i]? = some b ∧
      ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, ∃ b' ∈ L.blocks B.G₀,
        b'.place = { chain := 1, link := some l, piece := i + 1, kind := k } ∧
        LaidFramed Z b b' b.name { chain := 1, link := some l, piece := i + 1, kind := k } := by
  obtain ⟨-, -, -, hall⟩ := base_made hB
  obtain ⟨Lk, b, e1, e2, sp, hsp, L, hL, b', hb', es, ep, harm⟩ :=
    chain_hear hall (makers_K9 Z B.G₀) hb hc l sub hl i k hk hk9
  refine ⟨Lk, b, e1, e2, L, hL, b', hb', ep, ?_⟩
  have hfr : LaidFramed Z b b' sp.name { chain := 1, link := some l, piece := i + 1, kind := k } := by
    rcases harm with ⟨h, -⟩ | ⟨x, hx, hr, h⟩
    · exact Or.inl h
    · obtain ⟨L', hL', fb', hfb', hkf, er, e2'⟩ := frames_from_lots hall hx
      obtain ⟨-, -, -, -, -, hlk⟩ := role_behind (er.symm.trans hr)
      obtain ⟨fb, hfb, rfl⟩ := frame_from hL' hfb' hkf hlk
      rw [e2'] at h
      exact Or.inr ⟨fb, hfb, h⟩
  rw [hfr.name]
  exact hfr

end IM

#print axioms IM.frame_from
#print axioms IM.chain_hear_first
