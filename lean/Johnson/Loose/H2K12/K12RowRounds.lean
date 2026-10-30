-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Loose.H2K12.K12RowRoundsW
/-
Johnson/Loose/H2K12/K12RowRounds.lean: CONDITIONAL: UNDER THE PREMISES hV AND hn, NEITHER SHOWN OF
ANY PUBLIC FILES BY LEAN's KERNEL: THE PROXIMITY TEST's (the kind K12's) SECOND
ROW, IN ANOTHER FORM: FOR EACH SUB-PROTOCOL b OF THE LOT AND EACH SPOT p AT b's PLACE:
b.rounds IS THE WRITTEN TABLE's LIST AT p's NAME (the premise hL of ProofFile.Sk.base_good | back_good,
Johnson/Desc/ProofFile/Law/Skel/SkelRoundsParts.lean, at Q := ProofFile.Sk.Lst listAt, …/SkelLists.lean
[neither imported]). Calls and rewritings: no evaluation in Lean's
kernel stands in this file.
  k12_blocks_rounds  from hV (the numbers which the list of rounds gives are the written member
                     piLFull: the first row's own premise, H2K12/K12RowSkel.lean): the lot's one
                     sub-protocol stands at ⟨1, none, 2, K12⟩ and its declared rounds are the
                     table's list at "F:2", at every ground G
  k12_row_rounds     from hV and hn: hL's own form at this lot. ProofFile.Sk.Lst listAt p.name b.rounds is
                     Or.inr of its end
hn (each spot at ⟨1, none, 2, K12⟩ bears the name "F:2") IS A NAMED PREMISE, PAID BY NOBODY HERE.
It is no fact on the lot: a spot's name is made of the head of its row in the table of cuts
(Johnson/Desc/ProofFile/Places.lean: spotsFrom): at that place the make gives h ++ ":2" with h one
of "F", "M", "seal". Were two spots to share the place under two names, hn could not be met. THAT
IT IS MET AT THE LIBRARY's STORED FULL-SIZE PUBLIC FILES IS SHOWN BY NO THEOREM AND BY NO EVALUATION
THAT THIS FILE's WRITERS KNOW OF. Where the list has no spot at that place k12_row_rounds holds for
nothing: that is hL's own form.
G IS IDLE: the lot reads no ground (k12_blocks, H2K12/K12RowAlone.lean: by unfolding, at every g).
WHAT IT IS NOT: hV is shown of no public files by Lean's kernel (it is the first clause of the
conclusion of members_written | members_written_front, H2K12/K12MemberWritten.lean |
K12MemberFront.lean, from hypotheses by field).
THE KIND's THREE OTHER SUB-PROTOCOLS stand in no lot of the first chain. The full size alone. No
soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open H2K.Member (piLFull)

/-- **The lot's one sub-protocol: its place and its declared rounds.** -/
theorem k12_blocks_rounds (Z : ProofFile.Pub) (G : ProofFile.Ground) (hV : H2U.p12OfMade Z.made = piLFull) :
    ∀ b ∈ (VerifiableInference.Desc.K12.lot Z).blocks G,
      b.place = ⟨1, none, 2, .K12⟩ ∧ b.rounds = Johnson.AtFull.Rounds.listAt "F:2" := by
  intro b hb
  rw [k12_blocks, hV] at hb
  obtain rfl : b = lotB piLFull := List.mem_singleton.1 hb
  exact ⟨placeL_full, roundsL_full⟩

/-- **THE ROW, IN THE FORM "at the spot's name".** -/
theorem k12_row_rounds (Z : ProofFile.Pub) (G : ProofFile.Ground) (hV : H2U.p12OfMade Z.made = piLFull)
    (spots : List ProofFile.Spot)
    (hn : ∀ p ∈ spots, p.place = ⟨1, none, 2, .K12⟩ → p.name = "F:2") :
    ∀ b ∈ (VerifiableInference.Desc.K12.lot Z).blocks G, ∀ p ∈ spots, p.place = b.place →
      b.rounds = Johnson.AtFull.Rounds.listAt p.name := by
  intro b hb p hp e
  obtain ⟨h1, h2⟩ := k12_blocks_rounds Z G hV b hb
  rw [hn p hp (e.trans h1)]
  exact h2

end H2K12

#print axioms H2K12.k12_blocks_rounds
#print axioms H2K12.k12_row_rounds
