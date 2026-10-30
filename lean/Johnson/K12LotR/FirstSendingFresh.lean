-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/K12LotR/FirstSendingFresh.lean: **BEHIND AN ACCEPTING STEP OF LINK 0's
FIRST SUB-PROTOCOL, AS ITS LOT's LIST HAS IT, THE MESSAGE THAT THE FRAME's TEST ON THE INDEX
MASKS FINDS HAS THE FRESH LEDGER.** One definition, one theorem: the first debt ("the make") of the
fact along the run that stands in the place of the public item "pile.room"
(Johnson/P1L20R/RoomFold.lean: the premise hK of make_at).
  `shLast q gp`: the shape of the last message that the first segment's opening sends.
  `free0Of q gp`: the fresh ledger's free count at that shape and the codes q.codes.
  `first_sending_fresh`: general in Z, in the ground G and in the state s in front: for every
    sub-protocol b' of a list of `ProofFile.onlineFirstChainBlockTables Z` at G of the kind K1, at link 0, piece 1: where the
    shape in front has a message "at the start" and b' accepts from s to m: whatever
    `IndexMasksAt room m.check m.st.oracles im` finds has a ledger that is not closed, with just
    `free0Of G.first (K1.gpOf Z)` entries left.
PREMISES: two closed tests on `shLast` (a mask row; an answer); on s: its frame's shape has a
message "at the start" (it cannot be dropped: FirstIndexMasks.lean's head). AGAINST THE STATEMENT AS
FIRST ASKED: that premise on s; and "of the kind K1" beside "link 0, piece 1" (the naming lemma asks
it).
Called: `IM.lot_K1`, `IM.k1_mem`, `IM.numbers_pieces` (Johnson/IMR/K1Seat.lean); `K1.step_ok`;
`K1.firstAtS_fresh` (Johnson/Desc/K1/Law/FirstFresh.lean).
Nothing on soundness.

-/
import Johnson.IMR.K1Seat
import Johnson.Desc.K1.Law.FirstFresh

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice
open VerifiableInference.Desc (Block KindName)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Props (IndexMasksAt)
open ProofFile (Cl)

/-- The shape of the opening's last message. -/
def shLast (q : Params.First) (gp : GPar) : OracleShape :=
  ((firstPar q gp).sent.getD ((firstPar q gp).sent.size - 1) default).shape

/-- The fresh ledger's free count there. -/
def free0Of (q : Params.First) (gp : GPar) : Nat :=
  Send.freeMaskEntries (shLast q gp).maskRows
    (q.codes.mask.getD (shLast q gp).maskCode default).ell (shLast q gp).answers

/-- **The make.** -/
theorem first_sending_fresh {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (hm : 0 < (shLast G.first (gpOf Z)).maskRows) (ha : 1 ≤ (shLast G.first (gpOf Z)).answers) :
    ∀ (b' : Block S Cl) (s : S) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn)
      (m : S) (n : Nat), (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G) → b'.place.kind = KindName.K1 →
      b'.place.link = some 0 → b'.place.piece = 1 → s.check.frame.shape.atStart ≠ [] →
      b'.step 0 s rs cols = .ok (m, n) →
      ∀ room im, IndexMasksAt room m.check m.st.oracles im →
      ∃ l, (m.st.oracles[im]?).bind (·.ledger) = some l ∧ l.closed = false ∧
        l.left = free0Of G.first (gpOf Z) := by
  intro b' s rs cols m n ⟨L, hL, hb⟩ hk hl hpc hne hstep room im hi
  obtain ⟨x, hx, rfl⟩ := IM.lot_K1 hL hb hk hl
  rcases IM.k1_mem hx with rfl | ⟨l', X, pr, pd, reads, digits, hX, hn, rfl | rfl⟩
  · obtain ⟨hfit, gs, hd⟩ := step_ok 0 _ s m rs cols n hstep
    have hfit' : VerifiableInference.Desc.roundsFit (rounds (firstPar G.first (gpOf Z))) rs =
        true := hfit
    unfold rounds at hfit'
    rcases rs with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
    · simp [VerifiableInference.Desc.roundsFit] at hfit'
    · simp [VerifiableInference.Desc.roundsFit] at hfit'
    · have hd' : (firstSegmentOpening G.first (gpOf Z) : Block S Unit).decide s
          [VerifiableInference.Desc.noDigest a, VerifiableInference.Desc.noDigest b] gs =
          .ok m := hd
      exact (firstAtS_fresh G.first (gpOf Z) s m _ _ gs hd' hne room im hi hm ha).2
    · simp [VerifiableInference.Desc.roundsFit] at hfit'
  · exfalso
    have epc : pr = 1 := hpc
    rcases IM.numbers_pieces hn with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  · exfalso
    have epc : pd = 1 := hpc
    rcases IM.numbers_pieces hn with ⟨-, h⟩ | ⟨-, h⟩ <;> omega

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.first_sending_fresh
