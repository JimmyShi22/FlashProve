-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/AtLaid.lean: ON LISTS AND TESTS ALONE: CONDITIONAL:
at a sub-protocol that is K4's lot's own (`ProofFile.k4Block x`, Johnson/Desc/ProofFile/Lot/K4.lean),
seated alone as the description's maker seats it (`IM.LaidAlone`, Johnson/IMR/SeatForm.lean: under a
name, a place, a guard on the mark and a guard on the reply, and nothing else): its entries are
those of the verifier's table of K4's rounds; it passes the description's own test on its shape; so
the test on the rounds accepts them, and it has as many rounds as K4's row has moves. Statements and
proofs: calls of the library's `IM.alone_rounds`, `IM.alone_oracles` and of
Law/ExactFresh/AtSeat.lean.

Limits. No statement here is on a law of coins. THAT A DESCRIPTION's MEMBER IS SO SEATED IS A
HYPOTHESIS HERE (hb: an equation on the sub-protocol). By reading, the library's `IM.k4_of`
(Johnson/IMR/K4Seat.lean) has that equation at the third hearing sub-protocol of each of the twelve
layers' segments of the full-size description, under its own hypotheses; that file is not imported
here. THAT THE SIDE's SUB-PROTOCOL IS THAT MEMBER (that no other member of the list stands at K4's
place in front of it) is not shown here. hQ: three equations between the public data and the lot's
parameters; `k4PubOf` (Honest/K4/Part.lean) lays them so, by reading. No property is claimed.
What this file's imports reach, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/ or ThirdParty/ and at the names RecCompile.Honest…,
Both… and PassH…: through Johnson/IMR/SeatForm.lean: it stopped nowhere; it saw 7 modules whose
names hold RecCompile.

  `laid_entries`, `laid_shaped`   **the seat's two clauses at a sub-protocol so seated.**
  `laid_entries_pub`, `laid_stated`, `laid_count`   in the public data's letters: the entries; so
      the test on the rounds; the count of rounds.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.AtSeat
import Johnson.IMR.SeatForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.ExactFresh
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S)

section
variable {same : S → S → Bool} {b : Block S ProofFile.Cl} {x : Bool × OnBytes.Desc.First.K4.Par}
  {name : String} {a : Place} (hb : IM.LaidAlone same b (ProofFile.k4Block x) name a)
include hb

/-- **Its rounds have the table's entries.** -/
theorem laid_entries :
    b.rounds.map (·.entry) = OnBytes.Desc.First.K4.entries x.2.P x.2.hp x.2.g := by
  rw [IM.alone_rounds hb]
  exact k4Block_entries x

/-- **It passes the description's test on its shape.** -/
theorem laid_shaped : b.shaped = true := by
  have e := k4Block_shaped x
  unfold Block.shaped at e ⊢
  rw [IM.alone_rounds hb, IM.alone_oracles hb]
  exact e

variable {Q : K4Pub} (hQ : Q.P = x.2.P ∧ Q.hp = x.2.hp ∧ Q.g = x.2.g)
include hQ

/-- The entries in the public data's letters. -/
theorem laid_entries_pub :
    b.rounds.map (·.entry) = OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g := by
  rw [laid_entries hb, hQ.1, hQ.2.1, hQ.2.2]

/-- So the test on the rounds accepts them. -/
theorem laid_stated : k4StatedAllB Q (b.rounds.zip b.oracles) = true :=
  block_stated_shaped Q b (laid_entries_pub hb hQ) (laid_shaped hb)

/-- And it has as many rounds as K4's row has moves. -/
theorem laid_count : b.rounds.length = ((k4RowIn Q).map (·.moves.length)).sum :=
  block_count Q b (laid_entries_pub hb hQ)

end

end ProofFile.Honest.K4.ExactFresh

#print axioms ProofFile.Honest.K4.ExactFresh.laid_entries
#print axioms ProofFile.Honest.K4.ExactFresh.laid_shaped
#print axioms ProofFile.Honest.K4.ExactFresh.laid_entries_pub
#print axioms ProofFile.Honest.K4.ExactFresh.laid_stated
#print axioms ProofFile.Honest.K4.ExactFresh.laid_count
