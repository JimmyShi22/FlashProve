-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/StepsAtK4.lean: CONDITIONAL. Three statements with their
proofs.

What is here. AT THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4): THREE OF THE TESTS THAT
`chainSteps` (Honest/Frame.lean) MAKES AT A SUB-PROTOCOL WITH A PROVER's SIDE. Two on the book: in
the whole book of coins (`bookWhole`, Honest/BookWhole.lean) no row of the first table stands at
K4's place (`k4Place`, Honest/K4/Part.lean), and no entry names as its spender a part of K4's
place, for a part number from the length of K4's row (`k4Row`, the same file) on. It is
`bookWhole_tests_at` (Honest/Small/StepsOfBook.lean) at a sub-protocol that declares K4's entries:
none of these is named "SEND seed" (`k4_noSeed`, Law/W/MergesByName.lean) or "FOLD epsilon"
(`k4_noFold`, here), and the cut that the book's maker lays for the sub-protocol (`partsCut`,
Honest/BookOf.lean) has as many members as K4's row has parts (`k4_partsCut_row`,
Law/W/CutIsOurs.lean). One on the number of rounds: the side whose parts are K4's row has as many
rounds as the sub-protocol: `rounds_of_cut` (Honest/Small/RoundsOfCut.lean) at the same cut. The
test on the cut itself: `k4_cut_fits` (Law/W/CutAtK4.lean).

  `k4_noFold`   no round of a sub-protocol that declares K4's entries is named "FOLD epsilon".
  `k4_tests_fit`   **THE STATEMENT ON THE BOOK**: both tests, in `chainSteps`' own words but for
      three letters: the whole book for its book, that book's first table for its rows, and the
      length of the row as the kind's half has it (`k4Half`, Honest/K4/Part.lean) for that of the
      side's parts.
  `k4_rounds_fit`   **THE STATEMENT ON THE NUMBER OF ROUNDS.** It names no book.

Not shown here. THAT `bookWhole` RETURNS AT ANY FILES (h); that the description passes its test on
places (hp); THAT ANY MEMBER OF A DESCRIPTION STANDS AT K4's PLACE AND DECLARES K4's ENTRIES (hb,
hpl, hr): all five are premises here. (`k4_member_there`, Law/W/LockAtMember.lean, has hb, hpl and
hr together at the opened description: at the full size alone.) That the prover's side which
`chainSteps` finds at that place has K4's row as its parts. That the book and the table which
`chainSteps` is handed are the whole book and its first table: `ready` (Honest/Frame.lean) hands
`B.rowsOf 0`, `onlineProverFromPublicFiles` (Honest/AtPure.lean) the book of `bookWhole`; no file here joins them.
Nothing on an entry's owner. The test on the two lists' lengths; that `lendRow` returns; that
`chainSteps` returns. `k4_tests_fit`: the first chain alone. A LAW, NOT A PART: no file that
defines a part of the proof file's description may import this one. Nothing on soundness, on
completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Small.StepsOfBook
import Johnson.Desc.ProofFile.Honest.Small.RoundsOfCut
import Johnson.Desc.ProofFile.Honest.K4.Law.W.CutIsOurs
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MergesByName

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W
open OnBytes.Desc.First.K4 (entries)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block FileDescription)

/-- CONDITIONAL on hr. No round of a sub-protocol that declares K4's entries is named
"FOLD epsilon". -/
theorem k4_noFold {S Cl : Type} {b : Block S Cl} {Q : K4Pub}
    (hr : b.rounds = (entries Q.P Q.hp Q.g).map fun e => ({ entry := e } : Fmt.DeclaredRound)) :
    ∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon" := by
  intro r hrm
  rw [hr] at hrm
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hrm
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 he
  show d.name.name ≠ "FOLD epsilon"
  cases d.name <;> decide

/-- CONDITIONAL on h, hp, hb, hpl and hr. **IN THE WHOLE BOOK NO ROW OF THE FIRST TABLE STANDS AT
K4's PLACE, AND NO ENTRY NAMES AS ITS SPENDER A PART OF K4's PLACE, FOR A PART THAT K4's ROW DOES
NOT HAVE.** -/
theorem k4_tests_fit {Xf : Type} {F : FileDescription Xf} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₁ F.Cl} (hb : b ∈ F.first.blocksInOrder) {Q : K4Pub} {W₀ Rc Xi Tr X : Type}
    (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard) (hpl : b.place = k4Place Q)
    (hr : b.rounds = (entries Q.P Q.hp Q.g).map fun e => ({ entry := e } : Fmt.DeclaredRound)) :
    (B.rowsOf 0).any (fun r => r.1.place == b.place &&
        decide ((k4Row (Rc := Rc) (X := X) Q cells weights tokens look).length ≤ r.1.part)) =
      false ∧
    B.ahead.any (fun e => e.spender.place == b.place &&
        decide ((k4Row (Rc := Rc) (X := X) Q cells weights tokens look).length ≤
          e.spender.part)) = false := by
  refine bookWhole_tests_at h hp hb (k4_noSeed hr) (k4_noFold hr) ?_
  rw [k4_partsCut_row (Rc := Rc) (X := X) cells weights tokens look hpl hr, List.length_map]

/-- CONDITIONAL on hpl and hr. **THE SIDE WHOSE PARTS ARE K4's ROW HAS AS MANY ROUNDS AS THE
SUB-PROTOCOL.** -/
theorem k4_rounds_fit {S Cl : Type} {b : Block S Cl} {Q : K4Pub} {W₀ Rc Xi Tr X : Type}
    (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard) (hpl : b.place = k4Place Q)
    (hr : b.rounds = (entries Q.P Q.hp Q.g).map fun e => ({ entry := e } : Fmt.DeclaredRound)) :
    Placed.rounds ⟨k4Place Q, k4Row (Rc := Rc) (X := X) Q cells weights tokens look⟩ =
      b.rounds.length :=
  rounds_of_cut (k4_partsCut_row (Rc := Rc) (X := X) cells weights tokens look hpl hr).symm

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4_noFold
#print axioms ProofFile.Honest.K4.W.k4_tests_fit
#print axioms ProofFile.Honest.K4.W.k4_rounds_fit
