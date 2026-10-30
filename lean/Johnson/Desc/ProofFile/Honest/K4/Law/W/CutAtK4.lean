-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/CutAtK4.lean: CONDITIONAL. Two statements with their proofs.

What is here. BOTH SIDES OF THE SECOND TEST THAT `chainSteps` (Honest/Frame.lean) MAKES AT A
SUB-PROTOCOL WITH A PROVER's SIDE, AT THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4): in the
whole book of coins the cut that stands at K4's place is the list of the numbers of moves of the
parts of K4's row. The left side: `bookWhole_cut_first` (Honest/Small/CutOfBook.lean): the book has
there the sub-protocol's own cut. The right side: `k4_partsCut_row` (Law/W/CutIsOurs.lean): that
cut is the numbers of moves of K4's parts.

  `k4_rounds_ne`   a sub-protocol that declares K4's table's entries has a round.
  `k4_cut_fits`   **THE STATEMENT.**

Not shown here. THAT `bookWhole` RETURNS AT ANY FILES; that the description passes its test on
places; THAT ANY MEMBER OF A DESCRIPTION STANDS AT K4's PLACE AND DECLARES K4's ENTRIES: hb, hpl
and hr are premises. That the prover's side which `chainSteps` finds at that place has K4's row as
its parts. Nothing on the other tests of `chainSteps`. The first chain alone. A LAW, NOT A PART: no
file that defines a part of the proof file's description may import this one. Nothing on soundness,
on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Small.CutOfBook
import Johnson.Desc.ProofFile.Honest.K4.Law.W.CutIsOurs
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RowIsPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W
open OnBytes.Desc.First.K4 (entries)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block FileDescription)

/-- CONDITIONAL on hpl and hr. A sub-protocol that declares K4's table's entries has a round. -/
theorem k4_rounds_ne {S Cl : Type} {b : Block S Cl} {Q : K4Pub} (hpl : b.place = k4Place Q)
    (hr : b.rounds = (entries Q.P Q.hp Q.g).map fun e => ({ entry := e } : Fmt.DeclaredRound)) :
    b.rounds ≠ [] := by
  intro h0
  have e := k4_partsCut_moves hpl hr
  have e0 : partsCut b = [] := by
    unfold partsCut
    rw [h0]
    rfl
  rw [e0] at e
  have hl := congrArg List.length e
  rw [List.length_map, k4RowIn_len, List.length_nil] at hl
  omega

/-- CONDITIONAL on h, hp, hb, hpl and hr. **IN THE WHOLE BOOK THE CUT AT K4's PLACE IS THE NUMBERS
OF MOVES OF THE PARTS OF K4's ROW.** -/
theorem k4_cut_fits {Xf : Type} {F : FileDescription Xf} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₁ F.Cl} (hb : b ∈ F.first.blocksInOrder) {Q : K4Pub} {W₀ Rc Xi Tr X : Type}
    (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard) (hpl : b.place = k4Place Q)
    (hr : b.rounds = (entries Q.P Q.hp Q.g).map fun e => ({ entry := e } : Fmt.DeclaredRound)) :
    B.cuts.lookup b.place =
      some ((k4Row (Rc := Rc) (X := X) Q cells weights tokens look).map (·.moves.length)) := by
  rw [bookWhole_cut_first h hp hb (k4_rounds_ne hpl hr),
    k4_partsCut_row cells weights tokens look hpl hr]

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4_rounds_ne
#print axioms ProofFile.Honest.K4.W.k4_cut_fits
