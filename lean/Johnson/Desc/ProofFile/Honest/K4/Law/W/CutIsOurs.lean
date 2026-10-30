-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/CutIsOurs.lean: CONDITIONAL. THE BOOK's MAKER CUTS THE
SUB-PROTOCOL OF THE LAYERS' OWN ROUNDS (kind K4) AS K4's OWN ROW IS CUT: PART FOR PART AS MANY
ROUNDS AS THE PART HAS MOVES.

What is here. PUBLIC DATA ALONE. Law/W/PlanRow.lean writes K4's row out as units of names and counts
(`k4Units`) and shows that the maker's cut (`partsCut`, Honest/BookOf.lean) is these units' lengths.
Law/ExactFresh/AtSide.lean has the verifier's table cut part by part as rows of the table
(`k4Rows`), and Law/TableFitsRows.lean shows, with no hypothesis, that our own cut (`cutOf`,
Johnson/Desc/K4/Honest/Front.lean) is these rows' lengths (`cut_eq`) and that each part of K4's row
has as many moves (`moves_cut`). Here the two writings of the row are tied. Statements and proofs.

  `k4Units_rows`: the units are the table's rows, each round as its name and its count of sent
      elements. No hypothesis.
  `k4_partsCut_ours`: **the maker's cut is our own cut.**
  `k4_partsCut_moves`: the maker's cut is the numbers of moves of the parts of K4's row AT THE
      SMALL INPUT (`k4RowIn`).
  `k4_partsCut_row`: **and of the parts of K4's row as the kind's half has it** (`k4Row`,
      Honest/K4/Part.lean: the same parts placed in the wider input: `Part.lift` keeps the number of
      moves).

Not shown here. hpl and hr, that the sub-protocol stands at K4's place and declares the entries of
K4's table, are hypotheses. The frame compares what a book's field cuts holds at a place with the
numbers of moves of the half's parts there (Honest/Frame.lean, in `chainSteps`). `k4_partsCut_row`
has the right side of that comparison. THAT A BOOK's FIELD cuts HOLDS THE MAKER's CUT AT K4's PLACE
IS NOT SPOKEN OF HERE. Nothing on a book, on coins, or on what a part sends.
No property is claimed.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.PlanRow
import Johnson.Desc.ProofFile.Honest.K4.Law.TableFitsRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W
open OnBytes.Desc.First.K4 (masked pointRd batchRd entries)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block)
open ProofFile.Honest.K4.ExactFresh

variable {S Cl : Type}

/-- The units are the table's rows, each round as its name and its count of sent elements. -/
theorem k4Units_rows (Q : K4Pub) :
    k4Units Q = (k4Rows Q).map (·.map fun d => (d.name.name, d.sent)) := by
  cases hg : (Q.g == 0) <;>
    simp [k4Units, k4TailUnits, k4Rows, maskedP, masked, pointRd, batchRd, nStack, hg,
      OnBytes.Model.RoundName.name]

variable {b : Block S Cl} {Q : K4Pub}

/-- CONDITIONAL: on hpl and hr. **THE MAKER's CUT IS OUR OWN CUT.** -/
theorem k4_partsCut_ours (hpl : b.place = k4Place Q)
    (hr : b.rounds = (entries Q.P Q.hp Q.g).map fun e => ({ entry := e } : Fmt.DeclaredRound)) :
    partsCut b = cutOf Q := by
  rw [k4_partsCut hpl hr, cut_eq, k4Units_rows, List.map_map]
  refine List.map_congr_left fun L _ => ?_
  exact List.length_map _

/-- CONDITIONAL: on hpl and hr. The maker's cut is the numbers of moves of K4's parts at the small
input. -/
theorem k4_partsCut_moves (hpl : b.place = k4Place Q)
    (hr : b.rounds = (entries Q.P Q.hp Q.g).map fun e => ({ entry := e } : Fmt.DeclaredRound)) :
    partsCut b = (k4RowIn Q).map (·.moves.length) := by
  rw [k4_partsCut_ours hpl hr]
  exact (eq_of_beq (moves_cut Q)).symm

/-- CONDITIONAL: on hpl and hr. **THE MAKER's CUT IS THE NUMBERS OF MOVES OF THE PARTS OF K4's ROW
AS THE KIND's HALF HAS IT.** -/
theorem k4_partsCut_row {W₀ Rc Xi Tr X : Type} (cells : Tr → Cells) (weights : W₀ → Weights)
    (tokens : Xi → Array Nat) (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    (hpl : b.place = k4Place Q)
    (hr : b.rounds = (entries Q.P Q.hp Q.g).map fun e => ({ entry := e } : Fmt.DeclaredRound)) :
    partsCut b =
      (k4Row (Rc := Rc) (X := X) Q cells weights tokens look).map (·.moves.length) := by
  rw [k4_partsCut_moves hpl hr]
  unfold k4Row
  rw [List.map_map]
  refine List.map_congr_left fun p _ => ?_
  exact (List.length_map _).symm

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4Units_rows
#print axioms ProofFile.Honest.K4.W.k4_partsCut_ours
#print axioms ProofFile.Honest.K4.W.k4_partsCut_moves
#print axioms ProofFile.Honest.K4.W.k4_partsCut_row
