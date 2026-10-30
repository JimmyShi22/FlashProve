-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/KeptNames.lean: THE ONE LINE `K4Kept` (K4Reads.lean: "the test of a name at
the table of joints' door that is of the sort rest says one thing at two states s, s' inside
the fence") PAID AT THE NAMES THAT ARE OPEN ACROSS K4's SUB-PROTOCOL, out of the structure of
equations `K4Means`. One definition, one statement with its proof: a name, an equation, a lemma "it
reads what the fence keeps".

  `restNames`: THE LIST, AS A TEST WITH CODE: without a segment: "K13.weightsOk" · "K12.bookInOrder"
    · "K12.seatsCarried" · "K12.msgShapes" · "K12.bookFits" · "K13.pileMasks" · "K13.pileWithin" ·
    "K13.oneRow"; at any segment: "frame.liveIs" · "frame.sentIs" · "pile.room" · "K8.lay7".
  `K4PileNames Mg tlP`: five equations more: on the pile's three names and on two of the approximate
    range proof's ("K8.lay7": open across K4's sub-protocol; "K8.funsThird": made by it).
    **`k4Kept_of_means`**: `K4Means Mg D` · `K4PileNames Mg` ⟹ `K4Kept Mg restNames Z`.

A NEW NAME OF ANOTHER KIND THAT IS OPEN ACROSS K4's SUB-PROTOCOL TURNS THIS FILE ALONE: one name in
the list, one equation in `K4Means`, one lemma. ("ledger.treesAre" is not of this sort: its test
reads the segment's ledger, which K4's sub-protocol turns: it has an arm of its own in
Riders/KeepsOfMeans.lean.)

Limits. The names that only carry a fact on
every reached state across many kinds' sub-protocols HAVE LEFT the composed meaning's door: THIRTEEN
(the weights' one · the proximity test's door's four · the pile's three · "pile.room" ·
"frame.liveIs" · "K8.lay7" · "K8.onThird" · "K8.funsThird"), and four conjuncts of "in order": a
theorem here that spends, keeps or makes one of them stands at a WIDER meaning than the composed one
(a bridge's side), and is carried to it by a bridge under facts on reached states that are owed.
Which names ARE open across K4's sub-protocol is a test on the door's filling (k4PubFit). K04_law,
the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.Riders.KeepsOfMeans
import Johnson.Desc.First.K8.Cond
import Johnson.Desc.First.K8.CondFuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Riders (weightsB_kept atFirstBook_kept atFirstSeats_kept
  atFirstShapes_kept)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc.Sound (MsgT)

variable {Xi P Tok : Type} {rows cols nR kC : ℕ} {X : Verify.Public}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X} {Z : P}

/-- The names whose tests read only what the fence keeps. -/
def restNames : Option ℕ → String → Bool
  | none, n => n == "K13.weightsOk" || n == "K12.bookInOrder" || n == "K12.seatsCarried" ||
      n == "K12.msgShapes" || n == "K12.bookFits" || n == "K13.pileMasks" ||
      n == "K13.pileWithin" || n == "K13.oneRow"
  | some _, n => n == "frame.liveIs" || n == "frame.sentIs" || n == "pile.room" || n == "K8.lay7"

/-- Five equations more, on the pile's three names and two of the approximate range proof's: beside
`K4Means`, so that that structure does not turn for names which are to leave the door. -/
structure K4PileNames (Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT))
    (tlP : ℕ → Option HTailF2) : Prop where
  pileMasks : ∀ a, Mg.pub (.more none "K13.pileMasks") a =
    VerifiableInference.Desc.K13.pileMasksC a.2
  pileWithin : ∀ a, Mg.pub (.more none "K13.pileWithin") a =
    VerifiableInference.Desc.K13.pileWithinC a.2
  oneRow : ∀ a, Mg.pub (.more none "K13.oneRow") a = VerifiableInference.Desc.K13.oneRowC a.2
  lay7 : ∀ m a, Mg.pub (.more (some m) "K8.lay7") a =
    (tlP m).any fun t => VerifiableInference.Desc.First.K8.Ready.lay7B t a.2
  funsThird : ∀ m a, Mg.pub (.more (some m) "K8.funsThird") a =
    VerifiableInference.Desc.First.K8.Ready.funsThirdB a.2

/-- **The line, at these names.** -/
theorem k4Kept_of_means (E : K4Means Mg D) {tlP : ℕ → Option HTailF2} (Ep : K4PileNames Mg tlP) :
    K4Kept Mg restNames Z := by
  refine ⟨fun seg name hn s s' h => ?_⟩
  obtain ⟨⟨al, hal⟩, hR⟩ := h
  cases seg with
  | none =>
    have e : name = "K13.weightsOk" ∨ name = "K12.bookInOrder" ∨ name = "K12.seatsCarried" ∨
        name = "K12.msgShapes" ∨ name = "K12.bookFits" ∨ name = "K13.pileMasks" ∨
        name = "K13.pileWithin" ∨ name = "K13.oneRow" := by
      simpa [restNames, or_assoc] using hn
    obtain ⟨al', hal', _⟩ := hR.here al hal
    have hrows : s'.rows = s.rows := by
      unfold VerifiableInference.Desc.First.S.rows
      rw [hal, hal', hR.out]
    rcases e with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [E.weightsOk, E.weightsOk, weightsB_kept hal hR]
    · rw [E.bookInOrder, E.bookInOrder, atFirstBook_kept hR]
    · rw [E.seatsCarried, E.seatsCarried, atFirstSeats_kept hR]
    · rw [E.msgShapes, E.msgShapes, atFirstShapes_kept hR]
    · rw [E.bookFits, E.bookFits]
      unfold VerifiableInference.Desc.K12.Door.atFirstFits
      rw [hR.book]
    · rw [Ep.pileMasks, Ep.pileMasks]
      unfold VerifiableInference.Desc.K13.pileMasksC
      rw [hrows, hR.out]
    · rw [Ep.pileWithin, Ep.pileWithin]
      unfold VerifiableInference.Desc.K13.pileWithinC VerifiableInference.Desc.K13.ledgersFitC
        VerifiableInference.Desc.K13.rowsWithinC
      rw [hrows, hR.st]
    · rw [Ep.oneRow, Ep.oneRow]
      unfold VerifiableInference.Desc.K13.oneRowC
      rw [hal, hal']
  | some j =>
    have e : name = "frame.liveIs" ∨ name = "frame.sentIs" ∨ name = "pile.room" ∨
        name = "K8.lay7" := by
      simpa [restNames, or_assoc] using hn
    rcases e with rfl | rfl | rfl | rfl
    · have e1 := E.liveIs j (Z, s)
      have e2 := E.liveIs j (Z, s')
      change Mg.pub (.more (some j) "frame.liveIs") _ = _ at e1 e2
      rw [e1, e2, liveIsB_kept hR]
    · rw [E.sentIs, E.sentIs, sentIsB_kept hR]
    · rw [E.room, E.room, roomIsB_kept hR]
    · rw [Ep.lay7, Ep.lay7]
      unfold VerifiableInference.Desc.First.K8.Ready.lay7B
      rw [hR.tl]

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.k4Kept_of_means
