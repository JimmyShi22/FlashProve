-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5KindOfTests.lean: kind K5: **THE KIND's SHARE IN THE FORM AtMgA.Kind (Johnson/P5J/RowsAtAll.lean) FROM THE HEAD AND BOOLS ALONE.** A joining: calls. It turns nothing of the condition (K5CondAt, Door/Law/K5LeftOfCond.lean) or of the theorem
k05_kind_of_cond (Door/Law/K05KindOfCond.lean).
The two sentences of the condition's part cells (K5CellsCond, Door/Law/K5RestCells.lean) want ONE inverse idx of the numbering. Here it is the closed term idxAt (At.sentAt Zp) (At.num Zp) (2 g + 1) (Johnson/Desc/First/Look/K3IdxAt.lean):
tie at it follows from the Bool tieWW g, whose only letter is g (tie_of_writtenW', Door/Law/K5TieWitness.lean); one at it is a theorem from the named test oneC (P5J.AtMgA.one_at, Johnson/P5J/K03OneOwnAt.lean).
SHAPED SO THAT LATER THEOREMS DROP IN: the forms «…_of_one» take the sentence one and the sentence pads as they stand: whoever proves either from the head calls these.
Compiled with the whole library.

(Where this and lean/THEOREM.md differ, the page holds.)
ONLY WHERE THE LIST OF Johnson/Desc/Laid/ProofAsks.lean HAS THE THIRTEEN TESTS OF ProofAsksFirstThirteenTests.lean AND THE HEAD OF Johnson/P5J/MgAtAll.lean HAS THE FIELDS opts · k3.

Main names:
  cells_of_one: (∀ g < 12, tieWW g = true) · (∀ g < 12, the sentence in which one_at ends, at 2 g + 1) → the premise cells of k05_kind_at_head₂ (Door/Law/K5AlongOfHead.lean), in its own text.
  **cells_of_written**: the same from (∀ g < 12, h.oneC (2 g + 1) = true).
  k05_kind_of_one: the head · the three equations on 𝔏 · k5PlansB₂ = true · the twelve tieWW · the twelve sentences one · pads → h.Kind 𝔏 .K5.
  **k05_kind_of_tests**: the head · the three equations on 𝔏 · k5PlansB₂ = true · the twelve tieWW [36 Bools without a letter] · the twelve oneC · offC [13 Bools at the public part] → h.Kind 𝔏 .K5.
IS IT EMPTY HERE? IMPLICATIONS. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/). NONE OF THE 49 BOOLS IS SHOWN true IN LEAN. THE KIND's LAW IS NOT PROVED.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5AlongOfHead
import Johnson.Desc.First.Att.Door.Law.K5TieWitness
import Johnson.Desc.First.Att.Door.Law.K5CellsOfTests
import Johnson.Desc.First.Att.Door.Law.K5PadsOfOffC

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Door
open OnBytes OnBytes.Flat OnBytes.Model OnBytes.Maker OnBytes.Slice KObj
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt sigListCalls idxAt)
open VerifiableInference.OnPublicFiles (OneNumber)
open P5J (AtMg AtMgA F0T TS Free)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **The condition's part cells, at the closed inverse of the numbering: tie from a Bool whose only letter is g; one as it stands.** -/
theorem cells_of_one (hT : ∀ g, g < 12 → tieWW g = true)
    (hO : ∀ g, g < 12 → OneNumber (P5J.At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 (P5J.At.num Zp)
      (idxAt (P5J.At.sentAt Zp) (P5J.At.num Zp) (2 * g + 1)) (_root_.Meaning.tlAt (P5J.At.X Zp)) (2 * g + 1)
      (fun j : Fin (sigListCalls (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 (2 * g + 1)).length =>
      (h.toAtMg.𝔇 h.𝔇).seat3 (2 * g + 1) false j.1) (h.toAtMg.𝔇 h.𝔇).arr id) :
    ∀ g, g < 12 → ∀ (a : Attention.Plan) (x₁ : Look.Place), (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ → ∃ idx, K5CellsCond h a x₁ idx := by
  intro g hg a x₁ ha hx
  have hxl : x₁.link = 2 * g + 1 := VerifiableInference.OnPublicFiles.lookAt_link hx
  refine ⟨idxAt (P5J.At.sentAt Zp) (P5J.At.num Zp) (2 * g + 1), tie_of_writtenW' h (pins_at_head h.toAtMg).1 hg ha hx (hT g hg), ?_⟩
  rw [hxl]
  exact hO g hg

/-- **The same, with one from the named test oneC (Johnson/P5J/K03OneOwnAt.lean).** -/
theorem cells_of_written (hT : ∀ g, g < 12 → tieWW g = true) (hB : ∀ g, g < 12 → h.oneC (2 * g + 1) = true) :
    ∀ g, g < 12 → ∀ (a : Attention.Plan) (x₁ : Look.Place), (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ → ∃ idx, K5CellsCond h a x₁ idx :=
  cells_of_one h hT fun g hg => h.one_at (by omega) (hB g hg)

variable (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
  (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
  (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
include q₁ q₂ q₃

/-- The kind's share, with the sentences one and pads as they stand. -/
theorem k05_kind_of_one (hW : k5PlansB₂ = true) (hT : ∀ g, g < 12 → tieWW g = true)
    (hO : ∀ g, g < 12 → OneNumber (P5J.At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 (P5J.At.num Zp)
      (idxAt (P5J.At.sentAt Zp) (P5J.At.num Zp) (2 * g + 1)) (_root_.Meaning.tlAt (P5J.At.X Zp)) (2 * g + 1)
      (fun j : Fin (sigListCalls (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 (2 * g + 1)).length =>
      (h.toAtMg.𝔇 h.𝔇).seat3 (2 * g + 1) false j.1) (h.toAtMg.𝔇 h.𝔇).arr id)
    (pads : PadsAll h) : h.Kind 𝔏 KindName.K5 :=
  k05_kind_at_head₂ h 𝔏 q₁ q₂ q₃ hW pads (cells_of_one h hT hO)

/-- **THE KIND's SHARE IN THE FORM AtMgA.Kind (RowsAtAll.lean), FROM THE HEAD AND BOOLS ALONE.** -/
theorem k05_kind_of_tests (hW : k5PlansB₂ = true) (hT : ∀ g, g < 12 → tieWW g = true)
    (hB : ∀ g, g < 12 → h.oneC (2 * g + 1) = true) (hC : h.toAtMg.offC = true) : h.Kind 𝔏 KindName.K5 :=
  k05_kind_at_head₂ h 𝔏 q₁ q₂ q₃ hW (pads_of_offC h hC) (cells_of_written h hT hB)

end H2K5.Door

#print axioms H2K5.Door.cells_of_one
#print axioms H2K5.Door.cells_of_written
#print axioms H2K5.Door.k05_kind_of_one
#print axioms H2K5.Door.k05_kind_of_tests
