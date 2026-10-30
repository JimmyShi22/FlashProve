-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/NamesOfBuilt.lean: THE TWO LAST PREMISES ON LETTERS OF hSt_wide
(Johnson/Road/K4/FormsStWide.lean), WHERE THE NAMES ARE THE BUILT SEGMENTS' OWN: the list of a
segment's arrays' names that the layers' arm off the public parameters reads (uLAt,
Johnson/Road/K4/ULayAt.lean, at its meant filling) is the list that the pinned value's structure A
reads, wherever A's data of what is sent are the composed meaning's and A's number is the segment's.

  `namesOf built l`: the names of segment l's arrays, off a list of built segments; no names where
    the list has no entry l.
  `names_map`: that is entry l of the list of all segments' names.
  `hnm_built`: hSt_wide's hnm at names := namesOf Dm.built.
  `hSt_built`: hSt_wide with hnm struck: in its place two equations on A's letters.
No new argument.
Limits. PREMISES of hSt_built, none paid here: those of hSt_wide but hnm · huL reads Dm.uL =
uLAt X (namesOf Dm.built) · hAD: A's list of lists of names is the composed meaning's (by the
definition where A.D is made of Dm.sent) · hAl: A's number is m. THE SAME TEXT AS namesOf STANDS IN
ANOTHER FILE OF CLOSED LETTERS (names3, Johnson/P5J/LettersAt3Lay.lean, at the
built segments of the public parameters): it was typed there from a text of ours that is not in this
repository; the two are held together by no Lean. WHAT IS SHOWN AT THE WIDER MEANING COUNTS ONLY
WHEN THE BRIDGE FROM IT TO THE COMPOSED ONE IS PAID. Met through Lean at no
member. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.

-/
import Johnson.Road.K4.FormsStWide

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4

open Iop OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Road.K4.Rec (RecPlan openAllB arraysPlanB)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.First (S ModelPart Meaning)
open VerifiableInference.Desc.First.Look (tlAt)
open VerifiableInference.Desc.Sound (Frame Piece onQ MsgT StatedIs mgWide MgData WideData)

/-- The names of a segment's arrays, off a list of built segments. -/
def namesOf (built : Array Stages.LinkH) (l : ℕ) : Array (ℕ × String) :=
  ((built[l]?).map (·.arrayOf)).getD #[]

/-- That is entry l of the list of all segments' names. -/
theorem names_map (built : Array Stages.LinkH) (l : ℕ) :
    namesOf built l = (built.map (·.arrayOf)).getD l #[] := by
  unfold namesOf
  simp [Array.getD_eq_getD_getElem?]

variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X) (E : WideData P)
  (Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)) {Z : P}
  {links : List ModelPart} {ps : List Place} {k m : ℕ}
  {q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT)} {par : Par}

/-- hSt_wide's hnm at the built segments' own names, under hAD hAl. -/
theorem hnm_built (A : PinPlan (CellsK rows cols)) (hAD : A.D.arrayOf = Dm.sent.arrayOf)
    (hAl : A.link = m) : namesOf Dm.built m = A.D.arrayOf.getD A.link #[] := by
  rw [hAD, hAl]
  exact names_map Dm.built m

/-- **forms_pins' hSt at the wider meaning's own data and the built segments' own names**, under Em
huL hAD hAl hO hS htl hCells. -/
theorem hSt_built (A : PinPlan (CellsK rows cols))
    (Em : K4Means (mgWide Dm E Mg) (k4DataWide Dm E Mg))
    (huL : Dm.uL = uLAt X (namesOf Dm.built)) (hAD : A.D.arrayOf = Dm.sent.arrayOf)
    (hAl : A.link = m) (hO : openAllB (k4DataWide Dm E Mg).moreL links ps k m = true)
    (hS : ∀ a τ fo o G',
      onQ (k4DataWide Dm E Mg).N (mgWide Dm E Mg) links ps (fun s => (Z, s)) k a →
      a.1.failed = none → Yes seatS par q a τ fo o G' →
      ∀ a₀, a.1.here = .lay a₀ → PscRun.Sized a₀.F)
    (htl : tlAt X m = some par.hp.tl) {own : List (ℕ × ℕ)} {R : RecPlan} {n m' : ℕ}
    (hCells : arraysPlanB A par.hp.tl own R n m' = true) :
    ∀ a τ fo o G', onQ (k4DataWide Dm E Mg).N (mgWide Dm E Mg) links ps (fun s => (Z, s)) k a →
      a.1.failed = none → Yes seatS par q a τ fo o G' →
      StatedIs (k4DataWide Dm E Mg).St (uLay par.hp.tl fun _ B => matsOfB A par.hp.tl B)
        (behindOf seatS q a τ o G').1 :=
  hSt_wide Dm E Mg A Em (namesOf Dm.built) huL hO hS htl (hnm_built Dm A hAD hAl) hCells

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.names_map
#print axioms OnBytes.Road.K4.hnm_built
#print axioms OnBytes.Road.K4.hSt_built
