-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/FormsStWide.lean: THE PREMISE hSt OF THE LINE "forms" AT THE PINNED VALUE
(forms_pins, Johnson/Road/K4/FormsAtPins.lean), IN ITS OWN WORDS, where the data's letter St is the
one stated function at the layers' arm off the public parameters (uLAt,
Johnson/Road/K4/ULayAt.lean); and at the wider meaning's own data (k4DataWide,
Johnson/Road/K4/K4MeansAtWide.lean).

  `hSt_of_arm`: forms_pins' hSt to the letter, at every meaning Mg and data D with K4Means.
  `hSt_wide`: the same at D := k4DataWide Dm E Mg, where the composed meaning's parameter uL is
    uLAt.
No new argument: hSt_pins, named_of_arrays (Johnson/Road/K4/ULayPins.lean); here_link_behind
(Johnson/Road/K4/HereLinkBehind.lean).
Limits. PREMISES of hSt_of_arm, none paid here:
  E: K4Means at Mg and D · hStD: D.St is Stated.of (uBySort (uLAt X names) uA uH).
  hO: the test openAllB: the six public items that RecIs spends are open at border k. THREE OF THE
    SIX LEAVE THE TABLE's DOOR WITH THE COMPOSED FILLING `mgAll` (by reading, not held against
    the file that ships): THERE hO SAYS FALSE AND THIS IS IDLE: it speaks at a wider meaning alone.
  hS: at an accepting run inside the promise in front the ledger in front has the right sizes (a
    field of KeptAsks, which forms_pins' premise asks gives).
  htl: tlAt X m is the group's public parameters' structure (tlAt_plan,
    Johnson/Road/K4/K4PinsScope.lean) · hnm: names m is A's list of arrays' names · hCells: the test
    arraysPlanB (forms_pins' own premise): spent for "every symbol array has a name" alone.
Of hSt_wide: Em (K4Means at the wider meaning and its data) · huL: Dm.uL = uLAt X names: AN EQUATION
ON A PARAMETER OF THE COMPOSED MEANING THAT IS OPEN TODAY · the other five as above. WHAT IS SHOWN
AT THE WIDER MEANING COUNTS ONLY WHEN THE BRIDGE FROM IT TO `mgAll`'s IS PAID. Met through
Lean at no member. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on
soundness.


-/
import Johnson.Road.K4.ULayPins
import Johnson.Road.K4.HereLinkBehind
import Johnson.Road.K4.K4MeansAtWide

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
open VerifiableInference.Desc.Sound (Frame Piece onQ MsgT Stated UFn StatedIs uBySort mgWide MgData
  WideData)

section
variable {Xi P Tok Cl : Type} {rows cols nR kC : ℕ} {X : Verify.Public} {Fr : Frame}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X} {Z : P}
  {links : List ModelPart} {ps : List Place} {k m : ℕ}
  {q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT)} {par : Par}

/-- **forms_pins' hSt, to the letter**, under E hStD hO hS htl hnm hCells. -/
theorem hSt_of_arm (A : PinPlan (CellsK rows cols)) (E : K4Means Mg D)
    (names : ℕ → Array (ℕ × String)) (uA uH : ℕ → UFn)
    (hStD : D.St = Stated.of (uBySort (uLAt X names) uA uH))
    (hO : openAllB D.moreL links ps k m = true)
    (hS : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ a₀, a.1.here = .lay a₀ → PscRun.Sized a₀.F)
    (htl : tlAt X m = some par.hp.tl) (hnm : names m = A.D.arrayOf.getD A.link #[])
    {own : List (ℕ × ℕ)} {R : RecPlan} {n m' : ℕ}
    (hCells : arraysPlanB A par.hp.tl own R n m' = true) :
    ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' →
      StatedIs D.St (uLay par.hp.tl fun _ B => matsOfB A par.hp.tl B)
        (behindOf seatS q a τ o G').1 := by
  intro a τ fo o G' ha hu Y
  obtain ⟨b, hs, hl⟩ := here_link_behind E hO ha hu Y (hS a τ fo o G' ha hu Y)
  rw [hStD]
  exact hSt_pins A X names uA uH hs hl htl hnm (named_of_arrays A hCells)

end

section
variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X) (E : WideData P)
  (Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)) {Z : P}
  {links : List ModelPart} {ps : List Place} {k m : ℕ}
  {q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT)} {par : Par}

/-- **The same at the wider meaning's own data**, under Em huL hO hS htl hnm hCells. -/
theorem hSt_wide (A : PinPlan (CellsK rows cols))
    (Em : K4Means (mgWide Dm E Mg) (k4DataWide Dm E Mg)) (names : ℕ → Array (ℕ × String))
    (huL : Dm.uL = uLAt X names)
    (hO : openAllB (k4DataWide Dm E Mg).moreL links ps k m = true)
    (hS : ∀ a τ fo o G',
      onQ (k4DataWide Dm E Mg).N (mgWide Dm E Mg) links ps (fun s => (Z, s)) k a →
      a.1.failed = none → Yes seatS par q a τ fo o G' →
      ∀ a₀, a.1.here = .lay a₀ → PscRun.Sized a₀.F)
    (htl : tlAt X m = some par.hp.tl) (hnm : names m = A.D.arrayOf.getD A.link #[])
    {own : List (ℕ × ℕ)} {R : RecPlan} {n m' : ℕ}
    (hCells : arraysPlanB A par.hp.tl own R n m' = true) :
    ∀ a τ fo o G', onQ (k4DataWide Dm E Mg).N (mgWide Dm E Mg) links ps (fun s => (Z, s)) k a →
      a.1.failed = none → Yes seatS par q a τ fo o G' →
      StatedIs (k4DataWide Dm E Mg).St (uLay par.hp.tl fun _ B => matsOfB A par.hp.tl B)
        (behindOf seatS q a τ o G').1 :=
  hSt_of_arm A Em names Dm.uA Dm.uH
    (show Stated.of (uBySort Dm.uL Dm.uA Dm.uH) = _ by rw [huL]) hO hS htl hnm hCells

end

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.hSt_of_arm
#print axioms OnBytes.Road.K4.hSt_wide
