-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/HereLinkBehind.lean: BEHIND AN ACCEPTING RUN OF K4's SUB-PROTOCOL FROM INSIDE THE
PROMISE IN FRONT, THE VERIFIER's STATE STANDS IN A LAYERS' SEGMENT, AND THE NUMBER THAT THE STATED
FUNCTIONS' ARM READS (linkNo, Johnson/Desc/Sound/StatedAll.lean) IS THE SEGMENT's m. One statement.

  **`here_link_behind`**: there is b with (behindOf …).1.here = .lay b, and linkNo of that state is
    m: the two premises hs and hl of hSt_pins (Johnson/Road/K4/ULayPins.lean), at that state.
    PREMISES: E : K4Means Mg D · hO : the six public items are open at border k (openAllB) · ha,
    hu: the state in front lies inside the promise and bears no mark · Y: the run accepts · hS: the
    ledger in front is Sized. They are premises of forms_pins (Johnson/Road/K4/FormsAtPins.lean)
    too.
WHY NOT FROM THE BOOK-KEEPING: the promise's test shapeAt (Johnson/Desc/First/Borders.lean) speaks
of the field link of the open segment's context; linkNo reads the field check.frame.link. That this
is m is the field link of RecIs (Johnson/Road/K4/Rec/Whole.lean), which recIs_run has behind an
accepting run.
Limits. hO rejects at the composed meaning's own small list of extra public tests: the statement
speaks at a wider meaning alone. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED.
Nothing on soundness.


-/
import Johnson.Road.K4.FormsAtPins
import Johnson.Desc.Sound.StatedAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open Iop OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Desc.First.K4.InT (segAt_lay)
open OnBytes.Road.K4.InT (kept_open)
open OnBytes.Road.K4.Rec (openAllB)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.First (S ModelPart Meaning)
open VerifiableInference.Desc.Sound (Frame Piece onQ MsgT linkNo)

variable {Xi P Tok Cl : Type} {rows cols nR kC : ℕ} {X : Verify.Public} {Fr : Frame}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X} {Z : P}
  {links : List ModelPart} {ps : List Place} {k m : ℕ}
  {q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT)} {par : Par}

/-- **Behind an accepting run: a layers' segment stands open, and its number is m.** -/
theorem here_link_behind (E : K4Means Mg D) (hO : openAllB D.moreL links ps k m = true)
    {a : S × Fr.E.Str} {τ : Tr (uLT (ckP .two) q.ds)} {fo : Forest.Heard} {o : Own} {G' : Fork}
    (ha : onQ D.N Mg links ps (fun s => (Z, s)) k a) (hu : a.1.failed = none)
    (Y : Yes seatS par q a τ fo o G')
    (hS : ∀ a₀, a.1.here = .lay a₀ → PscRun.Sized a₀.F) :
    ∃ b, (behindOf seatS q a τ o G').1.here = .lay b ∧
      linkNo (behindOf seatS q a τ o G').1 = m := by
  obtain ⟨_, b, _, _, _, _, _, _, _, hb, _⟩ := kept_open (kept_of_yes Y)
  obtain ⟨A', hA', _, eL⟩ := segAt_lay hb
  have Rc := recIs_run E hO ha hu Y hS hA'
  have hL : (behindOf seatS q a τ o G').1.link? = some b.L := by simp only [S.link?, hb]
  refine ⟨b, hb, ?_⟩
  unfold linkNo
  rw [hL]
  show b.L.check.frame.link = m
  rw [← eL]
  exact Rc.link

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.here_link_behind
