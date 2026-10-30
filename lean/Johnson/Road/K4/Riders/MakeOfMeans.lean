-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/MakeOfMeans.lean: THE LINE make OF K4's ROW's STRUCTURE `K4Keeps` (in the
form in which `k4Keeps_at`, K4AtMg.lean, takes it: every public item that K4's row makes, or that is
tied to an item which it opens, holds of the verifier's state behind an accept) OUT OF THE STRUCTURE
OF EQUATIONS `K4Means`, ITEM BY ITEM. One statement with its proof: the list, then a line an item.

  **`make_of_means`**: THE SIX ITEMS: leftOn m: its Bool is true by the equation · formsInT m 2
    "planes" | "join": idle at a feed-forward segment: the map of names gives them no run (hPl, hJo:
    two equations on the letter runs): true of every state · lookIn m 7 (hIn) · formsInT m 3 "own"
    (hOwn) · hasRow m (hRow): THREE LINES, each asked at a Yes inside the promise in front, each
    named below · hDoor: what the door's filling lets the row make at K4's place holds after it
    accepts (one named premise, whatever the door lays there).

WHO PAYS THE THREE LINES. hOwn: InT/FormsInTOwn.lean (`formsInT_own`, `inT_ofLink`) with the
equation formsInT, under its own named premises · hRow: Total/RowAtKept.lean and the files beside,
with the equation hasRow · hIn: `k3OnIn_of_kept` (LookOutKept.lean) under "K4's hearing takes just
as many slots as the public parameters say": typed by nobody.

Limits. The three lines, hDoor, hPl and hJo are premises. AT THE COMPOSED FILLING's ISSUES UP TO THE
SEVENTH hRow AND hOwn COULD NOT BE PAID: no item of the promise in front said "the index masks'
ledger has an entry left", nor what hOwn's premises ask of the verifier's state. K04_law, the law of
K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.K4Means
import Johnson.Road.K4.K4PubBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open Iop OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par seatS)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.First (S ModelPart Pub Meaning pubRowM moreItem)
open VerifiableInference.Desc.Sound (Frame Piece onQ MsgT)

variable {Xi P Tok Cl : Type} {rows cols nR kC : ℕ} {X : Verify.Public} {Fr : Frame}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X} {Z : P}
  {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}
  {q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT)} {par : Par}

/-- **The line make.** -/
theorem make_of_means (E : K4Means Mg D) (H : AtK4 links ps k m pl)
    (hDoor : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ nm ∈ (Mg.more.rows links pl).makes,
      Mg.pub (moreItem nm) (Z, (behindOf seatS q a τ o G').1) = true)
    (hPl : D.runs m 2 "planes" = []) (hJo : D.runs m 2 "join" = [])
    (hIn : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' →
      Mg.pub (.lookIn m 7) (Z, (behindOf seatS q a τ o G').1) = true)
    (hOwn : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' →
      Mg.pub (.formsInT m 3 "own") (Z, (behindOf seatS q a τ o G').1) = true)
    (hRow : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' →
      Mg.pub (.hasRow m) (Z, (behindOf seatS q a τ o G').1) = true) :
    ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ x ∈ (pubRowM Mg.more links pl).makes ++
        [Pub.formsInT m 3 "own", .formsInT m 2 "planes", .formsInT m 2 "join", .hasRow m],
      Mg.pub x (Z, (behindOf seatS q a τ o G').1) = true := by
  intro a τ fo o G' ha hu y x hx
  rw [k4_makes H] at hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hx
  rcases hx with ((rfl | rfl) | ⟨nm, hnm, rfl⟩) | rfl | rfl | rfl | rfl
  · exact hIn a τ fo o G' ha hu y
  · exact E.leftOnB m _
  · exact hDoor a τ fo o G' ha hu y nm hnm
  · exact hOwn a τ fo o G' ha hu y
  · rw [E.formsInT, hPl]
    rfl
  · rw [E.formsInT, hJo]
    rfl
  · exact hRow a τ fo o G' ha hu y

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.make_of_means
