-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/SharedRowTwelve.lean: THE SHARED CHAIN's LAST BORDER HAS THE NUMBER 12, AT THE SEATED IOP's OWN TERM: at
every three rows of pieces T that hold its sub-protocols (`OfDesc (F0T o Zp Np cF) T`): 1 + T.l₂.length = 12. A
joining of two theorems of other files (Johnson/Road/Tables/TablesLen.lean: `len₂_of`;
FlatLengths.lean: `closed_lengths`).

Why. TablesFitR's field SH₃ (Johnson/P5J/TopTablesR.lean) and the premises hD, hX of its payer
(Johnson/Desc/Last/ShapeDoorField.lean) speak of the border `1 + T.l₂.length`; the shared table's own lemmas on
its last border speak of the numeral 12.

  `shared_row_twelve`   1 + T.l₂.length = 12 · in the goals' scope, from `LaidAt` at any o.
  `of_twelve`           what holds at 12 holds at 1 + T.l₂.length (p is a letter): the form in which it is spent.
  `shared_places_plain` A NEGATIVE TEST OF THE NUMBER: without the split the shared table has 11 places.
What is not claimed. That `LaidAt` can be met. Nothing on soundness.

-/
import Johnson.Road.Tables.TablesLen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc.Sound (OfDesc ThreeAt)
open VerifiableInference.Desc.Shared (sharedPlaces)
open OnBytes.Maker (WholeD)
open OnBytes.Road.Tables (len₂_of closed_lengths)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {o : ProofFile.SecondHashFunctionArgument}
  {C : _root_.Run.PQ.CK} {D' : WholeD} {all : List OnBytes.Maker.LeftT} {X₁ X₂ W : Type}

/-- **The shared chain's last border is number 12.** -/
theorem shared_row_twelve (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {T : ThreeAt C D' all (F0T o Zp Np cF) X₁ X₂ W}
    (h : OfDesc (F0T o Zp Np cF) T) : 1 + T.l₂.length = 12 :=
  (len₂_of hZ L h).trans (congrArg (fun x : ℕ × ℕ × ℕ => x.2.1) closed_lengths)

/-- What holds at 12 holds at the shared chain's last border. -/
theorem of_twelve (hZ : VerifierAndGoals.InScope Z = true) (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF)
    {T : ThreeAt C D' all (F0T o Zp Np cF) X₁ X₂ W} (h : OfDesc (F0T o Zp Np cF) T)
    (p : ℕ → Prop) (h12 : p 12) : p (1 + T.l₂.length) := by
  rw [shared_row_twelve hZ L h]
  exact h12

/-- A negative test of the number: without the split the table has a place fewer. -/
theorem shared_places_plain : (sharedPlaces false).length = 11 := by decide

end P5J

#print axioms P5J.shared_row_twelve
#print axioms P5J.of_twelve
#print axioms P5J.shared_places_plain
