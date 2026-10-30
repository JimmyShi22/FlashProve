-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Walk/Shape/ClearForms.lean: THE FRAME's "cleared" (clearWith,
Johnson/Desc/First/Walk/Frame.lean) TURNS NO ROW's MAKE: the makes of the statement's rows (formsOf,
Johnson/Desc/First/Shape/Forms.lean) behind it are those in front. One general law with its two
fillings; nothing is evaluated.

Why. Where the link leaves a row, "cleared" turns the statement: one ledger of one message loses an
entry (the pending row itself goes to the pile, not into the statement). A message's sample rows and
a group's open rows stay.

  `forms_taken`: a statement whose one message gets another ledger has the same makes.
  **`clear_forms`**: clearWith … s = .ok t, at the pending row's own text: formsOf t.st = formsOf
    s.st.
  `clearHead_forms`: the same for the head's tail (tailHead).

Limits. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Walk.Shape.ClearRow
import Johnson.Desc.First.Shape.Forms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Shape
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.Pend (pendingRowO pendingRowO_means)
open VerifiableInference.Desc.First.Pend.Shape (means_cut)
open VerifiableInference.Desc.First.Close (countsHead leftHead tailHead)
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Props

theorem forms_taken (St : Statement) (im : Nat) (l : Ledger) :
    formsOf { St with oracles := St.oracles.modify im fun x => { x with ledger := some l } } =
      formsOf St := by
  unfold formsOf
  dsimp only
  rw [orc_same St.oracles im (fun x => { x with ledger := some l }) fun _ => rfl]

theorem clear_forms {X : LinkPub} {lay : WsLay} {lin : LinShape}
    {counts : S → Except String Unit} {left : S → Option WsForkOut} {s t : S}
    (h : clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t) :
    formsOf t.st = formsOf s.st := by
  obtain ⟨C, F, -, hF, -, k, r, -, hq⟩ := clearWith_iff.1 h
  rcases hq with ⟨-, hl⟩ | ⟨w, q, os, -, hr, hl⟩
  · obtain ⟨rfl, -⟩ := (leave_iff hF t).1 hl
    rfl
  · have hF' : ({ s with out := pendingKept s.out q, st := { s.st with oracles := os } } :
        S).fork? = some F := hF
    obtain ⟨rfl, -⟩ := (leave_iff hF' t).1 hl
    obtain ⟨-, x, l, -, -, -, -, -, rfl⟩ :=
      (means_cut _ _ _ _ _ _ _ _).1 ((pendingRowO_means _ _ _ _ _ _ _ _).1 hr)
    exact forms_taken s.st s.out.indexMasks _

theorem clearHead_forms {X : LinkPub} {lay : WsLay} {lin : LinShape} {s t : S}
    (h : tailHead X lay lin s = .ok t) : formsOf t.st = formsOf s.st :=
  clear_forms (counts := countsHead) (left := leftHead) h

end Johnson.Desc.First.Walk.Shape

#print axioms Johnson.Desc.First.Walk.Shape.clear_forms
#print axioms Johnson.Desc.First.Walk.Shape.clearHead_forms
#print axioms Johnson.Desc.First.Walk.Shape.forms_taken
