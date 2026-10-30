-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/CellsAt.lean: the table of cells that the tie of the smallness test reads, as a
term: segment, the pair with the verifier's state, the witness, an array's number, row, column ↦ a
field element.

  `cellsAt cs arr ms N m a w t r c`
      where the verifier's state `a.2` has an open segment's part `p` (`K9.segAt?`,
      Johnson/Desc/First/Batch/FormsIn.lean): the cell (r, c) of the array that stands at place `t` of
      the open link's own list `arrayOf` (link, name), read through `dataQ (N.group m) p`
      (Johnson/Desc/Sound/FormsQ.lean) off the witness's tables at the seats (`seatTab`,
      Johnson/Desc/Sound/BordersFill.lean); 0 where the state has no such part.
  `cellsAt_of_part`   at a state with a part: the first arm.
  `cellsAt_none`      at a state without one: 0.
  `cellsAt_congr`     two witnesses whose tables agree at the seats of `N.group m` give one table.

Why this accessor. `dataQ` is the one through which the sentences "forms", "formsT" and "total" read
the witness: the tie has to speak of the same cells, or the two have nothing to join. The choice of
the term is the composed meaning's; this file types it. It is general in the type `Cells` of
the witness's first part, as `seatTab` is. The composed meaning uses it at `CellsQ rows cols`; that
type is declared in Johnson/Desc/Sound/MgAll.lean, which is to import this file, so it cannot be
named here.

Limits. Beyond the list's end `arrayOf.getD t default` is (0, ""): the cell of that pair, in silence.
That the numbers which the tie reads off the state's plan are places of that list is not shown
here. At a seat that is no member's `seatTab` is the zero message. Nothing on soundness.

-/
import Johnson.Desc.Sound.FormsQ
import Johnson.Desc.Sound.BordersFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.First (Numbers)

variable {P Cells Tok : Type}

/-- **The table of cells at segment m.** -/
noncomputable def cellsAt (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)
    (a : P × First.S) (w : Wit Cells Tok MsgT) (t r c : ℕ) : Cb.Gl.E :=
  match K9.segAt? a.2 with
  | some p =>
    let x := ((a.2.link?.map fun (L : OnBytes.Model.LinkCtx) => L.arrayOf).getD #[]).getD t default
    (dataQ (N.group m) p (seatTab cs arr ms w)).cell x.1 x.2 r c
  | none => 0

/-- At a state with an open segment's part: the first arm. -/
theorem cellsAt_of_part (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)
    (a : P × First.S) (w : Wit Cells Tok MsgT) (t r c : ℕ) (p : K9.Part)
    (h : K9.segAt? a.2 = some p) :
    cellsAt cs arr ms N m a w t r c =
      (dataQ (N.group m) p (seatTab cs arr ms w)).cell
        (((a.2.link?.map fun (L : OnBytes.Model.LinkCtx) => L.arrayOf).getD #[]).getD t default).1
        (((a.2.link?.map fun (L : OnBytes.Model.LinkCtx) => L.arrayOf).getD #[]).getD t default).2 r c := by
  simp only [cellsAt, h]

/-- At a state without one: 0. -/
theorem cellsAt_none (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)
    (a : P × First.S) (w : Wit Cells Tok MsgT) (t r c : ℕ)
    (h : K9.segAt? a.2 = none) : cellsAt cs arr ms N m a w t r c = 0 := by
  simp only [cellsAt, h]

/-- Two witnesses whose tables agree at the seats of segment m's own list give one table. -/
theorem cellsAt_congr (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)
    (a : P × First.S) (w w' : Wit Cells Tok MsgT)
    (h : ∀ x ∈ N.group m, seatTab cs arr ms w x = seatTab cs arr ms w' x) (t r c : ℕ) :
    cellsAt cs arr ms N m a w t r c = cellsAt cs arr ms N m a w' t r c := by
  unfold cellsAt
  cases K9.segAt? a.2 with
  | none => rfl
  | some p =>
    show (dataQ (N.group m) p (seatTab cs arr ms w)).cell _ _ r c =
      (dataQ (N.group m) p (seatTab cs arr ms w')).cell _ _ r c
    rw [dataQ_congr (N.group m) p _ _ h]

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.cellsAt_of_part
#print axioms VerifiableInference.Desc.Sound.cellsAt_none
#print axioms VerifiableInference.Desc.Sound.cellsAt_congr
