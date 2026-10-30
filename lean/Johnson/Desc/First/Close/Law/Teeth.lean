-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/Teeth.lean: WHAT THE PREMISE `OrderedV` OF K10's LAW ON VECTORS ASKS ON
THE ROWS THAT ARE SENT, AND THAT IT CAN FAIL. Statements and proofs.

`OrderedV` (BatTie.lean, beside this file) lets each typed row have further weights fr. They are 0
off the free rows of the cube. So they cannot make up for a typed row that is not the program's.
  `OrderedV.sent`: under `OrderedV` there is a list of all the typed rows' names, each once, as long
    as the program's list of rows, such that at every number i and every index j of the fold's input
    code that is no free row: typed row number i, arranged, at j IS `rowVec` of the program's row
    number i at j.
  `OrderedV.refuted`: if ONE typed row, arranged, differs at ONE index that is no free row from
    `rowVec` of every row of the program's list: `OrderedV` is false, whatever the further weights.
Limits. No value is written here: that some data meet `OrderedV` is not shown. Nothing on soundness,
on an honest prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.BatTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice Iop IOR KObj Cb Cb.Pv Johnson.Top.H
open Johnson.Top.H.ArrAdd (FreeAt)

variable {S : Sig GE} (R : RowsK S) {B : Type} (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B))

/-- On the rows that are sent the typed rows ARE the program's. -/
theorem OrderedV.sent {N : SlotNames R} {fr : ∀ ν, Slf GE (R.G.RowSt Sb ν) R.Sh.Cin.J}
    {x : (B → GE) × (∀ b, Sb b)} {σ : S.Smp} {z : Z.D} {e : E} {T : Statement} {L : GroupLayout}
    {rows : List OnBytes.Row} (h : OrderedV R Sb sl Z N fr x σ z e T L rows) :
    ∃ ord : List (R.G.Row B), ord.Nodup ∧ (∀ ν, ν ∈ ord) ∧ ∃ hl : ord.length = rows.length,
      ∀ i (hi : i < ord.length) j, ¬ FreeAt R.Sh j →
        R.Sh.rho.fm (R.G.rows sl ord[i] ((R.G.claims x σ).2 ord[i])) j =
          rowVec N T L (rows[i]'(hl ▸ hi)) j := by
  obtain ⟨ord, o1, o2, -, -, o5, o6⟩ := h
  have hl : ord.length = rows.length := by
    have := congrArg List.length o5
    simpa using this
  refine ⟨ord, o1, o2, hl, fun i hi j hj => ?_⟩
  have h5 := congrArg (fun l => l[i]?) o5
  simp only [List.getElem?_map] at h5
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (hl ▸ hi)] at h5
  have h6 := congrFun (Option.some.inj h5) j
  rw [← h6]
  show _ = R.Sh.rho.fm (R.G.rows sl ord[i] ((R.G.claims x σ).2 ord[i])) j +
    fr ord[i] ((R.G.claims x σ).2 ord[i]) j
  rw [o6 _ _ j hj, add_zero]

/-- **`OrderedV` can fail**: further weights do not make up for ONE typed row that is not the
program's on a row that is sent. -/
theorem OrderedV.refuted {N : SlotNames R} {fr : ∀ ν, Slf GE (R.G.RowSt Sb ν) R.Sh.Cin.J}
    {x : (B → GE) × (∀ b, Sb b)} {σ : S.Smp} {z : Z.D} {e : E} {T : Statement} {L : GroupLayout}
    {rows : List OnBytes.Row} (ν₀ : R.G.Row B) (j : R.Sh.Cin.J) (hj : ¬ FreeAt R.Sh j)
    (hne : ∀ w ∈ rows,
      R.Sh.rho.fm (R.G.rows sl ν₀ ((R.G.claims x σ).2 ν₀)) j ≠ rowVec N T L w j) :
    ¬ OrderedV R Sb sl Z N fr x σ z e T L rows := by
  intro h
  obtain ⟨ord, -, o2, hl, o5⟩ := OrderedV.sent R Sb sl Z h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (o2 ν₀)
  exact hne _ (List.getElem_mem (hl ▸ hi)) (o5 i hi j hj)

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.OrderedV.sent
#print axioms VerifiableInference.Desc.First.Close.OrderedV.refuted
