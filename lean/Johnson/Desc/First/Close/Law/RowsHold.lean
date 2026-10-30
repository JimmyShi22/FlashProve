-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/RowsHold.lean: UNDER `OrderedV` A TYPED ROW HOLDS OF THE GROUP's
MESSAGES JUST IF THE PROGRAM's ROW, AS A VECTOR, HOLDS OF THE ARRANGED MESSAGE. Statements and
proofs.

K10's law ends in typed rows that hold of decoded messages (Front.lean, beside this file). A table
of joints speaks of the program's rows. This file is the step between, on vectors.
  `OrderedV.value`: under `OrderedV` (BatTie.lean) and the laws of the group's arrangement there is
    a list of all the typed rows' names, each once, as long as the program's list, such that at
    every number i and every pair u of message and randomness of the group's code: the value of
    typed row number i on u's message is the value of `rowVec` of the program's row number i on the
    arranged message; and the typed target is the reading of the program's.
  `OrderedV.holds_iff`: so typed row number i holds of u exactly if `rowVec` of the program's row
    number i, on the arranged message, gives the reading of that row's target.
Why. The arrangement carries a form's value (`Reshape.Laws.val`, `inj`); an arranged message is 0 on
the free rows (`up_free`, Johnson/Top/H/ArrAdd.lean); off them the typed row, arranged, is the
program's (`OrderedV.sent`, Teeth.lean).
Limits. The program's row stands as the vector `rowVec`: that its value on the arranged message is
what "the row says of the tables" is in other files' terms is not shown here. `OrderedV` is a
premise. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.Teeth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice Iop IOR KObj Cb Cb.Pv Johnson.Top.H
open Johnson.Top.H.ArrAdd (FreeAt up_free)

variable {S : Sig GE} (R : RowsK S) {B : Type} (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B))

/-- The value of a typed row is the value of the program's row on the arranged message. -/
theorem OrderedV.value {N : SlotNames R} {fr : ∀ ν, Slf GE (R.G.RowSt Sb ν) R.Sh.Cin.J}
    {x : (B → GE) × (∀ b, Sb b)} {σ : S.Smp} {z : Z.D} {e : E} {T : Statement} {L : GroupLayout}
    {rows : List OnBytes.Row} (hL : R.Sh.rho.Laws)
    (h : OrderedV R Sb sl Z N fr x σ z e T L rows) :
    ∃ ord : List (R.G.Row B), ord.Nodup ∧ (∀ ν, ν ∈ ord) ∧ ∃ hl : ord.length = rows.length,
      ∀ i (hi : i < ord.length),
        (R.G.claims x σ).1 ord[i] = readE (rows[i]'(hl ▸ hi)).target ∧
        ∀ u : (R.G.C.J → GE) × (R.G.C.Q → GE),
          ∑ j, R.G.rows sl ord[i] ((R.G.claims x σ).2 ord[i]) j * u.1 j =
            ∑ j, rowVec N T L (rows[i]'(hl ▸ hi)) j * (R.Sh.rho.up u).1 j := by
  obtain ⟨ord, o1, o2, o3, -, o5, o6⟩ := h
  have hl : ord.length = rows.length := by
    have := congrArg List.length o5
    simpa using this
  refine ⟨ord, o1, o2, hl, fun i hi => ⟨?_, fun u => ?_⟩⟩
  · have h3 := congrArg (fun l => l[i]?) o3
    simp only [List.getElem?_map] at h3
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (hl ▸ hi)] at h3
    exact Option.some.inj h3
  · have h5 := congrArg (fun l => l[i]?) o5
    simp only [List.getElem?_map] at h5
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (hl ▸ hi)] at h5
    have h6 := Option.some.inj h5
    have hv := hL.val (R.G.rows sl ord[i] ((R.G.claims x σ).2 ord[i])) (R.Sh.rho.up u)
    rw [hL.inj] at hv
    rw [← hv]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : FreeAt R.Sh j
    · rw [up_free R.Sh u j hj, mul_zero, mul_zero]
    · have h7 := congrFun h6 j
      have h8 : R.Sh.rho.fm (R.G.rows sl ord[i] ((R.G.claims x σ).2 ord[i])) j +
          fr ord[i] ((R.G.claims x σ).2 ord[i]) j = rowVec N T L (rows[i]'(hl ▸ hi)) j := h7
      rw [o6 _ _ j hj, add_zero] at h8
      rw [h8]

/-- **A typed row holds of the group's messages just if the program's row, as a vector, holds of the
arranged message.** -/
theorem OrderedV.holds_iff {N : SlotNames R} {fr : ∀ ν, Slf GE (R.G.RowSt Sb ν) R.Sh.Cin.J}
    {x : (B → GE) × (∀ b, Sb b)} {σ : S.Smp} {z : Z.D} {e : E} {T : Statement} {L : GroupLayout}
    {rows : List OnBytes.Row} (hL : R.Sh.rho.Laws)
    (h : OrderedV R Sb sl Z N fr x σ z e T L rows) :
    ∃ ord : List (R.G.Row B), ord.Nodup ∧ (∀ ν, ν ∈ ord) ∧ ∃ hl : ord.length = rows.length,
      ∀ i (hi : i < ord.length) (u : (R.G.C.J → GE) × (R.G.C.Q → GE)),
        (∑ j, R.G.rows sl ord[i] ((R.G.claims x σ).2 ord[i]) j * u.1 j =
            (R.G.claims x σ).1 ord[i]) ↔
          ∑ j, rowVec N T L (rows[i]'(hl ▸ hi)) j * (R.Sh.rho.up u).1 j =
            readE (rows[i]'(hl ▸ hi)).target := by
  obtain ⟨ord, o1, o2, hl, o⟩ := OrderedV.value R Sb sl Z hL h
  refine ⟨ord, o1, o2, hl, fun i hi u => ?_⟩
  rw [(o i hi).1, (o i hi).2 u]

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.OrderedV.value
#print axioms VerifiableInference.Desc.First.Close.OrderedV.holds_iff
