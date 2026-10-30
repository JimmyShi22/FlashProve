-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Says2.lean: what the first claim of group 3 and the claims of group 4 of the layers'
own rounds say, and what a digit of a norm's row is worth on true reads.

  `rowBatch_says` (group 3, first claim): the hidden sum from which the row products' token sumcheck
      starts is the sum of the hidden row products under the powers omV.
  `shown_says` (group 4): the four hidden end values of norm i are worth what the fields a, b, Rlo,
      Rhi of the norm's row, made of its digits at the sumcheck's end point, are worth.
  `digitsAt_value`: on true short tables of the matrix ar at a token point, digit n of norm ν is
      worth byte n of the library's ledger of that norm, extended over the positions, there.

Limits. Identities in a world, at one point each: no draw, no soundness, nothing from the field to
the integers. The third has the library's premises on the tables; nothing here shows that they can
hold at the layout of a shipped example. No theorem on a run of `verify-on-bytes` is called.

-/
import Johnson.Road.K4.ListsTie
import OnBytes.Desc.First.K4.RowsLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Lay Heard Pub Ten aff0)
open Inst.Model.FFSeg (Dim Cell led)
open Blocks (ext)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K}

/-- Group 3, first claim. -/
theorem rowBatch_says (hρ : Numerals ρ) (y : Lay) (H : Heard)
    (hz : (Desc.First.K4.rowBatchForm y H).value ρ W = 0) :
    W.slot H.tV.sCl = ∑ i ∈ range (ledNP y.h.xl * y.NI),
      ρ.val (H.omV.getD i zeroE) * W.slot (H.sPv + i) := by
  rw [rowBatchForm_eq, rowBatch_value ρ W hρ] at hz
  exact sub_eq_zero.mp hz

/-- Group 4. -/
theorem shown_says {v : Env} {H : Heard} {l : List Aff}
    (h : Desc.First.K4.rowsForms v H = some l) (hz : ∀ f ∈ l, f.value ρ W = 0) {i : ℕ}
    (hi : i < v.y.NI) {D : ℕ → Aff} (hD : Desc.First.K4.digitsAt v "r_tV" i = some D) :
    W.slot (H.tV.sEnd + 4 * i + 0) = (Desc.First.P6.Row.ofDigits D).a.value ρ W ∧
      W.slot (H.tV.sEnd + 4 * i + 1) = (Desc.First.P6.Row.ofDigits D).b.value ρ W ∧
      W.slot (H.tV.sEnd + 4 * i + 2) = (Desc.First.P6.Row.ofDigits D).Rlo.value ρ W ∧
      W.slot (H.tV.sEnd + 4 * i + 3) = (Desc.First.P6.Row.ofDigits D).Rhi.value ρ W := by
  obtain ⟨Dr, _, hDr, _, mE, _, _⟩ := Desc.First.K4.rowsForms_mem h hi
  rw [hD] at hDr
  cases hDr
  have key : ∀ f ∈ [Aff.slot (H.tV.sEnd + 4 * i + 0) - (Desc.First.P6.Row.ofDigits D).a,
      Aff.slot (H.tV.sEnd + 4 * i + 1) - (Desc.First.P6.Row.ofDigits D).b,
      Aff.slot (H.tV.sEnd + 4 * i + 2) - (Desc.First.P6.Row.ofDigits D).Rlo,
      Aff.slot (H.tV.sEnd + 4 * i + 3) - (Desc.First.P6.Row.ofDigits D).Rhi],
      f.value ρ W = 0 := fun f hf => hz f (mE f hf)
  have k0 := key _ (List.mem_cons_self ..)
  have k1 := key _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have k2 := key _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have k3 := key _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..))))
  rw [Aff.value_sub, Aff.value_slot] at k0 k1 k2 k3
  exact ⟨sub_eq_zero.mp k0, sub_eq_zero.mp k1, sub_eq_zero.mp k2, sub_eq_zero.mp k3⟩

/-- A digit of a norm's row, on true short tables. -/
theorem digitsAt_value (hρ : Numerals ρ) {v : Env} {c : Cells K} {t : Cell → K} {u : ℕ → K}
    {lT : ℕ} {P : String} {b : ℕ} {trow : Ten} (hb : v.tabAt ("ar@" ++ P) = some b)
    (hrow : v.y.T_ "row" = some trow) (hJ : trow.J = 99) (T : Tied c t .D trow.mat trow.place)
    (R : ShortTrue ρ W v b trow.mat lT c u) {ν : ℕ} {D : ℕ → Aff}
    (hD : Desc.First.K4.digitsAt v P ν = some D) :
    ∀ n, n < 99 → (D n).value ρ W = ext lT (fun i => led t ν i n) u := by
  intro n hn
  unfold Desc.First.K4.digitsAt at hD
  obtain ⟨cells, hc, e⟩ := Option.map_eq_some_iff.mp hD
  rw [← e, Aff.value_add, Aff.value_ofConst, hρ.ofNat, ← rowCells_value hb hrow hJ T R hc n hn]
  norm_num

#print axioms rowBatch_says
#print axioms shown_says
#print axioms digitsAt_value

end OnBytes.Road.K4
