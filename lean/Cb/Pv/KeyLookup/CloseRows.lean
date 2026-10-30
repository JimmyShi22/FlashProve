-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/CloseRows.lean: what the rows of the closing and of the test of the bits read, and
how many corners have a cell.

It imports the library and Bits.lean; no file of the port.

The rows, in the order in which the blocks append them: `A.rowE P zz` (closing, Close.lean), then
`A.rowU P o` and `A.rowV P o` (test of the bits, Bits.lean). The row on the counts is `numRow` of
Letters.lean.
  `ClPl.In P G`   G holds of the live cells (bAt u j, u < 2^d, j < pl), of the places of wE and wB
                  and of cB. It stands for the library's `PlacesIn` (Cb/Ld/LdLkpAsm2Pull.lean),
                  whose clause bAt runs over all u and j.
  `rowE_supp`     under `P.In G`, if the incoming form is 0 outside G: so is the closing's row.
  `rowU_supp`, `rowV_supp`   under `P.In G`: both rows of the test of the bits are 0 outside G.
  `cells_card`    if pl ≤ 2^mu: of the 2^(mu + d) corners exactly pl · 2^d have a cell.
  `cell_apart`    if the places bAt u j (u < 2^d, j < pl) are apart: a corner that has a cell shares
                  it with no other corner.
Not shown: that the places of bAt are apart (that depends on the value of bAt).

-/
import Cb.Pv.KeyLookup.Bits
import Cb.Ld.LdLkpSuppProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Finset

/-- The first row of a sumcheck has the coefficient 0 at an entry that is no place of its hiding
    polynomial and that neither the incoming form nor
a kept map reads. -/
theorem slU_zero {E : Type} [Field E] (Y : PscPar E)
    (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E) (o : Y.Out) (j : Y.J)
    (h1 : ∀ i, Y.wAt i ≠ j) (h2 : Y.slS o.st j = 0)
    (h3 : ∀ b, rowB o.st b (Y.hp o.st o.pt) j = 0) : Y.slU rowB o j = 0 := by
  unfold PscPar.slU
  rw [Finset.sum_eq_zero fun i _ => if_neg (h1 _), h2,
    Finset.sum_eq_zero fun b _ => by rw [h3 b, mul_zero]]
  simp

variable {E : Type} [Field E] [Fintype E] {A : Dat E}

/-- What stands for `PlacesIn` here. -/
structure ClPl.In (P : ClPl A) (G : A.J → Prop) : Prop where
  cells : A.CellsIn G
  wE : ∀ i, G (P.wE i)
  wB : ∀ i, G (P.wB i)
  cB : G P.cB

namespace Dat
variable (A) (P : ClPl A) {G : A.J → Prop}

theorem rowE_supp (h : P.In G) (zz : (A.En P).par.Mid)
    (hI : SuppIn G (show A.XS from zz.st).top.mf) : SuppIn G (A.rowE P zz).cf := by
  intro j hj
  refine slU_zero (A.En P).par (A.En P).rowB ((A.En P).outOf zz) (some j)
    (fun i e => hj (Option.some.inj e ▸ h.wE i)) (hI j hj) fun b => ?_
  unfold LkEndM.rowB
  exact Finset.sum_eq_zero fun c _ => if_neg fun e => hj (A.cell_in h.cells _ j e)

theorem rowU_supp (h : P.In G) (o : (A.BT P).par.Out) : SuppIn G (A.rowU P o).cf := by
  intro j hj
  exact slU_zero (A.BT P).par (fun _ b => b.elim) o (some j)
    (fun i e => hj (Option.some.inj e ▸ h.wB i)) rfl fun b => b.elim

theorem rowV_supp (h : P.In G) (o : (A.BT P).par.Out) : SuppIn G (A.rowV P o).cf := by
  intro j hj
  show (A.Bt P).rowA o.st () ((A.BT P).par.hp o.st o.pt) (some j) = 0
  unfold LkBit.rowA
  have e1 : ∀ b, (A.Bt P).tAt b ≠ some j := fun b e => hj (A.cell_in h.cells b j e)
  have e2 : some j ≠ (A.Bt P).cAt := fun e => hj (Option.some.inj e ▸ h.cB)
  rw [Finset.sum_eq_zero fun b _ => if_neg (e1 b), zero_add]
  exact if_neg e2

/-- If the places of the live bits are apart, two corners with the same cell, not `none`, are
equal. -/
theorem cell_apart
    (hb : ∀ u u' j j', u < 2 ^ A.d → u' < 2 ^ A.d → j < A.pl → j' < A.pl →
      A.bAt u j = A.bAt u' j' → u = u' ∧ j = j')
    (c c' : Fin (A.mu + A.d) → Bool) (hn : A.cell c ≠ none) (h : A.cell c = A.cell c') :
    c = c' := by
  have h1 : numLE c % 2 ^ A.mu < A.pl :=
    Nat.lt_of_not_le fun e => hn ((A.cell_none_iff c).2 e)
  have h2 : numLE c' % 2 ^ A.mu < A.pl :=
    Nat.lt_of_not_le fun e => hn (h.trans ((A.cell_none_iff c').2 e))
  rw [A.cell_live c h1, A.cell_live c' h2] at h
  obtain ⟨e1, e2⟩ := hb _ _ _ _ (A.row_lt c) (A.row_lt c') h1 h2 (Option.some.inj h)
  apply ldLkpNum_inj
  rw [← Nat.div_add_mod (numLE c) (2 ^ A.mu), ← Nat.div_add_mod (numLE c') (2 ^ A.mu), e1, e2]

/-- How many corners have a cell. -/
theorem cells_card (hr : A.pl ≤ 2 ^ A.mu) :
    (univ.filter fun c : Fin (A.mu + A.d) → Bool => (A.cell c).isSome = true).card =
      A.pl * 2 ^ A.d := by
  have h1 : ∀ c : Fin (A.mu + A.d) → Bool,
      (A.cell c).isSome = true ↔ numLE c % 2 ^ A.mu < A.pl := by
    intro c
    constructor
    · intro h
      by_contra hc
      rw [(A.cell_none_iff c).2 (Nat.le_of_not_lt hc)] at h
      exact absurd h (by simp)
    · intro h
      rw [A.cell_live c h]
      rfl
  rw [Finset.filter_congr fun c _ => h1 c, Finset.card_filter,
    ldLkpNum_sum ℕ (A.mu + A.d) fun n => if n % 2 ^ A.mu < A.pl then 1 else 0,
    Nat.add_comm A.mu A.d, pow_add, Alg.sum_range_mul_add]
  have h2 : ∀ a ∈ range (2 ^ A.d),
      ∑ b ∈ range (2 ^ A.mu), (if (a * 2 ^ A.mu + b) % 2 ^ A.mu < A.pl then 1 else 0) = A.pl := by
    intro a _
    have e1 : ∑ b ∈ range (2 ^ A.mu), (if (a * 2 ^ A.mu + b) % 2 ^ A.mu < A.pl then 1 else 0) =
        ∑ b ∈ range (2 ^ A.mu), if b < A.pl then 1 else 0 :=
      Finset.sum_congr rfl fun b hb => by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Finset.mem_range.1 hb)]
    have e2 : (range (2 ^ A.mu)).filter (fun b => b < A.pl) = range A.pl := by
      ext b
      simp only [mem_filter, mem_range]
      exact ⟨fun h => h.2, fun h => ⟨Nat.lt_of_lt_of_le h hr, h⟩⟩
    rw [e1, ← Finset.card_filter, e2, card_range]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, card_range, smul_eq_mul, Nat.mul_comm]

end Dat
end Lk6

#print axioms Lk6.Dat.rowE_supp
#print axioms Lk6.Dat.rowU_supp
#print axioms Lk6.Dat.rowV_supp
#print axioms Lk6.Dat.cells_card
#print axioms Lk6.Dat.cell_apart
