-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/OrderedNum.lean: THE PREMISE `OrderedV` OF K10's LAW FROM A NUMBERING
OF THE TYPED ROWS. A statement and its proof.

`orderedV_of` (OrderedOf.lean, beside this file) asks a list of all the typed rows' names, each
once, and the powers of the drawn element along it. Both come from ONE thing with a name: a
numbering.
  `orderedV_of_num`: let num number the typed rows' names one to one onto the numbers below n, let
    the batching's coefficients be the powers of one element at these numbers (the library's
    `Cb.Pv.Bat.powersZ n num`), let the seed be the reading of the element drawn, and let the
    program's list have n rows. Then `OrderedV`, at the choice of OrderedOf.lean, follows from
    `Pulls` and, name by name: a row b of the claim has the reading of the target of the program's
    row number num b as its target and `rowVec` of that row as its state; a member's sample row has
    the tie of OrderedOf.lean at its number.
Limits. Those of OrderedOf.lean. The numbering is a letter: that the text's order `runRows` (open
rows as created, each member's sample rows, the rows from reads) is such a numbering of a place's
typed rows is owed by whoever fills the place. Nothing on soundness, on an honest prover or on
hiding.

-/
import Johnson.Desc.First.Close.Law.OrderedOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice Iop IOR KObj Cb Cb.Pv Johnson.Top.H
open Johnson.Top.H.ArrAdd (FreeAt)

variable {S : Sig GE} (R : RowsK S) {B : Type} (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE)

theorem orderedV_of_num (n : ℕ) (num : R.G.Row B ≃ Fin n) (N : SlotNames R) (hP : Pulls R pull)
    (frS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), Slf GE (S.om as.1.1).Z.D R.Sh.Cin.J)
    (hfrS : ∀ as s j, ¬ FreeAt R.Sh j → frS as s j = 0)
    (x : (B → GE) × (B → R.Sh.Cin.J → GE)) (σ : S.Smp) (e : E) (T : Statement)
    (L : GroupLayout) (rows : List OnBytes.Row) (hn : rows.length = n)
    (hB : ∀ b, x.1 b = readE (rows[(num (.inl b)).val]'(hn ▸ (num (.inl b)).isLt)).target ∧
      x.2 b = rowVec N T L (rows[(num (.inl b)).val]'(hn ▸ (num (.inl b)).isLt)))
    (hS : ∀ as, (σ as.1.1).2 as.2 =
        readE (rows[(num (.inr as)).val]'(hn ▸ (num (.inr as)).isLt)).target ∧
      R.Sh.rho.fm (Slf.atMem (Jf := fun a : R.G.A => (S.om a.1).C.J) as.1
          ((S.om as.1.1).row as.2) (σ as.1.1).1) + frS as (σ as.1.1).1 =
        rowVec N T L (rows[(num (.inr as)).val]'(hn ▸ (num (.inr as)).isLt))) :
    OrderedV R (fun _ : B => R.Sh.Cin.J → GE) (fun _ V => pull V)
      (Cb.Pv.Bat.powersZ (E := GE) n num) N (frOf R pull frS) x σ (readE e) e T L rows := by
  have hlen : ((List.finRange n).map num.symm).length = rows.length := by simp [hn]
  have hget : ∀ i (h : i < ((List.finRange n).map num.symm).length),
      num (((List.finRange n).map num.symm)[i]) = ⟨i, by simpa using h⟩ := fun i h => by
    simp
  refine orderedV_of R pull (Cb.Pv.Bat.powersZ (E := GE) n num) N hP frS hfrS x σ (readE e) e T L
    rows
    ((List.finRange n).map num.symm) ((List.nodup_finRange n).map num.symm.injective)
    (fun ν => List.mem_map.2 ⟨num ν, List.mem_finRange _, num.symm_apply_apply ν⟩) hlen
    (fun i h => ?_) (fun i h b hb => ?_) (fun i h as has => ?_)
  · show readE e ^ (num (((List.finRange n).map num.symm)[i])).val = readE e ^ i
    rw [hget i h]
  · have e1 : (num (.inl b)).val = i := by rw [← hb, hget i h]
    have := hB b
    simp only [e1] at this
    exact this
  · have e1 : (num (.inr as)).val = i := by rw [← has, hget i h]
    have := hS as
    simp only [e1] at this
    exact this

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.orderedV_of_num
