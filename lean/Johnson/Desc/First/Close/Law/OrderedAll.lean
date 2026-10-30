-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/OrderedAll.lean: THE PREMISE `OrderedV` OF K10's LAW, FROM A NUMBERING,
THE CHOICE OF THE CLAIM's TYPED ROWS, AND WHAT IS LEFT OF THE SAMPLE ROWS' TIE. A definition, a
statement and its proof.

It joins `orderedV_of_num` (OrderedNum.lean) and `sample_tie` (SampleTie.lean), beside this file.
  `frSOf pS`: a sample row's further weights: on the free rows, what the program's sample row has
    there beyond the library's sample row, arranged; 0 elsewhere. pS as s: the program's sample row
    as a vector on the whole cube, as a function of the seed s: a letter.
  `orderedV_all`: `OrderedV`, at the choice of OrderedOf.lean and at `frSOf pS`, at the powers of
    the element drawn along a numbering num, from `Pulls` and, name by name: a row b of the claim
    has the reading of the target of the program's row number num b as its target and `rowVec` of
    that row as its state; of a member's sample row: the answer is the reading of the program's
    row's target; pS at the seed is `rowVec` of that row; that row names one oracle message alone
    (`NamesOne`); and `SampleFits`: the member's change of shape carries the library's sample row at
    the seed to the row's coefficients under the layout's weights, and the row weighs nothing on
    other members' rows.
Limits. Those of the files named. `Pulls`, the numbering, pS and `SampleFits` are premises: shown of
no data here. For the claim's rows there is one text, not two held against each other: the typed row
is the program's by make. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.OrderedNum
import Johnson.Desc.First.Close.Law.SampleTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice Iop IOR KObj Cb Cb.Pv Johnson.Top.H
open Johnson.Top.H.ArrAdd (FreeAt)

variable {S : Sig GE} (R : RowsK S) {B : Type} (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE)

open Classical in
/-- A sample row's further weights. -/
noncomputable def frSOf
    (pS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE) :
    ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), Slf GE (S.om as.1.1).Z.D R.Sh.Cin.J :=
  fun as s j => if FreeAt R.Sh j then
    pS as s j - R.Sh.rho.fm (Slf.atMem (Jf := fun a : R.G.A => (S.om a.1).C.J) as.1
      ((S.om as.1.1).row as.2) s) j else 0

open Classical in
theorem orderedV_all (n : ℕ) (num : R.G.Row B ≃ Fin n) (N : SlotNames R) (hP : Pulls R pull)
    (pS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE)
    (x : (B → GE) × (B → R.Sh.Cin.J → GE)) (σ : S.Smp) (e : E) (T : Statement)
    (L : GroupLayout) (rows : List OnBytes.Row) (hn : rows.length = n)
    (hB : ∀ b, x.1 b = readE (rows[(num (.inl b)).val]'(hn ▸ (num (.inl b)).isLt)).target ∧
      x.2 b = rowVec N T L (rows[(num (.inl b)).val]'(hn ▸ (num (.inl b)).isLt)))
    (hS : ∀ as, (σ as.1.1).2 as.2 =
        readE (rows[(num (.inr as)).val]'(hn ▸ (num (.inr as)).isLt)).target ∧
      pS as (σ as.1.1).1 = rowVec N T L (rows[(num (.inr as)).val]'(hn ▸ (num (.inr as)).isLt)) ∧
      ∃ o, NamesOne (rows[(num (.inr as)).val]'(hn ▸ (num (.inr as)).isLt)) o ∧
        SampleFits N T L (rows[(num (.inr as)).val]'(hn ▸ (num (.inr as)).isLt)) o as.1
          (Slf.atMem (Jf := fun a : R.G.A => (S.om a.1).C.J) as.1
            ((S.om as.1.1).row as.2) (σ as.1.1).1)) :
    OrderedV R (fun _ : B => R.Sh.Cin.J → GE) (fun _ V => pull V)
      (Cb.Pv.Bat.powersZ (E := GE) n num) N (frOf R pull (frSOf R pS)) x σ (readE e) e T L
      rows := by
  refine orderedV_of_num R pull n num N hP (frSOf R pS) (fun as s j hj => ?_) x σ e T L rows hn hB
    fun as => ⟨(hS as).1, ?_⟩
  · show (if FreeAt R.Sh j then _ else 0) = (0 : GE)
    rw [if_neg hj]
  · obtain ⟨-, h2, o, h3, h4⟩ := hS as
    funext j
    show R.Sh.rho.fm _ j + (if FreeAt R.Sh j then _ else 0) = _
    by_cases hj : FreeAt R.Sh j
    · rw [if_pos hj, h2]
      ring
    · rw [if_neg hj, add_zero]
      exact sample_tie N T L _ o as.1 _ h3 h4 j hj

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.orderedV_all
