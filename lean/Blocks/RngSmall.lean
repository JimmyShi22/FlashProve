-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/RngSmall.lean: conditions under which the round-by-round errors of the lookup argument and of
the closing block are small.

`Small` D' ε (Blocks/Small.lean) says that every count of the list ε, times D', is at most the
number of values of the verifier message; then, for D' > 0, the largest error is at most 1/D'. Here
`Small` is proved from inequalities between natural numbers:

 * `SC.small_scErr`, `PL.small_plErr`, `Closing.small_closeErr`: the masked sumcheck, the product
   layer, the closing block (for 0 < nL and 2 D' ≤ |E|, which serves ς).
 * `Lk.small_stLookup`: the errors of the lookup argument are small if (2^D - 1) D' ≤ |E| (α), gT D'
   ≤ |E| (the points; gT is the largest number of coordinates), 2 D' ≤ |E| (the rounds of the
   sumchecks), 0 < Pm and 2 ≠ 0 in E; D' is the bound, D the number of coordinates of a tree of
   keys.

The counts, in the order of the messages: 2^D - 1 (α); g |E|^(g-1) for a point of g coordinates; 2
for each round and 1 for each ζ in the layers of both sides; 2 and 0 in the leaf layer and the bit
layer; |E|^(2 Pm - 1) for the 2 Pm coefficients of the root test, 2 for each of its rounds; 2 at ς
and |E|^(n-1) at the n coefficients of the closing block.

A point of g coordinates has the error g / |E|; the coefficients of the root test are a separate
message. α costs (2^D − 1)/|E|.

Notation: α: the challenge of the lookup argument (Blocks/LookupRel.lean; block `Lk.bAl`); the leaf
layer, the bit layer and the root test are those of the list of blocks in the head of
Blocks/LookupBlock.lean (`Lk.bL`; `bB`; `bUV`, `bXi`, `bRs`, `bRec`); ζ: a challenge of the verifier
in a product layer (the head of Blocks/ProductBlock.lean: "and the verifier a challenge ζ"); ς: the
product challenge of the closing block (the head of Blocks/ClosingBlock.lean); `Pm`, `gT`, natural
numbers: the number of the highest plane, `2 ^ lp - 1` (`lp`: 2^lp bits for a multiplicity); the
number of variables of the leaves of the table side (`LkPar`, Blocks/LookupRel.lean).

Terms: lean/GLOSSARY.md.
-/
import Blocks.Small
import Blocks.ClosingStage
import Blocks.LookupStage
import Blocks.RngForest
import Blocks.RngForms

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks

open Iop Prob

/-- A point of n coordinates. -/
theorem small_ePt (E : Type) [Field E] [Fintype E] (D n : ℕ) (h : n * D ≤ Fintype.card E) :
    Lk.ePt E n * D ≤ Fintype.card (Fin n → E) := by
  unfold Lk.ePt
  rw [Fintype.card_fun, Fintype.card_fin]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact small_aux _ _ _ _ hn h

/-- n coefficients, of which a fraction 1/|E| is bad. -/
theorem small_coef (E : Type) [Fintype E] (K : Type) [Fintype K] [DecidableEq K] (D : ℕ)
    (hK : 0 < Fintype.card K) (h : D ≤ Fintype.card E) :
    Fintype.card E ^ (Fintype.card K - 1) * D ≤ Fintype.card (K → E) := by
  rw [Fintype.card_fun]
  have := small_aux 1 (Fintype.card E) D (Fintype.card K) hK (by omega)
  rwa [Nat.one_mul] at this

theorem SC.small_scErr {E Y P Ξ ι : Type} [Field E] [Fintype E] [DecidableEq E] [DecidableEq ι]
    (S : SC E Y P Ξ ι) (D : ℕ) (h : ∀ i, (S.e i + 1) * D ≤ Fintype.card E) :
    ∀ l : List ι, Small D (S.scErr l)
  | [] => trivial
  | i :: l =>
    small_app D (s := (S.round i).shape) (S.e i + 1, ()) (S.scErr l)
      ⟨h i, trivial⟩ (SC.small_scErr S D h l)

theorem PL.small_plErr {E Y P N Ξ : Type} [Field E] [Fintype E] [DecidableEq E]
    [Fintype N] [DecidableEq N] (L : PL E Y P N Ξ) (D e : ℕ)
    (h2 : 2 * D ≤ Fintype.card E) (he : e * D ≤ Fintype.card E) : Small D (L.plErr e) :=
  small_app D (s := L.init.shape) () _ trivial
    (small_app D (s := (L.sc.sc L.ord).shape) (t := L.fin.shape) _ (e, ())
      (SC.small_scErr L.sc D (fun _ => h2) _) ⟨he, trivial⟩)

theorem Closing.small_closeErr (E : Type) [Field E] [Fintype E] [DecidableEq E] (nL nR nO D : ℕ)
    (hL : 0 < nL) (h2 : 2 * D ≤ Fintype.card E) :
    Small D (Closing.closeErr E (Fin nL) (Fin nR) nO) :=
  small_app D (s := [Closing.rAux E (Fin nR)])
    (t := [Closing.rOpen E (Fin nL) (Fin nR) nO]) (2, ()) _ ⟨h2, trivial⟩
    ⟨small_coef E (Fin nL ⊕ Fin nO ⊕ Fin nR) D
        (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) (by omega),
      trivial⟩

namespace Lk

variable {E Y Pd N : Type} [Field E] [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N]
  [DecidableEq N] [Fintype Pd] [DecidableEq Pd] (L : Lk E Y Pd N) (D : ℕ)

theorem small_stKey (h2 : 2 * D ≤ Fintype.card E) : ∀ n l : ℕ, Small D (L.stKey n l).ε
  | 0, _ => trivial
  | n + 1, l =>
    small_app D (s := (L.stK l).B.shape) _ _
      ((L.plK l).small_plErr D 1 h2 (by omega)) (small_stKey h2 n (l + 1))

theorem small_stTab (h2 : 2 * D ≤ Fintype.card E) : ∀ n l : ℕ, Small D (L.stTab n l).ε
  | 0, _ => trivial
  | n + 1, l =>
    small_app D (s := (L.stT l).B.shape) _ _
      ((L.plT l).small_plErr D 1 h2 (by omega)) (small_stTab h2 n (l + 1))

/-- The errors of the lookup argument are small, under the hypotheses below and 2 ≠ 0 in E. -/
theorem small_stLookup (hα : (2 ^ L.par.D - 1) * D ≤ Fintype.card E)
    (hg : L.par.gT * D ≤ Fintype.card E) (h2 : 2 * D ≤ Fintype.card E) (hPm : 0 < L.par.Pm) :
    Small D L.stLookup.ε := by
  have hσl : (L.par.σ + L.par.lp) * D ≤ Fintype.card E :=
    le_trans (Nat.mul_le_mul_right _ (by unfold LkPar.gT; omega)) hg
  have hσ : L.par.σ * D ≤ Fintype.card E := le_trans (Nat.mul_le_mul_right _ (by omega)) hσl
  have hAl : Small D L.stAl.ε := ⟨hα, trivial⟩
  have hZY : Small D L.stZY.ε := ⟨small_ePt E D _ hσ, trivial⟩
  have hKe : Small D L.stKe.ε := trivial
  have hT0 : Small D L.stT0.ε := ⟨small_ePt E D _ hσl, trivial⟩
  have hL : Small D L.stL.ε := L.plL.small_plErr D 0 h2 (by omega)
  have hB0 : Small D L.stB0.ε := ⟨small_ePt E D _ hg, trivial⟩
  have hB : Small D L.stB.ε := L.plB.small_plErr D 0 h2 (by omega)
  have h14 : Small D L.st14.ε :=
    small_app D L.stAl.ε _ hAl <|
    small_app D L.stZY.ε _ hZY <|
    small_app D (L.stKey L.par.D 0).ε _ (L.small_stKey D h2 _ _) <|
    small_app D L.stKe.ε _ hKe <|
    small_app D L.stT0.ε _ hT0 <|
    small_app D (L.stTab L.par.r 0).ε _ (L.small_stTab D h2 _ _) <|
    small_app D L.stL.ε _ hL <| small_app D L.stB0.ε L.stB.ε hB0 hB
  have h5 : Small D L.st5.ε := ⟨small_ePt E D _ hσ, trivial⟩
  have hUV : Small D L.stUV.ε := ⟨small_ePt E D _ hσ, trivial⟩
  have hXi : Small D L.stXi.ε :=
    ⟨by
      have h := small_coef E (Fin (2 * L.par.Pm)) D (by rw [Fintype.card_fin]; omega) (by omega)
      rw [Fintype.card_fin] at h
      show L.par.eXi (Fintype.card E) * D ≤ _
      rw [show L.par.eXi (Fintype.card E) = Fintype.card E ^ (2 * L.par.Pm - 1)
          from if_neg (by omega)]
      exact h, trivial⟩
  have hRs : Small D L.stRs.ε := SC.small_scErr L.scR D (fun _ => h2) _
  have hRec : Small D L.stRec.ε := trivial
  have h6 : Small D L.st6.ε :=
    small_app D L.stUV.ε _ hUV <|
    small_app D L.stXi.ε _ hXi <|
    small_app D L.stRs.ε L.stRec.ε hRs hRec
  exact small_app D L.st14.ε _ h14 (small_app D L.st5.ε L.st6.ε h5 h6)

end Lk

end Blocks
