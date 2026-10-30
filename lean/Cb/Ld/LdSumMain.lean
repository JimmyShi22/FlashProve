-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumMain.lean: under the hypotheses below, the zero-knowledge sumcheck that folds is a block
of a chain: the record `IOR.GoodT` for the term `Y.ior`, with its honest side `Y.hon`, of
Cb/Ld/LdSum.lean.

The top statement of the block and its proof (an assembly).
The file follows the paper that this protocol builds on (lean/CREDITS.md).

The statement (`Spec.ld_sum_good`). Y: the parameters (Cb/Ld/LdSum.lean): k = h + g variables,
degree n, any finite non-empty challenge set, codes C (main table) and Z (masks, read under two
transformations), two linear forms with states, a packing of the hiding coefficients.
From the main relation on [C with 2^k rows, Z with 2^h rows] to the main relation on [C, Z, Z under
the fresh mask's transformation], each with its existential relaxation at the same radius e (a count
of long positions):
  strings (`point`); locality (`isLocal`); perfect completeness; round-by-round knowledge soundness
  with the named backward extractor `Y.ext d` and the errors `Y.err` (counts of challenges):
      round of the coefficient: Lst 0 (the list of the complex with the fresh mask in it)
      round j = 1 .. k: mC j + [j ≤ h] · (mS j + mW j) + Lst (j - 1) · n (agreement of the tables
      after the round; the list of the complex before it, times the degree),
      where [j ≤ h] is 1 if j ≤ h and 0 else
  honest-verifier zero knowledge, exact, for further reads of the fresh mask behind at most t long
  positions; nothing is withheld (both probabilities 0). (`Y.bud t`; `pBad`, `pHid` of `Y.nums`)
Hypotheses, all in the statement's own text: the three codes have their laws and a distance d > e as
they are read (`CodesOK`); Lst, mC, mS, mW bound the lists and the exceptional values of the k + 1
stages at e (`Y.ErrOK`); challenges are distinct elements of E; 2 ≤ n; the packing's law
(`Y.PackOK`) and the degrees of its weights (`Y.QwDeg`): both are stated in Cb/Ld/LdSumPack.lean for
the packing into 2^h rows (`pkC`, `QwC`) and its padded forms, and for the plain packing (`pk0`,
`Qw0`) the law alone is stated; the encoding of the fresh mask table hides t long positions (from
one row: Cb/Ld/LdSumZkRows.lean).
e may lie beyond half the distance: nothing is decoded from errors, and uniqueness of a codeword
within e is not used.
`Spec.ld_sum_good_row`: the same with zero knowledge asked of one row of the mask code. Counts
(rounds, reads, sources of a new symbol): `Spec.ld_sum_counts` in Cb/Ld/LdSumGood.lean.

Limits: `Y.ErrOK` is a hypothesis of the statement; this file proves no bound on a list or on
agreement, for any code. Running times are not modelled.
Declared differences to the paper that this protocol builds on: headers of Cb/Ld/LdSum.lean (six)
and of Cb/Ld/LdSumKnow.lean (two).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSumGood
import Cb.Ld.LdSumKnowProofs
import Cb.Ld.LdSumZkRows

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

namespace Spec

/-- The zero-knowledge sumcheck that folds. -/
def ld_sum_good : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] (Y : SumPar E P)
      (d e t : ℕ) (Lst mC mS mW : ℕ → ℕ),
    CodesOK E P Y.C Y.Z Y.Zw d e → Y.ErrOK e Lst mC mS mW → Function.Injective Y.val → 2 ≤ Y.n →
    Y.PackOK → Y.QwDeg → Y.Cw.Zk t →
    IOR.GoodT Y.ior Y.hon (Y.Cin.rels Y.slIn e fun _ => ()) (Y.Cout.rels Y.slOut e fun _ => ())
      (Y.ext d) (Y.nums t Lst mC mS mW)

/-- The same, zero knowledge being asked of one row of the mask code under the fresh mask's
transformation. -/
def ld_sum_good_row : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] (Y : SumPar E P)
      (d e t : ℕ) (Lst mC mS mW : ℕ → ℕ),
    CodesOK E P Y.C Y.Z Y.Zw d e → Y.ErrOK e Lst mC mS mW → Function.Injective Y.val → 2 ≤ Y.n →
    Y.PackOK → Y.QwDeg → Y.Zw.Zk t →
    IOR.GoodT Y.ior Y.hon (Y.Cin.rels Y.slIn e fun _ => ()) (Y.Cout.rels Y.slOut e fun _ => ())
      (Y.ext d) (Y.nums t Lst mC mS mW)

end Spec

theorem ld_sum_good : Spec.ld_sum_good := by
  intro E P _ _ _ Y d e t Lst mC mS mW hC hE hv hn hP hQ hZk
  exact ld_sum_good_of_know E P Y e t Lst mC mS mW (Y.ext d) hn hP hC.1.1 hC.1.2.1 hC.1.2.2 hZk
    (ld_sum_know E P Y d e Lst mC mS mW hC hE hv hn hQ)

theorem ld_sum_good_row : Spec.ld_sum_good_row := by
  intro E P _ _ _ Y d e t Lst mC mS mW hC hE hv hn hP hQ hZk
  exact ld_sum_good E P Y d e t Lst mC mS mW hC hE hv hn hP hQ
    (ld_zk_il E P Y.Zw (Fin Y.h → Bool) t hZk)

end Cb
