-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRelToy7d4.lean: a third small code not below half the distance, whose encoding hides three
positions, that meets the nine clauses of `Spec.ld_toy74` together, nothing assumed beyond the
hypotheses of the statements and whatever the arguments hold as proofs.

Statement and proofs. A guard against empty theorems; no parameter of a protocol.
The first toy is Cb/Ld/LdRelToy.lean, which also defines the field (`LdToy.K`); the second is
Cb/Ld/LdRelToy7.lean.

The code is Reed-Solomon over the field with 101 elements, at the points 1, .., 7, of dimension 4
(one message symbol, three symbols of randomness; they fill the dimension) and distance 4, with any
finite set R of interleaved rows. As a code read under a transformation (`LdCode`,
Cb/Ld/LdRel.lean), it is `LdToy74.toyLd74 R`.
An `LdCode` has an encoder to native words and a transformation from native words to long words;
`toyLd74 R` is read as it stands: each long position reads the one native position with the same
number.
The laws (`LdCode.Laws`, Cb/Ld/LdRel.lean): encoder and transformation are linear, the encoder is
injective, the transformation reads what it declares. The other notions of the statement are
`LdCode.Dist`, `LdCode.ListAt`, `LdCode.MCAat`, `LdCode.Zk`, `LdCode.Transparent`, `LdCode.LocalLE`
of Cb/Ld/LdRel.lean.
The radius is 2: 2 · 2 is not below the distance 4 (decoding is not unique in general); 2 is below
the distance and below the Johnson radius (`InJohnson n d e`, Cb/Gen/JohnsonList.lean, is
`n * (n - d) < (n - e) ^ 2`: at 7, 4, 2: 7 · 3 < 5 · 5).

Main names:
  `Spec.ld_toy74`, for every R: the laws; distance at least 4; at most 3 codewords within 2
    positions of any word (the Johnson bound, Cb/Ld/LdRelJohnson.lean: `listMax n d e`,
    Cb/Gen/JohnsonList.lean, is `n * (d - e) / ((n - e) ^ 2 - n * (n - d))`: at 7, 4, 2: 7 · 2 / 4,
    rounded down, where 4 = 5 · 5 - 7 · 3); at most 29 exceptional θ on any line
    (Cb/Ld/LdRelAny.lean: the sets that omit at most 2 of 7 positions: 1 + 7 + 21; its head says
    when a θ of the line T f₀ + θ T f₁ is exceptional), and 29 < 101; the encoding is zero knowledge
    at 3 positions; the transformation is transparent and reads at most 1 native position for a long
    one.
  `LdToy74.list74`, `LdToy74.mca74`: list and agreement for every code over this field read at these
    seven positions, under the hypotheses of their statements: for complexes, interleavings, doubled
    codes.

Why a third toy: in a batch of N instances an oracle message that the shared part of the prover
sends may lie in one shared test and in a test of each slot (1 + N tests, each of which reads one
long position at least). With two slots its encoding has to hide three positions; the code of
Cb/Ld/LdRelToy7.lean hides two.

Limits: this file says nothing on real parameters. That some word has two codewords within the
radius is not shown here (it is shown for the second toy); nor that the bound 3 is attained.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRelToy
import Cb.Ld.LdRelJohnsonProofs

set_option autoImplicit false

namespace Cb
namespace LdToy74
open Iop Prob Hiop Blocks LdToy

/-- Reed-Solomon: points 1, .., 7; dimension 4; one message symbol, three symbols of randomness. The
record's fields radius 1, count 2 are those for which the record's own law (`Code.Enc.Props`) is
shown, in `props74`; every statement below names its own radius and counts. -/
def C74 : Code.Enc K := Code.RS.code (Code.RS.natPoints K 7) 4 1 3 1 2

/-- the long positions -/
abbrev P74 : Type := (Reading.one C74).P

/-- The toy: rows R under `C74`, read as they stand. -/
@[reducible] def toyLd74 (R : Type) [Fintype R] [DecidableEq R] : LdCode K P74 :=
  (Reading.one C74).ld K fun _ => R

end LdToy74

namespace Spec
open LdToy LdToy74

def ld_toy74 : Prop :=
  ∀ (R : Type) [Fintype R] [DecidableEq R], (toyLd74 R).Laws ∧ (toyLd74 R).Dist 4 ∧ ¬ 2 * 2 < 4 ∧
    (toyLd74 R).ListAt 2 3 ∧ (toyLd74 R).MCAat 2 29 ∧ 29 < Fintype.card K ∧ (toyLd74 R).Zk 3 ∧
    (toyLd74 R).Transparent ∧ (toyLd74 R).LocalLE 1

end Spec

namespace LdToy74
open Iop Prob Hiop Blocks LdToy

theorem props74 : C74.Props K :=
  Code.RS.props_natPoints (F := K) (E := K) 101 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem core74 : C74.Core := ⟨props74.place, props74.dist, by decide, props74.hides⟩

theorem card74 : Fintype.card P74 = 7 := Fintype.card_fin 7

set_option maxRecDepth 100000 in
theorem cnt_sets74 : cnt (fun S : Finset (Fin 7) => Fintype.card (Fin 7) ≤ S.card + 2) = 29 := by
  rw [cnt_eq_card_filter]
  decide

/-- Every code at the seven positions with the laws and the distance 4 has at most 3 codewords
within 2 positions of any word. -/
theorem list74 (D : LdCode K P74) (hL : D.Laws) (hD : D.Dist 4) : D.ListAt 2 3 := by
  have hJ : InJohnson (Fintype.card P74) 4 2 := by
    rw [card74]
    unfold InJohnson
    norm_num
  have hl : listMax (Fintype.card P74) 4 2 = 3 := by
    rw [card74]
    unfold listMax
    norm_num
  have h := ld_list_johnson K P74 D 4 2 hL hD hJ
  rwa [hl] at h

/-- Every code at the seven positions with the laws has at most 29 exceptional values on any line,
at the radius 2. -/
theorem mca74 (D : LdCode K P74) (hL : D.Laws) : D.MCAat 2 29 :=
  ld_mca_mono K _ _ 2 _ 29 (le_of_eq cnt_sets74) (ld_mca_sets K P74 D hL 2)

end LdToy74

open Iop Prob Hiop Blocks LdToy LdToy74 in
theorem ld_toy74 : Spec.ld_toy74 := by
  intro R _ _
  have hd : HasDist C74.G C74.d := props74.dist
  have hL : (toyLd74 R).Laws :=
    ldr_laws K K Unit _ (Reading.one C74) (fun _ => R) (fun _ => props74.place)
      (fun _ => hd) (fun _ => core74.pos)
  have hD : (toyLd74 R).Dist 4 :=
    ldr_dist K K Unit _ (Reading.one C74) (fun _ => R) 4 (one_even K C74) (fun _ => props74.place)
      (fun _ => hd) (fun _ => le_refl _)
  refine ⟨hL, hD, by norm_num, list74 _ hL hD, mca74 _ hL, ?_, ?_, ?_, ?_⟩
  · rw [ZMod.card]
    norm_num
  · exact ldr_zk K K Unit _ (Reading.one C74) (fun _ => R) 3 (fun _ => core74) (fun _ => le_refl _)
  · exact ldr_transparent K K Unit _ (Reading.one C74) (fun _ => R)
  · exact ldr_local K K Unit _ (Reading.one C74) (fun _ => R)

end Cb
