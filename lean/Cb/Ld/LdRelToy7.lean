-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRelToy7.lean: a second small code beyond half the distance, whose encoding hides two
positions in this sense: `(toyLd7 R).Zk 2` (`LdCode.Zk`, Cb/Ld/LdRel.lean), that meets the nine
clauses of `Spec.ld_toy7` together, nothing assumed beyond the hypotheses of the statements and
whatever the arguments hold as proofs.

This file gives one concrete Reed-Solomon code and proves that, at a radius at which decoding is not
unique, it has the properties of a code that `Spec.ld_toy7` lists.
Statements and proofs. A guard against empty theorems; no parameter of a protocol.

Why a second toy: the toy of Cb/Ld/LdRelToy.lean (length 5, dimension 2) has one symbol of
randomness: its encoding hides one position in this sense: `(toyLd R).Zk 1` (`LdCode.Zk`,
Cb/Ld/LdRel.lean). An oracle message that lies in two groups is read by two tests, each at one long
position at least: its encoding has to hide two. At length 5 with two symbols of randomness the
distance is 3, and no radius is both beyond half the distance and below the Johnson radius.

The code is Reed-Solomon over the field with 101 elements (`LdToy.K`), at the points 1, .., 7, of
dimension 3 (one message symbol, two symbols of randomness; they fill the dimension) and distance 5,
with any finite set R of interleaved rows: `LdToy7.toyLd7 R`.
The laws (`LdCode.Laws`, Cb/Ld/LdRel.lean): encoder and transformation are linear, the encoder is
injective, the transformation reads what it declares. The other notions of the statement are
`LdCode.Dist`, `LdCode.ListAt`, `LdCode.MCAat`, `LdCode.Zk`, `LdCode.Transparent`, `LdCode.LocalLE`
of Cb/Ld/LdRel.lean.
The radius is 3: 2 · 3 is not below the distance 5; 3 is below the distance and below the Johnson
radius (`InJohnson n d e`, Cb/Gen/JohnsonList.lean, is `n * (n - d) < (n - e) ^ 2`: at 7, 5, 3:
7 · 2 < 4 · 4).

Main names:
  `Spec.ld_toy7`, for every R: the laws; distance at least 5; at most 7 codewords within 3 positions
    of any word (the Johnson bound: `listMax n d e`, Cb/Gen/JohnsonList.lean, is
    `n * (d - e) / ((n - e) ^ 2 - n * (n - d))`: at 7, 5, 3: 7 · 2 / 2); at most 64 exceptional θ on
    any line (Cb/Ld/LdRelAny.lean: the sets that omit at most 3 of 7 positions: 1 + 7 + 21 + 35),
    and 64 < 101; the encoding is zero knowledge at 2 positions; the transformation is transparent
    and reads at most 1 native position for a long one.
  `LdToy7.list7`, `LdToy7.mca7`: list and agreement for every code over this field read at these
    seven positions, under the hypotheses of their statements: for complexes, interleavings, doubled
    codes (`C.il Bool`: `LdCode.il`, Cb/Ld/LdRel.lean).
  `Spec.ld_toy7_two`: for one row, some word has two codewords with different messages within the
    radius (the zero word and (x - 1)(x - 2) = x² - 3 x + 2; the word is 0 at the points 1, 2, 3, 4
    and the parabola at 5, 6, 7).

Notation:
  `C.Dist d`: the transform of a non-zero codeword (the encoding of a pair (message, randomness)
    other than (0, 0)) is non-zero at d long positions or more.
  `C.Near e f g`: two native words are within e long positions of each other.
  `C.ListAt e L`: `cnt (fun w => C.Near e f (C.enc w.1 w.2)) ≤ L` for every native word f.
  `C.MCAat e bad`: mutual correlated agreement on lines under the transformation, as a count of
    exceptional θ: at most `bad`, over the sets S with `Fintype.card P ≤ S.card + e`.
  `C.Transparent`: `∃ bk, C.TranspBy bk`: "bk" computes, from a long position and the long symbol of
    a codeword there, the native symbols that were read for it.
  `C.LocalLE b`: `(C.src x).card ≤ b` for every long position x.
  (`C`: an `LdCode E P`; P: the long positions; all of Cb/Ld/LdRel.lean.) (`cnt`: Prob/Cnt.lean)

Limits: this file says nothing on real parameters: 64 of 101 is no security. It does not say that
the list bound 7 is attained.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRelToy
import Cb.Ld.LdRelJohnsonProofs

set_option autoImplicit false

namespace Cb
namespace LdToy7
open Iop Prob Hiop Blocks LdToy

/-- Reed-Solomon: points 1, .., 7; dimension 3; one message symbol, two symbols of randomness. The
record's fields `e` = 1 (a radius) and `mca` = 2 (a count) are those for which the record's own law
(`Code.Enc.Props`) is shown, in `props7`; every statement below names its own radius and counts. -/
def C7 : Code.Enc K := Code.RS.code (Code.RS.natPoints K 7) 3 1 2 1 2

/-- the long positions -/
abbrev P7 : Type := (Reading.one C7).P

/-- The toy: rows R under `C7`, read as they stand. -/
@[reducible] def toyLd7 (R : Type) [Fintype R] [DecidableEq R] : LdCode K P7 :=
  (Reading.one C7).ld K fun _ => R

end LdToy7

namespace Spec
open LdToy LdToy7

def ld_toy7 : Prop :=
  ∀ (R : Type) [Fintype R] [DecidableEq R], (toyLd7 R).Laws ∧ (toyLd7 R).Dist 5 ∧ ¬ 2 * 3 < 5 ∧
    (toyLd7 R).ListAt 3 7 ∧ (toyLd7 R).MCAat 3 64 ∧ 64 < Fintype.card K ∧ (toyLd7 R).Zk 2 ∧
    (toyLd7 R).Transparent ∧ (toyLd7 R).LocalLE 1

def ld_toy7_two : Prop :=
  ∃ (f : (toyLd7 Unit).Word) (w w' : (toyLd7 Unit).N.Wit),
    w.1 ≠ w'.1 ∧
    (toyLd7 Unit).Near 3 f ((toyLd7 Unit).enc w.1 w.2) ∧
    (toyLd7 Unit).Near 3 f ((toyLd7 Unit).enc w'.1 w'.2)

end Spec

namespace LdToy7
open Iop Prob Hiop Blocks LdToy

theorem props7 : C7.Props K :=
  Code.RS.props_natPoints (F := K) (E := K) 101 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem core7 : C7.Core := ⟨props7.place, props7.dist, by decide, props7.hides⟩

theorem card7 : Fintype.card P7 = 7 := Fintype.card_fin 7

set_option maxRecDepth 100000 in
theorem cnt_sets7 : cnt (fun S : Finset (Fin 7) => Fintype.card (Fin 7) ≤ S.card + 3) = 64 := by
  rw [cnt_eq_card_filter]
  decide

/-- Every code over `K` at the seven positions with the laws and distance at least 5 has at most 7
codewords within 3 positions of any word. -/
theorem list7 (D : LdCode K P7) (hL : D.Laws) (hD : D.Dist 5) : D.ListAt 3 7 := by
  have hJ : InJohnson (Fintype.card P7) 5 3 := by
    rw [card7]
    unfold InJohnson
    norm_num
  have hl : listMax (Fintype.card P7) 5 3 = 7 := by
    rw [card7]
    unfold listMax
    norm_num
  have h := ld_list_johnson K P7 D 5 3 hL hD hJ
  rwa [hl] at h

/-- Every code over `K` at the seven positions with the laws has at most 64 exceptional values on
any line, at the radius 3. -/
theorem mca7 (D : LdCode K P7) (hL : D.Laws) : D.MCAat 3 64 :=
  ld_mca_mono K _ _ 3 _ 64 (le_of_eq cnt_sets7) (ld_mca_sets K P7 D hL 3)

theorem ld_toy7 : Spec.ld_toy7 := by
  intro R _ _
  have hd : HasDist C7.G C7.d := props7.dist
  have hL : (toyLd7 R).Laws :=
    ldr_laws K K Unit _ (Reading.one C7) (fun _ => R) (fun _ => props7.place)
      (fun _ => hd) (fun _ => core7.pos)
  have hD : (toyLd7 R).Dist 5 :=
    ldr_dist K K Unit _ (Reading.one C7) (fun _ => R) 5 (one_even K C7) (fun _ => props7.place)
      (fun _ => hd) (fun _ => le_refl _)
  refine ⟨hL, hD, by norm_num, list7 _ hL hD, mca7 _ hL, ?_, ?_, ?_, ?_⟩
  · rw [ZMod.card]
    norm_num
  · exact ldr_zk K K Unit _ (Reading.one C7) (fun _ => R) 2 (fun _ => core7) (fun _ => le_refl _)
  · exact ldr_transparent K K Unit _ (Reading.one C7) (fun _ => R)
  · exact ldr_local K K Unit _ (Reading.one C7) (fun _ => R)

/-- the parabola x² - 3 x + 2 vanishes at the point 1; `eval2`: at the point 2 -/
theorem eval1 :
    C7.encE K (fun _ => (2 : K)) (fun i => if i.val = 0 then (-3 : K) else 1) (0 : Fin 7) = 0 := by
  simp [C7, Code.RS.code, Code.Enc.encE, Code.Enc.GE, Code.Enc.fm, Matrix.mulVec,
    dotProduct, Code.RS.natPoints]
  decide

theorem eval2 :
    C7.encE K (fun _ => (2 : K)) (fun i => if i.val = 0 then (-3 : K) else 1) (1 : Fin 7) = 0 := by
  simp [C7, Code.RS.code, Code.Enc.encE, Code.Enc.GE, Code.Enc.fm, Matrix.mulVec,
    dotProduct, Code.RS.natPoints]
  decide

theorem cnt_ge4 : cnt (fun x : Fin 7 => 4 ≤ x.val) = 3 := by
  rw [cnt_eq_card_filter]
  decide

theorem cnt_mid : cnt (fun x : Fin 7 => 2 ≤ x.val ∧ x.val < 4) = 2 := by
  rw [cnt_eq_card_filter]
  decide

theorem ld_toy7_two : Spec.ld_toy7_two := by
  let c : (toyLd7 Unit).Word :=
    (toyLd7 Unit).enc (fun _ => 2) (fun q => if q.2.2.val = 0 then -3 else 1)
  refine ⟨fun p s => if 4 ≤ (p.2 : Fin 7).val then c p s else 0, (0, 0),
    (fun _ => 2, fun q => if q.2.2.val = 0 then -3 else 1), ?_, ?_, ?_⟩
  · intro h
    have h0 : (0 : K) = 2 := congrFun h ⟨(), ((), (0 : Fin 1))⟩
    exact absurd h0 (by decide)
  · have hz : (toyLd7 Unit).enc 0 0 = 0 := (ld_toy7 Unit).1.encLin.map_zero
    refine le_trans (cnt_mono (Q := fun x : Fin 7 => 4 ≤ x.val) fun x hx => ?_) (le_of_eq cnt_ge4)
    by_contra h4
    refine hx (funext fun α => ?_)
    show (if 4 ≤ x.val then c ⟨α.1, x⟩ (α.2.1, ()) else 0) =
      (toyLd7 Unit).enc 0 0 ⟨α.1, x⟩ (α.2.1, ())
    rw [if_neg h4, hz]
    rfl
  · refine le_trans (cnt_mono (Q := fun x : Fin 7 => 2 ≤ x.val ∧ x.val < 4) fun x hx => ?_)
      (le_trans (le_of_eq cnt_mid) (by norm_num))
    by_contra h2
    refine hx (funext fun α => ?_)
    show (if 4 ≤ x.val then c ⟨α.1, x⟩ (α.2.1, ()) else 0) = c ⟨α.1, x⟩ (α.2.1, ())
    split_ifs with h4
    · rfl
    · have hx2 : x = (0 : Fin 7) ∨ x = (1 : Fin 7) := by
        have : x.val = 0 ∨ x.val = 1 := by omega
        exact this.imp (fun h => Fin.ext h) fun h => Fin.ext h
      rcases hx2 with rfl | rfl
      · exact eval1.symm
      · exact eval2.symm

end LdToy7
end Cb
