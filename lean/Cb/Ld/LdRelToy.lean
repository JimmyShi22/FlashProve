-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRelToy.lean: a small code at a radius not below half the distance that meets the nine
clauses of `Spec.ld_toy` together, nothing assumed beyond the hypotheses of `Spec.ld_toy`.

This file gives one concrete Reed-Solomon code and proves that, at a radius at which decoding is not
unique, it has the properties of a code that `Spec.ld_toy` lists. It is an example which shows that
these properties can hold together.
Statements and proofs. A guard against empty theorems; no parameter of a protocol.

The code is Reed-Solomon over the field with 101 elements (`LdToy.K`), at the points 1, .., 5, of
dimension 2 (one message symbol, one symbol of randomness; they fill the dimension) and distance 4,
with any finite set R of interleaved rows (`LdToy.toyLd R`).
The notions of the statement are `LdCode.Laws`, `LdCode.Dist`, `LdCode.ListAt`, `LdCode.MCAat`,
`LdCode.Zk`, `LdCode.Transparent`, `LdCode.LocalLE` of Cb/Ld/LdRel.lean.
The radius is 2: 2 · 2 is not below the distance 4, so a word may be within the radius of two
codewords; 2 is below the distance and below the Johnson radius.

Main names:
  `Spec.ld_toy`, for every R: the laws; distance at least 4; at most 2 codewords within 2 positions
    of any word (the Johnson bound); at most 16 exceptional θ on any line (Cb/Ld/LdRelAny.lean: the
    sets that omit at most 2 of 5 positions), and 16 < 101; the encoding is zero knowledge at 1
    position; the transformation (`Reading.one C5`, Cb/Gen/CodeRep.lean) is transparent and reads at
    most 1 native position for a long one.
  `Spec.ld_toy_two`: for one row, some word has two codewords with different messages within the
    radius (the zero word and the line x - 3, which vanishes at the point 3; the word is 0 at the
    points 1, 2, 3 and the line at 4, 5). So the toy is truly beyond unique decoding, and the list
    bound 2 is attained.

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

Limits: this file says nothing on real parameters: 16 of 101 is no security.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRelRepProofs
import Cb.Ld.LdRelAny
import Cb.Gen.JohnsonListProofs
import Code.RS
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false

namespace Cb
namespace LdToy
open Iop Prob Hiop Blocks

instance : Fact (Nat.Prime 101) := ⟨by norm_num⟩

/-- the field -/
abbrev K : Type := ZMod 101

/-- Reed-Solomon: points 1, .., 5; dimension 2; one message symbol, one symbol of randomness. (The
fields "radius 1, count 2" of the record are those of unique decoding and are not used, except in
`props5`, where the record's own law (`Code.Enc.Props`) is shown for them.) -/
def C5 : Code.Enc K := Code.RS.code (Code.RS.natPoints K 5) 2 1 1 1 2

/-- The toy: rows R under `C5`, read as they stand. -/
@[reducible] def toyLd (R : Type) [Fintype R] [DecidableEq R] : LdCode K (Reading.one C5).P :=
  (Reading.one C5).ld K fun _ => R

end LdToy

namespace Spec
open LdToy

def ld_toy : Prop :=
  ∀ (R : Type) [Fintype R] [DecidableEq R], (toyLd R).Laws ∧ (toyLd R).Dist 4 ∧ ¬ 2 * 2 < 4 ∧
    (toyLd R).ListAt 2 2 ∧ (toyLd R).MCAat 2 16 ∧ 16 < Fintype.card K ∧ (toyLd R).Zk 1 ∧
    (toyLd R).Transparent ∧ (toyLd R).LocalLE 1

def ld_toy_two : Prop :=
  ∃ (f : (toyLd Unit).Word) (w w' : (toyLd Unit).N.Wit),
    w.1 ≠ w'.1 ∧
    (toyLd Unit).Near 2 f ((toyLd Unit).enc w.1 w.2) ∧
    (toyLd Unit).Near 2 f ((toyLd Unit).enc w'.1 w'.2)

end Spec

namespace LdToy
open Iop Prob Hiop Blocks

theorem props5 : C5.Props K :=
  Code.RS.props_natPoints (F := K) (E := K) 101 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem core5 : C5.Core := ⟨props5.place, props5.dist, by decide, props5.hides⟩

theorem cnt_sets : cnt (fun S : Finset (Fin 5) => Fintype.card (Fin 5) ≤ S.card + 2) = 16 := by
  rw [cnt_eq_card_filter]
  decide

theorem ld_toy : Spec.ld_toy := by
  intro R _ _
  have hd : HasDist C5.G C5.d := props5.dist
  have hL : (toyLd R).Laws :=
    ldr_laws K K Unit _ (Reading.one C5) (fun _ => R) (fun _ => props5.place)
      (fun _ => hd) (fun _ => core5.pos)
  refine ⟨hL, ?_, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ldr_dist K K Unit _ (Reading.one C5) (fun _ => R) 4 (one_even K C5)
      (fun _ => props5.place) (fun _ => hd) (fun _ => le_refl _)
  · refine ldr_list K K Unit _ (Reading.one C5) (fun _ => R) 2 2 (fun _ => props5.place)
      ((one_listAt K K C5 R 2 2).2 fun f => ?_)
    exact johnson_enc K K C5 2 hd (show 5 * (5 - 4) < (5 - 2) ^ 2 by norm_num) R f
  · have h := ld_mca_sets K (Reading.one C5).P (toyLd R) hL 2
    exact ld_mca_mono K _ _ 2 _ 16 (le_of_eq cnt_sets) h
  · rw [ZMod.card]
    norm_num
  · exact ldr_zk K K Unit _ (Reading.one C5) (fun _ => R) 1 (fun _ => core5) (fun _ => le_refl _)
  · exact ldr_transparent K K Unit _ (Reading.one C5) (fun _ => R)
  · exact ldr_local K K Unit _ (Reading.one C5) (fun _ => R)

/-- the line x - 3 vanishes at the point 3 -/
theorem eval3 : C5.encE K (fun _ => (-3 : K)) (fun _ => (1 : K)) (2 : Fin 5) = 0 := by
  simp [C5, Code.RS.code, Code.Enc.encE, Code.Enc.GE, Code.Enc.fm, Matrix.mulVec,
    dotProduct, Code.RS.natPoints]
  decide

theorem cnt_ge3 : cnt (fun x : Fin 5 => 3 ≤ x.val) = 2 := by
  rw [cnt_eq_card_filter]
  decide

theorem cnt_lt2 : cnt (fun x : Fin 5 => x.val < 2) = 2 := by
  rw [cnt_eq_card_filter]
  decide

theorem ld_toy_two : Spec.ld_toy_two := by
  let c : (toyLd Unit).Word := (toyLd Unit).enc (fun _ => -3) (fun _ => 1)
  refine ⟨fun p s => if 3 ≤ (p.2 : Fin 5).val then c p s else 0, (0, 0),
    (fun _ => -3, fun _ => 1), ?_, ?_, ?_⟩
  · intro h
    have h0 : (0 : K) = -3 := congrFun h ⟨(), ((), (0 : Fin 1))⟩
    exact absurd h0 (by decide)
  · have hz : (toyLd Unit).enc 0 0 = 0 := (ld_toy Unit).1.encLin.map_zero
    refine le_trans (cnt_mono (Q := fun x : Fin 5 => 3 ≤ x.val) fun x hx => ?_) (le_of_eq cnt_ge3)
    by_contra h3
    refine hx (funext fun α => ?_)
    show (if 3 ≤ x.val then c ⟨α.1, x⟩ (α.2.1, ()) else 0) =
      (toyLd Unit).enc 0 0 ⟨α.1, x⟩ (α.2.1, ())
    rw [if_neg h3, hz]
    rfl
  · refine le_trans (cnt_mono (Q := fun x : Fin 5 => x.val < 2) fun x hx => ?_) (le_of_eq cnt_lt2)
    by_contra h2
    refine hx (funext fun α => ?_)
    show (if 3 ≤ x.val then c ⟨α.1, x⟩ (α.2.1, ()) else 0) = c ⟨α.1, x⟩ (α.2.1, ())
    split_ifs with h3
    · rfl
    · have hx2 : x = (2 : Fin 5) := Fin.ext (show x.val = 2 by omega)
      subst hx2
      exact eval3.symm

end LdToy
end Cb
