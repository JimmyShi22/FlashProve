-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/NineInScope.lean: `XNine X` (Johnson/Road/K4/K4PlanNine.lean) IN THE GOALS' SCOPE.
That the twelve feed-forward links have nine matrices each and that the labels name the owners by
the rule are theorems under the public core (`size_even`, `owner_label`, `ix_of_core`). The
matrices' rows of symbols and columns are NOT taken off the layers' layout (for the matrix of the
planes no library law has them as numerals): they are read off the request's layout: the test
`namedThere` (or `laidThere`, which holds it) says that the array which a label names has the
entry's rows of symbols and columns; where the layout is the written one, these are closed numbers,
decided by Lean's kernel. One closed fact and three theorems.

  `sizes_written`: at the written layout the array of owner and name `ownerW g μ` has
    `Alg.symRows (sizeW μ).1` rows of symbols and `(sizeW μ).2` columns: 12 × 9, by the kernel.
  `named_of_laid`: `laidThere` holds `namedThere`.
  `xNine_of_named`: `XNine X` from publicOf's return, the public core, layout = layoutFull and
    `namedThere X (sizesOf X) layout = true`.
  `xNine_of_laid`: the same from `laidThere`.

Limits. K04_law IS NOT PROVED BY THIS. `namedThere` (or `laidThere`) STAYS A TEST: it is one of the
named tests in front of the composed meaning's closed constant; it has run true at the full-size
public files. That the layout is the written one is other files' to pin. The reference sizes alone.

-/
import Johnson.Road.K4.K4PlanNine
import Johnson.Goal.Meaning.LaidCovered
import Johnson.Goal.Meaning.HidPlanNM
import Johnson.G.LayoutLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Model.Verify (Public publicOf)
open OnBytes.Params (ReqLayout)
open VerifiableInference.Desc (arrayOf)
open Meaning (labAt ownerK ownerA nameOf namedThere laidThere)
open Cb.Pv.Tail (Size)
open Johnson.G (layoutFull)

/-- **At the written layout the nine arrays of each of the twelve groups have the numerals' rows of
symbols and columns.** -/
theorem sizes_written :
    ((List.range 12).all fun g => (List.range 9).all fun μ =>
      match arrayOf layoutFull (ownerW g μ).1 (nameOf (ownerW g μ).2) with
      | none => false
      | some A => A.sizeI == Alg.symRows (sizeW μ).1 && A.sizeC == (sizeW μ).2) = true := by
  decide +kernel

/-- `laidThere` holds `namedThere`. -/
theorem named_of_laid {X : Public} {s : ℕ → Size} {layout : ReqLayout}
    (T : laidThere X s layout = true) : namedThere X s layout = true := by
  unfold laidThere at T
  unfold namedThere
  rw [List.all_eq_true] at T ⊢
  intro k hk
  have T1 := T k hk
  rw [List.all_eq_true] at T1 ⊢
  intro a ha
  have T2 := T1 a ha
  cases hA : arrayOf layout (ownerK (labAt X k a)) (nameOf (ownerA (labAt X k a))) with
  | none =>
    rw [hA] at T2
    cases T2
  | some A =>
    rw [hA] at T2
    have T3 : (A.sizeI == Alg.symRows ((s k).m a) && A.sizeC == (s k).k a &&
      (List.range A.sizeI).all fun i => (List.range A.sizeC).all fun c =>
        (VerifiableInference.Desc.laidAt A i c).isSome) = true := T2
    rw [Bool.and_eq_true] at T3
    exact T3.1

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}

/-- **`XNine X` in scope**, from the test that the named arrays have the entries' sizes, at the
written layout. -/
theorem xNine_of_named (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    {layout : ReqLayout} (hl : layout = layoutFull)
    (T : namedThere X (Meaning.sizesOf X) layout = true) : XNine X := by
  subst hl
  obtain ⟨-, i7, i8⟩ := Meaning.ix_of_core h C
  have nm : ∀ g, g < 12 → (Meaning.sizesOf X (2 * g)).NM = 9 := fun g hg =>
    ((Meaning.follows_sizesOf (Meaning.nmFit_of_core h C)).NM (2 * g) (by omega)).trans
      (Meaning.size_even h C hg)
  have own : ∀ g, g < 12 → ∀ μ, μ < 9 →
      (ownerK (labAt X (2 * g) μ), ownerA (labAt X (2 * g) μ)) = ownerW g μ := by
    intro g hg μ hμ
    rw [Meaning.owner_label h C (k := 2 * g) (by omega)
      (by rw [Meaning.size_even h C hg]; exact hμ)]
    unfold Meaning.ownerOf ownerW
    rw [if_neg (by omega), if_neg (by omega), i7, i8]
    by_cases c : μ = 8 ∧ g ≠ 0
    · rw [if_pos c, if_pos ⟨c.1, by omega⟩]
      exact Prod.ext (by show 2 * g - 2 = 2 * (g - 1); omega) rfl
    · rw [if_neg c, if_neg (fun d => c ⟨d.1, by omega⟩)]
  refine ⟨nm, own, fun g hg μ hμ => ?_⟩
  have o := own g hg μ hμ
  have o1 : ownerK (labAt X (2 * g) μ) = (ownerW g μ).1 := congrArg Prod.fst o
  have o2 : ownerA (labAt X (2 * g) μ) = (ownerW g μ).2 := congrArg Prod.snd o
  unfold namedThere at T
  rw [List.all_eq_true] at T
  have T1 := T (2 * g) (List.mem_range.2 (by omega))
  rw [List.all_eq_true] at T1
  have T2 := T1 μ (List.mem_range.2 (by rw [nm g hg]; exact hμ))
  rw [o1, o2] at T2
  have S := sizes_written
  rw [List.all_eq_true] at S
  have S1 := S g (List.mem_range.2 hg)
  rw [List.all_eq_true] at S1
  have S2 := S1 μ (List.mem_range.2 hμ)
  cases hA : arrayOf layoutFull (ownerW g μ).1 (nameOf (ownerW g μ).2) with
  | none =>
    rw [hA] at S2
    cases S2
  | some A =>
    rw [hA] at S2 T2
    have S3 : (A.sizeI == Alg.symRows (sizeW μ).1 && A.sizeC == (sizeW μ).2) = true := S2
    have T3 : (A.sizeI == Alg.symRows ((Meaning.sizesOf X (2 * g)).m μ) &&
      A.sizeC == (Meaning.sizesOf X (2 * g)).k μ) = true := T2
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at S3 T3
    exact Prod.ext (T3.1.symm.trans S3.1) (T3.2.symm.trans S3.2)

/-- The same from `laidThere`. -/
theorem xNine_of_laid (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    {layout : ReqLayout} (hl : layout = layoutFull)
    (T : laidThere X (Meaning.sizesOf X) layout = true) : XNine X :=
  xNine_of_named h C hl (named_of_laid T)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.sizes_written
#print axioms OnBytes.Road.K4.named_of_laid
#print axioms OnBytes.Road.K4.xNine_of_named
#print axioms OnBytes.Road.K4.xNine_of_laid
