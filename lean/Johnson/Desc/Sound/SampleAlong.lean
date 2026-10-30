-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SampleAlong.lean: "WHAT THE STORED TABLE DECODES TO": THE TYPED DATA's SAMPLE AND THE LIBRARY's ANSWER ALIKE THROUGH THE MAP OF SEEDS THAT FORGETS "THE FACTOR IS NOT 0": so the decoder and the collision at the shared chain's block 1 ARE THE LIBRARY's AT THE LIBRARY's OWN SAMPLE. Two definitions,
four theorems. A joint build of files of Johnson/Desc/Sound/ and of Johnson/Desc/K14/. General in the shape: no size is written.

  trS: a seed of the library's sample recZ (for each answer a point and a factor OTHER THAN 0: OnBytes/Slice/RecordRead.lean) as a seed of the typed data's sampleOf (a point and any element: Johnson/Desc/K14/Law/TypedIx.lean).
  mat_along: at corresponding seeds the two samples have ONE MATRIX: before the pads the equality kernel at the entry's bits; on the pads of the answer the factor times 1, X, X²; on the others' pads 0.
  ixLib: the typed data ixOf2 WITH THE LIBRARY's SAMPLE in sampleOf's place · ixOf2_is: ixOf2 is ixLib with sampleOf's seeds (withSeeds, Johnson/Desc/K14/Law/DecAlong.lean): rfl.
  dcd_lib | coll_lib: dcdAt | collAt (Johnson/Desc/K14/Law/CellsTie.lean) at (trS ρ, y) are ixLib's dec | Coll at (ρ, y): by dec_along | coll_along (DecAlong.lean).
WHAT IT IS FOR: the ties of fields (c), (d) of Johnson/Desc/Sound/DecFields.lean at tr := (trS ·, ·). WHAT STAYS OF THEM: that the top statements' index (DecR.ix at the release's sizes) IS ixLib (v, the matrix, the places, the radius, the rank: by unfolding at written sizes) and that the two readings of the stored string give
one table over the extension field.

Limits. Nothing on how often a table has a collision. A record whose factor IS 0 is tr of no record of the library's: what the two sides do there is not said.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K14.Law.CellsTie
import Johnson.Desc.K14.Law.DecAlong
import Johnson.Desc.K14.Law.Typed
import OnBytes.Slice.RecordRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Cb Cb.Ood

/-- A seed of the library's sample, as a seed of the typed data's: it forgets that the factor is not 0. -/
def trS (s : IndexShape) (err : Nat) (ρ : (recZ s.code.ell s.cubeBits s.answers).D) :
    (sampleOf (K := GE) s (fun t => OnBytes.Model.Reading.gl.val (thetaE t)) err).D :=
  fun a => ((ρ a).1, (ρ a).2.val)

/-- **At corresponding seeds the two samples have one matrix.** -/
theorem mat_along (s : IndexShape) (err : Nat) (ρ : (recZ s.code.ell s.cubeBits s.answers).D) :
    (sampleOf (K := GE) s (fun t => OnBytes.Model.Reading.gl.val (thetaE t)) err).mat (trS s err ρ) =
      (recZ s.code.ell s.cubeBits s.answers).mat ρ := by
  funext a j
  show recMat s (List.ofFn (ρ a).1) (ρ a).2.val (fun t => OnBytes.Model.Reading.gl.val (thetaE t)) a.val j.val =
    (recZ s.code.ell s.cubeBits s.answers).mat ρ a j
  have hpl : s.plain = s.code.ell - 3 * s.answers := rfl
  unfold recMat
  by_cases h1 : j.val < s.plain
  · rw [if_pos h1, recZ_before _ _ _ ρ a j (by rw [← hpl]; exact h1), eqK_ofFn]
    unfold eqW
    congr 1
    funext t
    show (ρ a).1 t = if h : t.val < s.cubeBits then (ρ a).1 ⟨t.val, h⟩ else 0
    rw [dif_pos t.isLt]
  · rw [if_neg h1]
    have hj := j.isLt
    have ha' : (j.val - s.plain) / 3 < s.answers := by omega
    have hp : j.val = s.code.ell - 3 * s.answers + 3 * (⟨(j.val - s.plain) / 3, ha'⟩ : Fin s.answers).val +
        (⟨(j.val - s.plain) % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3).val := by
      show j.val = s.code.ell - 3 * s.answers + 3 * ((j.val - s.plain) / 3) + (j.val - s.plain) % 3
      omega
    rw [recZ_pad _ _ _ ρ a j _ _ hp]
    by_cases h2 : (j.val - s.plain) / 3 = a.val
    · rw [if_pos (by unfold IndexShape.padPlace; omega), if_pos (Fin.ext h2)]
      have e : j.val - s.padPlace a.val 0 = (j.val - s.plain) % 3 := by
        unfold IndexShape.padPlace
        omega
      rw [e]
      rfl
    · rw [if_neg (by unfold IndexShape.padPlace; omega), if_neg fun h => h2 (congrArg Fin.val h)]

/-- The typed data, with the library's sample. -/
def ixLib (S : FoldeqShape) (eM : Nat)
    (rank : ((Fin S.index.v → Bool) → Fin (S.index.code.r + S.index.code.ell) → GE) → Nat) :
    Cb.LdIx GE (Fin (2 ^ S.index.code.logN)) (Fin (S.index.code.r + S.index.code.ell))
      (Fin S.index.code.ell) where
  v := S.index.v
  G := genOf (codeOf S.index.code)
  pl := Fin.natAdd S.index.code.r
  Z := recZ S.index.code.ell S.index.cubeBits S.index.answers
  eM := eM
  rank := rank

/-- The typed data is that, with sampleOf's seeds. -/
theorem ixOf2_is (S : FoldeqShape) (err eM : Nat)
    (rank : ((Fin S.index.v → Bool) → Fin (S.index.code.r + S.index.code.ell) → GE) → Nat) :
    ixOf2 S err eM rank = (ixLib S eM rank).withSeeds
      (sampleOf (K := GE) S.index (fun t => OnBytes.Model.Reading.gl.val (thetaE t)) err).D
      (sampleOf (K := GE) S.index (fun t => OnBytes.Model.Reading.gl.val (thetaE t)) err).mat err := rfl

/-- **Block 1's decoder is the library's at the library's own sample.** -/
theorem dcd_lib (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (c : Nat → Option (Nat × List UInt64)) (ρ : (ixLib p.S.fold eM rank).Z.D)
    (y : (ixLib p.S.fold eM rank).Row × (ixLib p.S.fold eM rank).Z.S → GE) :
    dcdAt p err eM rank c (trS p.S.fold.index err ρ, y) =
      (ixLib p.S.fold eM rank).dec (tabF OnBytes.Model.Reading.gl p.S.fold.index (colsOf c)) (ρ, y) :=
  Cb.LdIx.dec_along (ixLib p.S.fold eM rank) _ _ err (trS p.S.fold.index err)
    (mat_along p.S.fold.index err) _ ρ y

/-- **And its collision.** -/
theorem coll_lib (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (c : Nat → Option (Nat × List UInt64)) (ρ : (ixLib p.S.fold eM rank).Z.D)
    (y : (ixLib p.S.fold eM rank).Row × (ixLib p.S.fold eM rank).Z.S → GE) :
    collAt p err eM rank c (trS p.S.fold.index err ρ, y) ↔
      (ixLib p.S.fold eM rank).Coll (tabF OnBytes.Model.Reading.gl p.S.fold.index (colsOf c)) ρ :=
  Cb.LdIx.coll_along (ixLib p.S.fold eM rank) _ _ err (trS p.S.fold.index err)
    (mat_along p.S.fold.index err) _ ρ

end Desc.K14.Law

#print axioms Desc.K14.Law.mat_along
#print axioms Desc.K14.Law.ixOf2_is
#print axioms Desc.K14.Law.dcd_lib
#print axioms Desc.K14.Law.coll_lib
