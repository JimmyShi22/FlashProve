-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TiePlan.lean: THE ITEM "tie m" AT THE PLAN's OWN RECORD, AT ANY
SIZES: FROM TWO EQUATIONS ON A TABLE OF CELLS, AT A READER's OWN CELLS, TO THE LIBRARY's K8.TieOf.
Four statements and their proofs. No definition. A record tl, a table A, a reader of cells C, sizes
S and a list of matrices as letters: no thread, no run, no witness, no public record X, no trace.

  cast_signedOf          the image in the base field of signedOf x is x, at every x
  smallBy_of_cellsSmall  where the library's test cellsSmall accepts the integers a at numbers p
                         that have tl's rows and columns: SmallBy tl a (the first clause of
                         K8.TieOf)
  readsPacked_of_cells   where tl has S's shapes at segment l, and the list mats names at each
                         number what S's own list of l names there, under l's own number
                         (hmats): if the table holds, at the matrices' arrays, inside S's packed
                         shapes, the images of packedCells S C.cell l: ReadsPacked tl A (cellsAtOf C
                         mats)
  tieOf_plan             these, TablesLie, and the second equation (row 0 of the array of reads is
                         the vector of reads at tl's own tables, at cellsAtOf C mats): K8.TieOf tl A

THE INTEGERS ARE cellsAtOf C mats THEMSELVES: the balanced integers of the reader's own cells
(Johnson/Desc/ProofFile/Honest/K8/Part.lean): nothing is compared with a second naming of them.

BY CALLS: tieOf_iff (Johnson/HonestTrace/PackedJoins.lean) · packedBy_iff
(Johnson/HonestTrace/PackedTie.lean) · tieThird_sent (Johnson/HonestTrace/ReadsTie.lean) ·
parFits_parOfMats (Johnson/HonestTrace/Reads.lean) · pack3_cast (Johnson/HonestTrace/Packed.lean).

Limits. hmats BARS A BORROWED MATRIX: there the list of the place names the owner's segment, while
packedCells asks the reader under the borrower's number: a premise on the reader would be wanted:
not here. Every premise is asked and none is proved here. cellsSmall is a premise on the reader's
cells. Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.HonestTrace.PackedJoins
import Johnson.HonestTrace.ReadsTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open OnBytes.Model (HTailF2 lbz)
open OnBytes.HonestTrace (Sz ShapesFit TablesLie ParFits SmallBy ReadsPacked packedPlan packedCells
  parOfMats parFits_parOfMats tieOf_iff packedBy_iff tieThird_sent pack3_cast)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open ProofFile.Honest (Cells)
open ProofFile.Honest.K8 (cellsAtOf signedOf)
open VerifiableInference.Desc.First (K8.TieOf)
open VerifiableInference.Desc.First.K8 (Par)
open VerifiableInference.Desc.First.K8.Honest (CellsAt cellsSmall)

/-- **The image of signedOf x is x.** -/
theorem cast_signedOf (x : Cb.Gl.F) : ((signedOf x : ℤ) : Cb.Gl.F) = x := by
  unfold signedOf
  split_ifs
  · rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val x
  · rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_self, sub_zero]
    exact ZMod.natCast_zmod_val x

/-- **Where the library's test on the cells accepts, the first clause holds.** -/
theorem smallBy_of_cellsSmall {p : Par} {tl : HTailF2} (P : ParFits p tl.mats) {a : CellsAt}
    (h : cellsSmall p a = true) : SmallBy tl a := by
  intro μ _ c hc i hi
  rw [← P.ks μ] at hc
  rw [← P.ms μ] at hi
  have hlt : μ < p.ks.length := by
    by_contra hge
    rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hge)] at hc
    exact Nat.not_lt_zero _ hc
  unfold cellsSmall at h
  have h1 := List.all_eq_true.1 h μ (List.mem_range.2 hlt)
  have h2 := List.all_eq_true.1 h1 i (List.mem_range.2 hi)
  have h3 := of_decide_eq_true (List.all_eq_true.1 h2 c (List.mem_range.2 hc))
  have e : ((2 ^ lbz : ℕ) : ℤ) = 131072 := rfl
  rw [e, Int.abs_eq_natAbs]
  omega

/-- **The first equation, at the reader's own cells, is ReadsPacked at their balanced integers.** -/
theorem readsPacked_of_cells {tl : HTailF2} {S : Sz} {l : ℕ} (hS : ShapesFit tl S l) (C : Cells)
    (mats : List (ℕ × String × ℕ))
    (hmats : ∀ mu σ μ, S.matAt l mu = some (σ, μ) → mats[mu]? = some (l, μ.label, 0))
    (A : ℕ → ℕ → ℕ → Cb.Gl.E)
    (hA : ∀ ν, ν < tl.NM → ∀ c, c < (S.packedShape l ν).2 → ∀ i', i' < (S.packedShape l ν).1 →
      A (tl.gtTree.getD ν 0) i' c = algebraMap Cb.Gl.F Cb.Gl.E (packedCells S C.cell l ν i' c)) :
    ReadsPacked tl A (cellsAtOf C mats) := by
  intro ν hν c hc i' hi
  have e := hS ν hν
  have e1 : (S.shapeNo l ν).1 = (tl.mats.getD ν {}).m := by rw [e]
  have e2 : (S.shapeNo l ν).2 = (tl.mats.getD ν {}).k := by rw [e]
  have hc' : c < (S.shapeNo l ν).2 := by rw [e2]; exact hc
  have hi' : i' < Alg.symRows (S.shapeNo l ν).1 := by rw [e1]; exact hi
  rw [hA ν hν c hc' i' hi']
  congr 1
  cases hm : S.matAt l ν with
  | none =>
    have hsn : S.shapeNo l ν = (0, 0) := by simp only [Sz.shapeNo, hm]
    rw [hsn] at hc'
    exact absurd hc' (Nat.not_lt_zero _)
  | some q =>
    obtain ⟨σ, μ⟩ := q
    have hsn : S.shapeNo l ν = S.shape σ μ := by simp only [Sz.shapeNo, hm]
    have f1 : (S.shape σ μ).1 = (tl.mats.getD ν {}).m := by rw [← hsn]; exact e1
    have f2 : c < (S.shape σ μ).2 := by rw [← hsn]; exact hc'
    unfold packedCells packedPlan
    rw [hm]
    show (if c < (S.shape σ μ).2 then _ else _) = _
    rw [if_pos f2, pack3_cast, f1]
    congr 1
    funext r
    unfold cellsAtOf
    rw [hmats ν σ μ hm]
    show C.cell l μ.label r c = ((signedOf (C.cell l μ.label r (0 + c)) : ℤ) : Cb.Gl.F)
    rw [Nat.zero_add, cast_signedOf]

/-- **From the two equations at the reader's own cells to the library's item.** -/
theorem tieOf_plan {tl : HTailF2} {S : Sz} {l nR : ℕ} (hS : ShapesFit tl S l) (C : Cells)
    (mats : List (ℕ × String × ℕ))
    (hmats : ∀ mu σ μ, S.matAt l mu = some (σ, μ) → mats[mu]? = some (l, μ.label, 0))
    (hsmall : cellsSmall (parOfMats tl.mats) (cellsAtOf C mats) = true)
    (hLie : TablesLie tl.mats tl.funs nR) (A : ℕ → ℕ → ℕ → Cb.Gl.E)
    (hA : ∀ ν, ν < tl.NM → ∀ c, c < (S.packedShape l ν).2 → ∀ i', i' < (S.packedShape l ν).1 →
      A (tl.gtTree.getD ν 0) i' c = algebraMap Cb.Gl.F Cb.Gl.E (packedCells S C.cell l ν i' c))
    (hR : ∀ j < nR, A (u3Of tl) 0 j =
      OnBytes.Model.Reading.gl.val (First.K8.Honest.readAt (parOfMats tl.mats) tl.funs.toList
        (cellsAtOf C mats) j)) : K8.TieOf tl A :=
  (tieOf_iff tl A).2 ⟨cellsAtOf C mats, smallBy_of_cellsSmall (parFits_parOfMats tl.mats) hsmall,
    (packedBy_iff tl A _).2 (readsPacked_of_cells hS C mats hmats A hA),
    tieThird_sent (parFits_parOfMats tl.mats) hLie hR⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.cast_signedOf
#print axioms ProofFile.Honest.K1.smallBy_of_cellsSmall
#print axioms ProofFile.Honest.K1.readsPacked_of_cells
#print axioms ProofFile.Honest.K1.tieOf_plan
