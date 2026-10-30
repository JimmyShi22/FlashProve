-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanWide.lean: THE ITEM "tie m" AT
THE PLAN's OWN RECORD, AT ANY SIZES, A BORROWED MATRIX ALLOWED. tieOf_plan
(Johnson/Desc/ProofFile/Honest/K1/Law/TiePlan.lean) WITH A WIDER PREMISE FOR hmats. One definition
of a premise's form, four statements and their proofs. TiePlan.lean is not turned.

WHY. hmats asks that the list mats names, at each number, the segment's OWN number, the matrix's own
label and the column 0. The place's own list names THE OWNER's segment and label. By the library's
Sz.owner (Johnson/HonestTrace/Places.lean) each segment but the first has just one borrowed matrix:
qa in an attention's segment is qa of its group's layers; xbI from group 1 on is xbO of the group
before; xbL in the head is xbO of the last group. SO UNDER hmats, AT THE PLACE's OWN LIST,
tieOf_plan CAN BE MET AT THE FIRST SEGMENT ALONE.

  pack3_congr                 the packing reads its column below the number of rows alone
  OwnersAgree S C mats l      A PREMISE ON THE READER C: inside S's shapes it answers under the
                              list's names as under l's own number and the own labels
  ownersAgree_of_own          hmats gives it, at every reader: the wider law reaches as far
  readsPacked_of_cells_wide   readsPacked_of_cells with OwnersAgree for hmats
  tieOf_plan_wide             tieOf_plan likewise

WHO MIGHT PAY OwnersAgree: at the reference sizes, at a reader whose cells are a trace's: the
library's cellOf_owner (Johnson/HonestTrace/CellOfOwner.lean), under PartsFit and BorrowedSame. NOT
HERE.

ON OwnersAgree: in the law it stands at the input's own cells under «valid», at hSmall's very
binders: of completeness's kind: NOT PUBLIC: told as such: NOT IN FRONT OF A LAW OVER COINS;
milder than hSmall. ON exchangeAtS_tie_wide: the term of exchangeAtS_tie_plan rides with it.
A public premise is swapped for a hidden one: the law reaches further and owes more: one more debt
of (P1)'s kind: what pays it comes from the trace (ownersAgree_trace, OwnersAgreeAtTrace.lean, by
cellOf_owner: under PartsFit and BorrowedSame, at Sz.ref); a premise laid anew pays nothing.
The term, and where the law is called:
Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanShare.lean's head.

Limits. OwnersAgree IS OF COMPLETENESS's KIND: it speaks of the input's cells. Every premise is
asked and none is proved here.
Nothing on soundness,
on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TiePlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (Sz ShapesFit TablesLie ReadsPacked packedPlan packedCells pack3
  parOfMats parFits_parOfMats tieOf_iff packedBy_iff tieThird_sent pack3_cast)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open ProofFile.Honest (Cells)
open ProofFile.Honest.K8 (cellsAtOf signedOf)
open VerifiableInference.Desc.First (K8.TieOf)
open VerifiableInference.Desc.First.K8.Honest (cellsSmall)

/-- The packing reads its column below the number of rows alone. -/
theorem pack3_congr {A : Type} [CommRing A] {m : ℕ} {col col' : ℕ → A}
    (h : ∀ r, r < m → col r = col' r) (i : ℕ) : pack3 m col i = pack3 m col' i := by
  have h0 : ∀ j, (if j < m then col j else 0) = (if j < m then col' j else 0) := fun j => by
    by_cases hj : j < m
    · rw [if_pos hj, if_pos hj, h j hj]
    · rw [if_neg hj, if_neg hj]
  unfold pack3
  rw [h0 (3 * i), h0 (3 * i + 1), h0 (3 * i + 2)]

/-- **A PREMISE ON A READER OF CELLS: under the names of the list mats it answers as under the
segment's own.** S: the sizes; C: the reader; l: the segment. At each number mu of S's own list of
segment l the list mats has an entry e (a segment's number, a label, a first column), and inside
S's shape of that matrix C answers at e as it answers at l's own number and the matrix's own label.
FOR A BORROWED MATRIX: there the place's list names the owner's segment and label. Where mats names
l's own number, the own label and the column 0 it holds of every reader (ownersAgree_of_own). OF
COMPLETENESS's KIND: IT SPEAKS OF THE INPUT's CELLS. A definition: a premise's form. -/
def OwnersAgree (S : Sz) (C : Cells) (mats : List (ℕ × String × ℕ)) (l : ℕ) : Prop :=
  ∀ mu σ μ, S.matAt l mu = some (σ, μ) → ∃ e, mats[mu]? = some e ∧
    ∀ r c, r < (S.shape σ μ).1 → c < (S.shape σ μ).2 →
      C.cell e.1 e.2.1 r (e.2.2 + c) = C.cell l μ.label r c

/-- **The premise hmats gives it, at every reader.** -/
theorem ownersAgree_of_own {S : Sz} (C : Cells) {mats : List (ℕ × String × ℕ)} {l : ℕ}
    (hmats : ∀ mu σ μ, S.matAt l mu = some (σ, μ) → mats[mu]? = some (l, μ.label, 0)) :
    OwnersAgree S C mats l := fun mu σ μ h =>
  ⟨_, hmats mu σ μ h, fun r c _ _ => by
    show C.cell l μ.label r (0 + c) = _
    rw [Nat.zero_add]⟩

/-- readsPacked_of_cells (TiePlan.lean) WITH OwnersAgree FOR hmats. -/
theorem readsPacked_of_cells_wide {tl : HTailF2} {S : Sz} {l : ℕ} (hS : ShapesFit tl S l)
    (C : Cells) (mats : List (ℕ × String × ℕ)) (hOwn : OwnersAgree S C mats l)
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
    obtain ⟨en, hen, hag⟩ := hOwn ν σ μ hm
    unfold packedCells packedPlan
    rw [hm]
    show (if c < (S.shape σ μ).2 then _ else _) = _
    rw [if_pos f2, pack3_cast, ← f1]
    refine pack3_congr (fun r hr => ?_) i'
    unfold cellsAtOf
    rw [hen]
    show C.cell l μ.label r c = ((signedOf (C.cell en.1 en.2.1 r (en.2.2 + c)) : ℤ) : Cb.Gl.F)
    rw [cast_signedOf, hag r c hr f2]

/-- **From the two equations at the reader's own cells to the library's item, A BORROWED MATRIX
ALLOWED.** tieOf_plan (TiePlan.lean) with OwnersAgree for hmats. -/
theorem tieOf_plan_wide {tl : HTailF2} {S : Sz} {l nR : ℕ} (hS : ShapesFit tl S l) (C : Cells)
    (mats : List (ℕ × String × ℕ)) (hOwn : OwnersAgree S C mats l)
    (hsmall : cellsSmall (parOfMats tl.mats) (cellsAtOf C mats) = true)
    (hLie : TablesLie tl.mats tl.funs nR) (A : ℕ → ℕ → ℕ → Cb.Gl.E)
    (hA : ∀ ν, ν < tl.NM → ∀ c, c < (S.packedShape l ν).2 → ∀ i', i' < (S.packedShape l ν).1 →
      A (tl.gtTree.getD ν 0) i' c = algebraMap Cb.Gl.F Cb.Gl.E (packedCells S C.cell l ν i' c))
    (hR : ∀ j < nR, A (u3Of tl) 0 j =
      OnBytes.Model.Reading.gl.val (First.K8.Honest.readAt (parOfMats tl.mats) tl.funs.toList
        (cellsAtOf C mats) j)) : K8.TieOf tl A :=
  (tieOf_iff tl A).2 ⟨cellsAtOf C mats, smallBy_of_cellsSmall (parFits_parOfMats tl.mats) hsmall,
    (packedBy_iff tl A _).2 (readsPacked_of_cells_wide hS C mats hOwn A hA),
    tieThird_sent (parFits_parOfMats tl.mats) hLie hR⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.pack3_congr
#print axioms ProofFile.Honest.K1.OwnersAgree
#print axioms ProofFile.Honest.K1.ownersAgree_of_own
#print axioms ProofFile.Honest.K1.readsPacked_of_cells_wide
#print axioms ProofFile.Honest.K1.tieOf_plan_wide
