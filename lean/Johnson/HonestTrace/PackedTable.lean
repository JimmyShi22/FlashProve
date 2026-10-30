-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/PackedTable.lean

A table of cells, as a term, that meets ReadsPacked (Johnson/HonestTrace/PackedTie.lean) if no two
matrices of tl's list have one array number (GtOne): at such tl the second clause of the smallness
test's "tie" can be met. The table serves that clause alone: it is 0 at every array number that no
matrix has; where the array U3 has such a number, the third clause of K8.TieOf, which reads U3,
holds at it only if all its sums are 0. It is not meant as the table of a whole tie.

ReadsPacked tl A a asks one table A to hold, at array number tl.gtTree μ and from column 0 on, the
packed array of matrix number μ, for every matrix of tl's list. If two matrices have one array
number, a table can do that only if their packed arrays agree wherever both shapes reach.

Main definitions: "GtOne tl": no two matrices of tl's list, below tl.NM, have one number in
tl.gtTree. It is a premise on public numbers. "tableOf tl a": at array number t the packed array
packedPlan tl a μ of the first matrix μ with tl.gtTree μ = t; 0 at every other array number.

Main theorems:
* "readsPacked_tableOf": under GtOne tl, ReadsPacked tl (tableOf tl a) a, for all integers a.
* "packedBy_tableOf": under NamesFit, MeetsAll, k < 25 and GtOne tl: PackedBy tl (tableOf tl (T k))
  at the cells cellsAtOf (cellsC X T) (matsOf X k). (Under GtOne, PackedBy tl (tableOf tl a) a holds
  at all integers a; of the trace this theorem uses cellsAtOf_eq alone.)
* "gtOne_of_nodup", "gtOne_of_test": if tl.gtTree has tl.NM members and no member stands twice (or:
  the routine HTailF2.allDistinct says true of it), GtOne tl.

On GtOne. The verifier of OnBytes/Model/ tests both halves of gtOne_of_test: fixedBeforeTheMatrixF
(OnBytes/Model/Tail.lean) refuses unless tl.gtTree.size = tl.NM, and HTailF2.objectsF unless
allDistinct tl.gtTree.toList. If objectsF returns a state, that state's gtTree has no member twice
(objectsF_syms, OnBytes/Tie/Pv/Tail/EndSyms.lean). The description of the protocol has texts of its
own with the same two tests (orderOk, Johnson/Desc/First/K8/Order.lean;
Johnson/Desc/First/TailClaims/Equations.lean). No theorem here draws GtOne from a run. By a reading
of HTailF2.shapeF (OnBytes/Model/Tail.lean), which fills gtTree, each matrix gets an array of its
own, read from column 0: a matrix of the sub-proof one of the arrays PK or PX, by counters; a
borrowed matrix one of the arrays PF, by a counter, and only with the first column 0 and the rows
and columns that the handed list of borrowed arrays gives. No theorem of this library is cited here
for: what shapeF returns meets GtOne.

Limits. GtOne is not shown in this file at what Verify.publicOf returns. Like
Johnson/HonestTrace/PackedTie.lean this file can be built only where the files under
Johnson/Desc/K8/Honest/ and Johnson/Desc/ProofFile/Honest/ lie. tableOf is 0 at every number that no
matrix below tl.NM has in tl.gtTree. By a reading of the order in which shapeF numbers the arrays
(those of U1 to U3 that the sub-proof has, PK, PX, ZZ, BZ, PF), the numbers of U3, ZZ and BZ are
such where the sub-proof has U3; no theorem here says so. tableOf is made of packedPlan, at tl's
rows. tableOf tl (T l) has the image of packedOf S T l μ at tl.gtTree μ under GtOne tl and ShapesFit
tl S l (tableOf_meets, Johnson/HonestTrace/PackedJoins.lean). Neither premise is shown in this file
at a written list (the second, at the sizes Sz.ref under the library's head: shapesFit_plan,
Johnson/Desc/ProofFile/Honest/K8/PlanAtHead.lean); no theorem shows the two at one list.

Not claimed: K8.TieOf; that a prover's arrays are this table; that a verifier accepts.

-/
import Johnson.HonestTrace.PackedTie
import OnBytes.Tie.Pv.Tail.EndSyms

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Road
open OnBytes.Model (HTailF2)

/-- No two matrices of tl's list have one symbol array. -/
def GtOne (tl : HTailF2) : Prop :=
  ∀ μ, μ < tl.NM → ∀ ν, ν < tl.NM → tl.gtTree.getD μ 0 = tl.gtTree.getD ν 0 → μ = ν

/-- **The table of the packed arrays**: at array number t the packed array of the first matrix of
tl's list whose symbol array is t; 0 at every other array number. Where the numbers of U3, ZZ and BZ
are no matrix's it holds no reads and no digits: it is made to meet ReadsPacked, not the third
clause of K8.TieOf. -/
def tableOf (tl : HTailF2) (a : ℕ → ℕ → ℕ → ℤ) (t i' c : ℕ) : Cb.Gl.E :=
  match (List.range tl.NM).find? fun μ => tl.gtTree.getD μ 0 == t with
  | some μ => algebraMap Cb.Gl.F Cb.Gl.E (packedPlan tl a μ i' c)
  | none => 0

/-- Under GtOne tl, for μ < tl.NM: the first matrix with μ's array number is μ. -/
theorem find_gt {tl : HTailF2} (h : GtOne tl) {μ : ℕ} (hμ : μ < tl.NM) :
    ((List.range tl.NM).find? fun ν => tl.gtTree.getD ν 0 == tl.gtTree.getD μ 0) = some μ := by
  cases hf : (List.range tl.NM).find? fun ν => tl.gtTree.getD ν 0 == tl.gtTree.getD μ 0 with
  | none =>
    have := List.find?_eq_none.1 hf μ (List.mem_range.2 hμ)
    simp at this
  | some ν =>
    have h1 := List.find?_some hf
    have h2 := List.mem_range.1 (List.mem_of_find?_eq_some hf)
    rw [h ν h2 μ hμ (by simpa using h1)]

/-- Under GtOne tl: the table tableOf tl a holds packedPlan tl a at each matrix's symbol array. -/
theorem readsPacked_tableOf {tl : HTailF2} (h : GtOne tl) (a : ℕ → ℕ → ℕ → ℤ) :
    ReadsPacked tl (tableOf tl a) a := by
  intro μ hμ c _ i' _
  unfold tableOf
  rw [find_gt h hμ]

/-- If tl.gtTree has tl.NM members and no member stands twice in it: GtOne tl. -/
theorem gtOne_of_nodup {tl : HTailF2} (hs : tl.gtTree.size = tl.NM)
    (hn : tl.gtTree.toList.Nodup) : GtOne tl := by
  intro μ hμ ν hν e
  have h1 : μ < tl.gtTree.toList.length := by rw [Array.length_toList, hs]; exact hμ
  have h2 : ν < tl.gtTree.toList.length := by rw [Array.length_toList, hs]; exact hν
  have g : ∀ k (hk : k < tl.gtTree.toList.length), tl.gtTree.getD k 0 = tl.gtTree.toList[k] :=
    fun k hk => by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hk),
        Array.getElem_toList]
      rfl
  rw [g μ h1, g ν h2] at e
  exact (List.Nodup.getElem_inj_iff hn).1 e

/-- If tl.gtTree has tl.NM members and the routine HTailF2.allDistinct, which HTailF2.objectsF calls
on it, says true: GtOne tl. -/
theorem gtOne_of_test {tl : HTailF2} (hs : tl.gtTree.size = tl.NM)
    (ht : HTailF2.allDistinct tl.gtTree.toList = true) : GtOne tl :=
  gtOne_of_nodup hs (OnBytes.Tie.Pv.Tail.allDistinct_nodup _ ht)

variable {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- Under NamesFit, MeetsAll, k < 25 and GtOne tl: PackedBy holds of the table tableOf tl (T k) and
the cells read through matsOf X k. Of K8.TieOf this is the second clause alone; where U3's array
number is no matrix's, the third holds at this table only if all its sums are 0. -/
theorem packedBy_tableOf (N : NamesFit X T) (M : MeetsAll X i x T) {k : ℕ} (hk : k < 25)
    {tl : HTailF2} (h : GtOne tl) :
    PackedBy tl (tableOf tl (T k)) (ProofFile.Honest.K8.cellsAtOf (cellsC X T) (matsOf X k)) :=
  packedBy_trace N M hk tl _ (readsPacked_tableOf h (T k))

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.find_gt
#print axioms OnBytes.HonestTrace.readsPacked_tableOf
#print axioms OnBytes.HonestTrace.gtOne_of_nodup
#print axioms OnBytes.HonestTrace.gtOne_of_test
#print axioms OnBytes.HonestTrace.packedBy_tableOf
