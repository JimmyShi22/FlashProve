-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/NumbersUser.lean: K01_law, ROWS N1–N5: THAT THE STATEMENTS (NumbersFree.lean · SentAt.lean, this folder) ARE OF THE RIGHT SHAPE: the five premises on the plan's numbers of k01_digits_tied | k01_reads_tied
(Johnson/Desc/K1/Law/FiftyAtFull.lean), EACH TO ITS BINDER's LETTER (k := 14 l + k1Ix l d + 2 = noD l | noR l), from the Props as premises and the tests' yes.
  hinj_fifty    from GroupsPart · rowsAtFit N 25 · rowSegs_full [kernel]
  book_fifty    trees ∧ msgs, from BookFitSucc · DeclaredCounts · bookFit · what block k tells is P's layout
  hP: LaterSeatsOfTold's conclusion IS the binder (no join)
  hbase_fifty   N5: PAID: fenceFit_at (Johnson/Desc/First/FenceFit.lean), at base := N.treesAt ps[k]?: that the piece's base is that number is left to the files of this folder whose heads say «K01_law, J1» (tiled_base, Johnson/Road/K4/PieceAtFits.lean; told_len)
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.NumbersFree
import Johnson.Desc.K1.Law.SentAt
import Johnson.Desc.First.FenceFit
import Johnson.Desc.K1.Law.RowLFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes
open VerifiableInference.Desc.First (Numbers rowsAtFit bookFit fenceFit flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.K13.Law (openAt)
open IM (k1Ix)

theorem lt_places (l : ℕ) (hl : l < 25) (d : Bool) :
    14 * l + k1Ix l d + 2 < (flatPlacesOf linksFull true).length := by
  have e := of_decide_eq_true (List.all_eq_true.1
    (List.all_eq_true.1 k01_later_places l (List.mem_range.2 hl)) d (by cases d <;> simp))
  exact (List.getElem?_eq_some_iff.1 e).1

theorem hinj_fifty (h : GroupsPart) (N : Numbers) (hN : rowsAtFit N 25 = true) (l : ℕ)
    (hl : l < 25) (d : Bool) :
    ∀ m' ∈ First.rowSegs (openAt linksFull (flatPlacesOf linksFull true)
      (14 * l + k1Ix l d + 2 + 1)), N.groupAt m' = N.groupAt l → m' = l := by
  intro m' hm' e
  have a := of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1
    (List.all_eq_true.1 rowSegs_full l (List.mem_range.2 hl)) d (by cases d <;> simp)) m' hm')
  exact h N 25 l m' hN (by omega) (by omega) e

theorem book_fifty (h : BookFitSucc) (hc : DeclaredCounts) (N : Numbers)
    (told : List (List Oracle)) (hN : bookFit N (flatPlacesOf linksFull true) told = true) (l : ℕ)
    (hl : l < 25) (d : Bool) (P : Par) (decl : List Oracle)
    (ht : told[14 * l + k1Ix l d + 2]? = some decl)
    (hD : Declares decl (layOf P) P.sent.size (tenantOf P)) :
    N.treesAt (flatPlacesOf linksFull true)[14 * l + k1Ix l d + 2 + 1]? =
        N.treesAt (flatPlacesOf linksFull true)[14 * l + k1Ix l d + 2]? + (layOf P).shapes.size ∧
      N.msgsAt (flatPlacesOf linksFull true)[14 * l + k1Ix l d + 2 + 1]? =
        N.msgsAt (flatPlacesOf linksFull true)[14 * l + k1Ix l d + 2]? + P.sent.size := by
  have a := h N _ told _ decl hN (lt_places l hl d) ht
  rw [hD.trees, hc decl _ _ _ hD] at a
  exact a

theorem hbase_fifty (N : Numbers) (hN : fenceFit N linksFull (flatPlacesOf linksFull true) = true)
    (l : ℕ) (hl : l < 25) (d : Bool) :
    ∀ u ∈ First.sampledIn N (openAt linksFull (flatPlacesOf linksFull true)
      (14 * l + k1Ix l d + 2)),
      u.1 < N.treesAt (flatPlacesOf linksFull true)[14 * l + k1Ix l d + 2]? :=
  fun u hu => First.fenceFit_at N _ _ hN _ (Nat.le_of_lt (lt_places l hl d)) u hu

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hinj_fifty
#print axioms VerifiableInference.Desc.K1.book_fifty
#print axioms VerifiableInference.Desc.K1.hbase_fifty
#print axioms VerifiableInference.Desc.K1.oracles_declares
