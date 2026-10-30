-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CellOfOwner.lean

Conditional: where the numbers of parts are the full size's (PartsFit X) and each borrowed matrix of
T has its owner's entries (BorrowedSame X T), the reader cellOf X T (Johnson/HonestTrace/Full.lean)
answers alike under a matrix's own sub-proof and label and under its owner's.

Three matrices are borrowed (Sz.ref.owner, Johnson/HonestTrace/Places.lean): xbI in a group's list
from group 1 on is xbO of the group before; qa in an attention sub-proof's list is qa of its group;
xbL in the head's list is xbO of group 11. Every other matrix is its own owner.

Main definitions and theorems:
* "BorrowedSame X T": three equations on T, at all rows and columns: T (2 g) at the number of xbI is
  T (2 (g - 1)) at the number of xbO, for 0 < g < 12; T (2 g + 1) at the number of qa is T (2 g) at
  the number of qa, for g < 12; T 24 at the number of xbL is T 22 at the number of xbO.
* "borrowedSame_of_meetsAll": MeetsAll X i x T gives BorrowedSame X T.
* "owner_entry_of_same": under PartsFit X and BorrowedSame X T, for σ : Seg of a proof with 12
  groups and μ, member number mu of its list: the owner is of the proof, has a number a for the
  matrix, and T at the owner's sub-proof and a is T at σ's sub-proof and mu, at the given row and
  column.
* "cellOf_owner": under the same: cellOf X T (σ.no 12) μ.label r c = cellOf X T ((Sz.ref.owner σ
  μ).1.no 12) (Sz.ref.owner σ μ).2.label r c.

Limits. These are conditional lemmas. PartsFit and BorrowedSame are premises: this file shows
PartsFit of no X, and BorrowedSame of a T only under MeetsAll, which it shows of nothing. At a
matrix that is its own owner cellOf_owner says that a term equals itself. owner_entry_of_same has
the sentence and the steps of owner_entries under weaker premises; owner_entries lies in
Johnson/HonestTrace/DigitsAtTrace.lean, which is not imported here and need not lie where this file
lies. All is at 12 groups and the numbers of parts 3, 1, 1, 4. Nothing under Johnson/Goal/ is
imported or called here.

Not claimed: anything on a prover, on what is committed, on what a verifier accepts, or on a
property of the protocol.

-/
import Johnson.HonestTrace.CellOfAt
import Johnson.HonestTrace.Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model Inst.Model.All
open OnBytes.Road
open OnBytes.Model.Layer (matIx)

variable {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- **Each borrowed matrix has its owner's entries**, at all rows and columns: three equations on
the lists of T. They are the three last fields of OrdsN (Johnson/Meaning/Lists.lean) at the lists of
T. -/
structure BorrowedSame (X : Model.Verify.Public) (T : Tr) : Prop where
  /-- the stream that enters a later group is the stream that left the group before -/
  ff : ∀ g, 0 < g → g < 12 → ∀ r c,
    T (2 * g) (matIx X.y).iXI r c = T (2 * (g - 1)) (matIx X.y).iXO r c
  /-- an attention sub-proof's qa is its group's -/
  att : ∀ g < 12, ∀ r c,
    T (2 * g + 1) ((Hd.shapeA X g).cf.NAs + 3) r c = T (2 * g) (matIx X.y).iQA r c
  /-- the head's stream is the stream that left group 11 -/
  head : ∀ r c, T 24 (X.hS.NHf + 3) r c = T 22 (matIx X.y).iXO r c

/-- MeetsAll X i x T gives BorrowedSame X T: the fields seamFF, seamA and seamH of its field ords.
-/
theorem borrowedSame_of_meetsAll (M : MeetsAll X i x T) : BorrowedSame X T :=
  ⟨M.ords.seamFF, M.ords.seamA, M.ords.seamH⟩

/-- Under PartsFit X and BorrowedSame X T, for σ : Seg of a proof with 12 groups: the owner of
member number mu of σ's list is of the proof, has a number for the matrix, and T holds there the
entry of matrix number mu of σ's list. -/
theorem owner_entry_of_same (N : PartsFit X) (S : BorrowedSame X T) {σ : Seg} (hσ : σ.Below 12)
    {mu : ℕ} {μ : MatName} (hμ : (MatName.all 3 1 1 4 σ)[mu]? = some μ) (r c : ℕ) :
    ∃ a, (Sz.ref.owner σ μ).1.Below 12 ∧
      MatName.no? 3 1 1 4 (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2 = some a ∧
      T ((Sz.ref.owner σ μ).1.no 12) a r c = T (σ.no 12) mu r c := by
  have hn := all_no_ref σ hμ
  have own : Sz.ref.owner σ μ = (σ, μ) → ∃ a, (Sz.ref.owner σ μ).1.Below 12 ∧
      MatName.no? 3 1 1 4 (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2 = some a ∧
      T ((Sz.ref.owner σ μ).1.no 12) a r c = T (σ.no 12) mu r c := fun e => by
    rw [e]
    exact ⟨mu, hσ, hn, rfl⟩
  have iQA : (matIx X.y).iQA = 6 := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 2 = 6
    rw [N.af, N.ad]
  have iXO : (matIx X.y).iXO = 7 := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 3 = 7
    rw [N.af, N.ad]
  have iXI : (matIx X.y).iXI = 8 := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 4 = 8
    rw [N.af, N.ad]
  cases σ with
  | ff g =>
    have hg : g < 12 := hσ
    cases μ <;> try exact own rfl
    · -- xbI
      obtain rfl : mu = 8 := (Option.some.inj (show some (3 + 1 + 4) = some mu from hn)).symm
      by_cases h0 : g = 0
      · exact own (if_pos h0)
      · have e : Sz.ref.owner (.ff g) .xbI = (.ff (g - 1), .xbO) := if_neg h0
        rw [e]
        refine ⟨7, show g - 1 < 12 by omega, rfl, ?_⟩
        have s := S.ff g (by omega) hg r c
        rw [iXI, iXO] at s
        exact s.symm
  | att g =>
    have hg : g < 12 := hσ
    cases μ <;> try exact own rfl
    · -- qa
      obtain rfl : mu = 4 := (Option.some.inj (show some (1 + 3) = some mu from hn)).symm
      refine ⟨6, hg, rfl, ?_⟩
      have s := S.att g hg r c
      rw [iQA, N.as g hg] at s
      exact s.symm
  | head =>
    cases μ <;> try exact own rfl
    · -- xbL
      obtain rfl : mu = 7 := (Option.some.inj (show some (4 + 3) = some mu from hn)).symm
      refine ⟨7, show 11 < 12 by norm_num, rfl, ?_⟩
      have s := S.head r c
      rw [iXO, N.hf] at s
      exact s.symm

/-- **The reader answers alike under the matrix's own key and under its owner's.** Under PartsFit X
and BorrowedSame X T, for σ : Seg of a proof with 12 groups and μ, member number mu of its list, at
every row r and column c: cellOf X T at σ's number and μ's label is cellOf X T at the owner's number
and the owner's label. By cellOf_label (Johnson/HonestTrace/CellOfAt.lean) on both sides. -/
theorem cellOf_owner (N : PartsFit X) (S : BorrowedSame X T) {σ : Seg} (hσ : σ.Below 12)
    {mu : ℕ} {μ : MatName} (hμ : (MatName.all 3 1 1 4 σ)[mu]? = some μ) (r c : ℕ) :
    cellOf X T (σ.no 12) μ.label r c =
      cellOf X T ((Sz.ref.owner σ μ).1.no 12) (Sz.ref.owner σ μ).2.label r c := by
  obtain ⟨a, ob, on, oe⟩ := owner_entry_of_same N S hσ hμ r c
  rw [cellOf_label N T hσ (all_no_ref σ hμ) r c, cellOf_label N T ob on r c, oe]

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.borrowedSame_of_meetsAll
#print axioms OnBytes.HonestTrace.owner_entry_of_same
#print axioms OnBytes.HonestTrace.cellOf_owner
