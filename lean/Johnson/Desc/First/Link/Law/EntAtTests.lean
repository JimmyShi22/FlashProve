-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/EntAtTests.lean: THE TEST WITH CODE FOR THE ONE PREMISE OF EACH OF THE
SEVEN FIELDS OF SistersFull.lean ("every entry that the run's forms name has `EntAt`"): so that it
can be run at honest states. Definitions with code, and theorems.
  `vectorAtB nU tl sh t`: `TableAt`, as a Bool. `tableAt_of_vectorB`: a yes gives it. `entsAtB nU tl
    sh l`: every entry that a form of the list l names stands at virtual row 0 of such an array.
    `entAt_of_B`: **a yes at the fixed structure and the snapshot's looks gives `EntAt` of every
    such entry.**
  The names `vectorAtB`, `tableAt_of_vectorB`: `tableAtB` stands already in CoefsFit.lean (a like
    test).
  `entAt_at`: **the same from a yes at a state's own structure and its part's ledger:
    `EntAt` at `fixed9 φ s`**: so that a run of the test at a state is a member of the premise
    there.
  `entsAtB_row`, `entsAtB_digits`: THE TEST CAN SAY NO: at an entry of virtual row 1; at an entry of
    the digits' array: by Lean's kernel, at a small written structure at which an entry of vector 2
    gets a yes (`entsAtB_yes`).
Limits. Nothing is evaluated at a state of the protocol here. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.SistersFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims.Law (blank)

/-- `TableAt`, as a test with code. -/
def vectorAtB (nU : Array ℕ) (tl : HTailF2) (sh : List Look) (t : ℕ) : Bool :=
  ((List.range 3).any fun n0 => decide (0 < nU.getD n0 0) &&
      decide (tl.ix.U.getD n0 none = some t)) &&
    decide (tl.ix.ZZ ≠ t) && decide (tl.ix.BZ ≠ t) &&
    ((List.range tl.NM).all fun mu => decide (tl.gtTree.getD mu 0 ≠ t)) &&
    ((tl.z1.pieces.toList ++ tl.z2.pieces.toList).all fun p => decide (p.tree ≠ t)) &&
    unitLook sh t

/-- **A yes gives `TableAt`.** -/
theorem tableAt_of_vectorB {nU : Array ℕ} {tl : HTailF2} {sh : List Look} {t : ℕ}
    (h : vectorAtB nU tl sh t = true) : TableAt nU tl sh t := by
  unfold vectorAtB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h
  obtain ⟨n0, hn, hx⟩ := List.any_eq_true.1 a1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
  refine ⟨⟨n0, List.mem_range.1 hn, hx.1, hx.2⟩, a2, a3, fun mu hmu => ?_, fun k p hp => ?_, a6⟩
  · exact of_decide_eq_true (List.all_eq_true.1 a4 mu (List.mem_range.2 hmu))
  · refine of_decide_eq_true (List.all_eq_true.1 a5 p ?_)
    unfold zOf at hp
    by_cases hk : (k == 0) = true
    · rw [if_pos hk] at hp
      exact List.mem_append_left _ hp
    · rw [if_neg hk] at hp
      exact List.mem_append_right _ hp

/-- Every entry that a form of the list names stands at virtual row 0 of a table's vector. -/
def entsAtB (nU : Array ℕ) (tl : HTailF2) (sh : List Look) (l : List Aff) : Bool :=
  l.all fun f => f.ents.toList.all fun x => decide (x.row = 0) && vectorAtB nU tl sh x.tree

/-- **A yes at the fixed structure and the snapshot's looks gives `EntAt`.** -/
theorem entAt_of_B {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) {nU : Array ℕ}
    {q : α × Option Pub9} {tlb : HTailF2} {v : Pub9} (h1 : (π q.1).1 = some tlb)
    (hv : q.2 = some v) {l : List Aff}
    (h : entsAtB nU tlb (v.F.trees.toList.map look) l = true) :
    ∀ f ∈ l, ∀ x ∈ f.ents.toList, EntAt π nU q x := by
  intro f hf x hx
  have a := List.all_eq_true.1 (List.all_eq_true.1 h f hf) x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at a
  exact ⟨a.1, tlb, v, h1, hv, tableAt_of_vectorB a.2⟩

/-- **THE SAME AT A STATE's OWN STRUCTURE AND LEDGER**: the test reads none of the fourteen written
fields, and the snapshot's ledger is the part's. -/
theorem entAt_at {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α)
    (u : HTailF2) (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) {nU : Array ℕ} (s : S)
    (tl : HTailF2) (p : K9.Part) (htl : s.tl? = some tl) (hp : atS.get? s = some p) (l : List Aff)
    (h : entsAtB nU tl (p.F.trees.toList.map look) l = true) :
    ∀ f ∈ l, ∀ x ∈ f.ents.toList, EntAt π nU (fixed9 φ s) x := by
  have h1 : (π (fixed9 φ s).1).1 = some (blank u tl) := by
    show (π (φ s)).1 = _
    rw [hπ, htl]
    rfl
  have hv : (fixed9 φ s).2 = some (pubOf p) := by
    show (atS.get? s).map pubOf = _
    rw [hp]
    rfl
  exact entAt_of_B π h1 hv h

/-! ## The test can say no -/

/-- A small written structure: the digits' array is number 0, the planes' 1, vector 2 is 2. -/
def tlToy : HTailF2 := { ix := { ZZ := 0, BZ := 1, U := #[none, none, some 2] } }

/-- Three looks: number 2 is of the kind "table", with one row and one virtual row. -/
def shToy : List Look := [(HKind.table, 2, 1, 2), (HKind.table, 32, 1, 1), (HKind.table, 1, 1, 1)]

theorem entsAtB_yes :
    entsAtB #[0, 0, 1] tlToy shToy [{ ents := #[{ tree := 2, row := 0 }] }] = true := by
  decide +kernel

theorem entsAtB_row :
    entsAtB #[0, 0, 1] tlToy shToy [{ ents := #[{ tree := 2, row := 1 }] }] = false := by
  decide +kernel

theorem entsAtB_digits :
    entsAtB #[0, 0, 1] tlToy shToy [{ ents := #[{ tree := 0, row := 0 }] }] = false := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tableAt_of_vectorB
#print axioms VerifiableInference.Desc.LinkJoin.entAt_of_B
#print axioms VerifiableInference.Desc.LinkJoin.entAt_at
#print axioms VerifiableInference.Desc.LinkJoin.entsAtB_yes
#print axioms VerifiableInference.Desc.LinkJoin.entsAtB_row
#print axioms VerifiableInference.Desc.LinkJoin.entsAtB_digits
