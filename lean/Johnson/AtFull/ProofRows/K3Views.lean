-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/ProofRows/K3Views.lean: THE ENTRY TESTS' ROWS ON THE LOOKUPS (`K3Asks.digRow`,
`readsRow`: Johnson/Desc/First/Look/K3Asks.lean) READ LITTLE OF A LOOKUP's PLACE AND OF THE
STRUCTURE OF A SEGMENT's APPROXIMATE RANGE PROOF: each test at a place and a structure is the same
test at these two NARROWED to the fields that it reads, everything else at its default. Six
definitions with code and seven theorems. No test is typed anew: the library's own definitions
stand on both sides.
Why. A place holds two ledgers with allocated rows, and the structure holds plans and tables: they
cannot be written down. What the tests read of them can. So a test that Lean's kernel is to decide
at written values stands at the narrowed terms.
  `narrowP x`: name, link, calls, pub, lid, ns, lm (what the kind's own parameters take of a
    place: `P.ofPlace`, Johnson/Desc/First/Look/LookKind.lean; the row itself does not read the
    name); of the ledger F its next slot; of the ledger base, array by array, the numbers of rows
    and columns. `narrowT tl`: tau, mz, the two calls with their pieces (z1, z2), f9, and the
    numbers of the two arrays ZZ and BZ.
  `narrowC x`, `narrowM tl`: for the row on attention's callers' reading: link, F's next slot,
    four numbers of fs (dT, rK, kT, cK); NM, gtTree, and of each matrix its rows and columns.
  `arrB_narrow`, `digAddrB_narrow`, `digB_narrow`: EQUATIONS at the digits. `digOne`: the test as
    `digRow` asks it at one segment, of a place and a structure; `digOne_narrow`; `digRow_of`:
    `digRow` says yes where at each segment a place and a structure are there and `digOne` says
    yes.
  `readsB_narrow`; `readsRow_of`: the like for `readsRow`.
Limits. NO VALUE IS GIVEN HERE. The third row (`headRow`) is not touched. No soundness is claimed.

-/
import Johnson.Desc.First.Look.K3AsksDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofRows.K3
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K3Asks
open VerifiableInference.Desc.First.Look (Place P lookAt tlAt)

/-! ## 1 The digits -/

/-- Of an array: its numbers of rows and columns. -/
def narrowTree (T : HTree) : HTree := { R := T.R, K := T.K }

/-- **What the digits' row reads of a place.** -/
def narrowP (x : Place) : Place :=
  { name := x.name, link := x.link, calls := x.calls, pub := x.pub, lid := x.lid,
    base := { trees := x.base.trees.map narrowTree }, F := { next := x.F.next }, fs := {},
    ns := x.ns, lm := x.lm }

/-- **What it reads of the structure of the segment's approximate range proof.** -/
def narrowT (tl : HTailF2) : HTailF2 :=
  { tau := tl.tau, mz := tl.mz, z1 := tl.z1, z2 := tl.z2, f9 := tl.f9,
    ix := { ZZ := tl.ix.ZZ, BZ := tl.ix.BZ } }

theorem arrB_narrow (trees : Array HTree) (D : Sent) (l : List OracleShape) (i t : Nat) :
    arrB (trees.map narrowTree) D l i t = arrB trees D l i t := by
  unfold arrB
  rw [Array.getElem?_map]
  cases trees[t]? <;> cases (D.arrayOf.getD i #[])[t]? <;> rfl

theorem digAddrB_narrow (x : Place) (tl : HTailF2) (D : Sent) (l : List OracleShape) :
    digAddrB (narrowP x) (narrowT tl) D l = digAddrB x tl D l := by
  unfold digAddrB
  show ((match (x.base.trees.map narrowTree)[tl.ix.ZZ]? with
      | some T => decide (tl.tau ≤ T.R) && decide (tl.mz + tl.mz ≤ T.K)
      | none => false) &&
    (match (x.base.trees.map narrowTree)[tl.ix.BZ]? with
      | some T => decide (2 ^ (tl.f9.kT + tl.f9.cK) ≤ T.K) &&
          decide (2 ^ tl.f9.kT * 2 ^ tl.f9.cK * 2 ^ 5 ≤ 2 ^ (tl.f9.kT + tl.f9.cK) * T.R)
      | none => false) &&
    arrB (x.base.trees.map narrowTree) D l x.link tl.ix.ZZ &&
    arrB (x.base.trees.map narrowTree) D l x.link tl.ix.BZ &&
    decide (x.F.next + Forest.elems tl.f9 ≤ x.ns) &&
    maskB D l x.link (x.F.next + Forest.elems tl.f9)) = _
  rw [arrB_narrow, arrB_narrow, Array.getElem?_map, Array.getElem?_map]
  cases x.base.trees[tl.ix.ZZ]? <;> cases x.base.trees[tl.ix.BZ]? <;> rfl

/-- **The digits' one test at a segment reads the narrowed terms alone.** -/
theorem digB_narrow (set : Params.Setting) (x : Place) (tl : HTailF2) (D : Sent) :
    digB set (narrowP x) (narrowT tl) D = digB set x tl D := by
  unfold digB
  rw [digAddrB_narrow]
  rfl

/-- The test as `digRow` asks it at one segment: the lookup's numbers laid anew as the kind's own
parameters make them. -/
def digOne (set : Params.Setting) (x : Place) (tl : HTailF2) (D : Sent) : Bool :=
  ((P.ofPlace set true x).shape.map fun h => (x, { tl with f9 := h })).any fun xt =>
    digB set xt.1 xt.2 D

theorem digOne_narrow (set : Params.Setting) (x : Place) (tl : HTailF2) (D : Sent) :
    digOne set (narrowP x) (narrowT tl) D = digOne set x tl D := by
  unfold digOne
  show (((P.ofPlace set true x).shape.map fun h =>
      (narrowP x, { narrowT tl with f9 := h })).any fun xt => digB set xt.1 xt.2 D) = _
  cases (P.ofPlace set true x).shape with
  | none => rfl
  | some h => exact digB_narrow set x { tl with f9 := h } D

/-- **`digRow` from the segments.** -/
theorem digRow_of {X : Verify.Public} {D : Sent} {n : Nat} (hn : linksOf X = n)
    (h : ∀ i < n, ∃ x tl, lookAt X i true = some x ∧ tlAt X i = some tl ∧
      digOne (Params.settingOf X.P.frame) x tl D = true) : digRow X D = true := by
  unfold digRow
  rw [hn, List.all_eq_true]
  intro i hi
  obtain ⟨x, tl, hx, ht, hd⟩ := h i (List.mem_range.1 hi)
  unfold digAt
  rw [hx, ht]
  exact hd

/-! ## 2 Attention's callers' reading -/

/-- What the row on attention's callers' reading reads of a place. -/
def narrowC (x : Place) : Place :=
  { name := "", link := x.link, calls := #[], pub := #[], lid := 0, base := {},
    F := { next := x.F.next },
    fs := { dT := x.fs.dT, rK := x.fs.rK, kT := x.fs.kT, cK := x.fs.cK }, ns := 0, lm := 0 }

/-- What it reads of the structure. -/
def narrowM (tl : HTailF2) : HTailF2 :=
  { NM := tl.NM, gtTree := tl.gtTree, mats := tl.mats.map fun M => { m := M.m, k := M.k } }

theorem readsB_narrow (x : Place) (tl : HTailF2) (D : Sent) :
    readsB (narrowC x) (narrowM tl) D = readsB x tl D := by
  unfold readsB seatsB
  have e : ∀ mu, symRowsAt (narrowM tl) mu = symRowsAt tl mu ∧
      colsAt (narrowM tl) mu = colsAt tl mu := by
    intro mu
    unfold symRowsAt colsAt narrowM
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases tl.mats[mu]? <;> exact ⟨rfl, rfl⟩
  simp only [(e _).1, (e _).2]
  rfl

/-- **`readsRow` from the segments.** -/
theorem readsRow_of {X : Verify.Public} {D : Sent}
    (h : ∀ i ∈ attLinks X, ∃ x tl, lookAt X i false = some x ∧ tlAt X i = some tl ∧
      readsB x tl D = true) : readsRow X D = true := by
  unfold readsRow
  rw [List.all_eq_true]
  intro i hi
  obtain ⟨x, tl, hx, ht, hd⟩ := h i hi
  rw [hx, ht]
  exact hd

end Johnson.AtFull.ProofRows.K3

#print axioms Johnson.AtFull.ProofRows.K3.arrB_narrow
#print axioms Johnson.AtFull.ProofRows.K3.digAddrB_narrow
#print axioms Johnson.AtFull.ProofRows.K3.digB_narrow
#print axioms Johnson.AtFull.ProofRows.K3.digOne_narrow
#print axioms Johnson.AtFull.ProofRows.K3.digRow_of
#print axioms Johnson.AtFull.ProofRows.K3.readsB_narrow
#print axioms Johnson.AtFull.ProofRows.K3.readsRow_of
