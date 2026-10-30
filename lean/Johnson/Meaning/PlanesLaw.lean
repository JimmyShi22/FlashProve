-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/PlanesLaw.lean: what the lookup on the planes of its counts asks of a caller, and
one law that proves it, under the law of the reads, for each caller reading the planes by its reads.

The lookup's three claims on the planes of its counts' bits speak of values that the calling kind
hands in: for each column of the planes' matrix a form at the leaves' point, a form at the bits'
point and a form for the counts. The claims mean what they should if each form is worth that
column's combination of the matrix's cells. A caller of the verifier reads a column through a table
in its vector of reads. So the condition is met wherever the entries of virtual rows meet the law of
the reads (Fo.ReadsAll, OnBytes/Tie/Pv/Lookup/Ends/FoKeys.lean).

Main names (namespace `Meaning.Planes`).
  `K3HostPlanes`: the condition: three clauses, with the right sides of the library's cols_of_reads
      (OnBytes/Tie/Pv/Lookup/Port/FoReads.lean): colsK at the two points, pinColK.
  `K3HostPlanesUnderReads`: these three for all cells, and all entries of virtual rows that meet
      the law of the reads at these cells.
  `ReadersAre`: the caller's form for a column is the entry of the vector of reads at the table's
      first entry plus the column, for each of the three tables and every column of the planes.
  `host_planes_of_readsLaw`: ReadersAre and Fo.ReadsLaw give the condition.
  `host_planes`: **THE LAW FOR ALL CALLERS**: three tables of the planes among the caller's tables
      (Fo.PlaneTab, Ends/FoReadsIn.lean), ReadersAre and the law of the reads give the condition.
  `host_planes_underReads`: the same as K3HostPlanesUnderReads.
  `readOf`, `madeRead`, `reads_meet`: for all cells of the matrices there are entries that meet the
      law of the reads, if no entry of the vector of reads lies in two tables.

What a caller brings: which matrix holds the planes, lm, its list of tables, the array and the width
of its vector of reads (all in Fo.PlaneTab and the letters iU3, K3); that its reader returns, at
every column of the planes, the entry named (ReadersAre: a premise, not an "if and only if" with a
table's length).
Limits. THE LAW OF THE READS IS A PREMISE. That the three clauses are what the lookup's own law on
its claims asks of a caller is not shown here: no theorem of this file names that law. Ties in one
world: no draw, no error term, nothing on soundness. What is asked of a caller's key forms is not
treated.
-/
import OnBytes.Tie.Pv.Lookup.Ends.FoReadsIn
import OnBytes.Tie.Pv.Lookup.Forest.FoNumsEq
import OnBytes.Tie.Pv.Lookup.Forest.FoPlaneRows
import OnBytes.Tie.Pv.Lookup.Forest.FoPin
import OnBytes.Tie.Pv.Lookup.Port.FoReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Planes
open Finset
open Cb Cb.Fo Cb.Fo.NumsEq TwV
open OnBytes OnBytes.Model Fo
open Cb.Fo.Pin

/-- What is asked of a caller on the forms that read the planes' matrix. h, lm: the shape; the
matrix has 2 ^ lm rows. zb0, zb1: the leaves' point and the bits' point. ν: the reading of the
places. val: the value of a form. bit e col, pin col: the forms. -/
structure K3HostPlanes {K : Type} [CommRing K] (h : FoNums.Sh) (lm : ℕ) (zb0 zb1 : List K)
    (ν : _root_.Fo.Pl → K) (val : Aff → K) (bit : ℕ → ℕ → Aff) (pin : ℕ → Aff) : Prop where
  bit0 : ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) → val (bit 0 col) = colsK h lm zb0 ν col
  bit1 : ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) → val (bit 1 col) = colsK h lm zb1 ν col
  pin : ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) → val (pin col) = pinColK lm ν col

/-- The three clauses, for all cells and all entries that meet the law of the reads at the tables
funs. H: the ledger at which the claims are judged. mk, pl: where a mask entry and a cell of the
planes' matrix lie among the caller's entries. cm m r c: where cell (r, c) of matrix m lies. An
entry of the vector of reads needs no place among the caller's entries. -/
def K3HostPlanesUnderReads {K J₀ : Type} [CommRing K] (ρ : Reading K) (H : Fork)
    (h : FoNums.Sh) (lm : ℕ) (zb0 zb1 : List K) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀)
    (mats : Array TMat) (funs : Array HFun) (iU3 K3 : ℕ)
    (cm : ℕ → ℕ → ℕ → J₀) (bit : ℕ → ℕ → Aff) (pin : ℕ → Aff) : Prop :=
  ∀ (μ₀ : J₀ → K) (entry : ℕ → ℕ → ℕ → K),
    ReadsAll ρ mats funs entry iU3 K3 (fun m r c => μ₀ (cm m r c)) →
    K3HostPlanes h lm zb0 zb1 (fun p => zext μ₀ (placeOf mk pl p))
      (fun f => f.value ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry)) bit pin

/-- The caller's readers of the planes' columns: at every column of the planes the form is the entry
of the vector of reads at the table's first entry plus the column. tB0, tB1, tP: the first entries
of the three tables. iU3, K3: the array of the reads and its width. -/
structure ReadersAre (h : FoNums.Sh) (lm iU3 K3 tB0 tB1 tP : ℕ) (bit : ℕ → ℕ → Aff)
    (pin : ℕ → Aff) : Prop where
  bit0 : ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) → bit 0 col = u3Form iU3 K3 (tB0 + col)
  bit1 : ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) → bit 1 col = u3Form iU3 K3 (tB1 + col)
  pin : ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) → pin col = u3Form iU3 K3 (tP + col)

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- From the law of the reads at the planes' three tables. -/
theorem host_planes_of_readsLaw {h : FoNums.Sh} {lm iU3 K3 tB0 tB1 tP : ℕ} {bit : ℕ → ℕ → Aff}
    {pin : ℕ → Aff} (R : ReadersAre h lm iU3 K3 tB0 tB1 tP bit pin) {zb0 zb1 : List K}
    {ν : _root_.Fo.Pl → K} (W : World K)
    (Lw : ReadsLaw h lm zb0 zb1 ν W.entry iU3 K3 tB0 tB1 tP) :
    K3HostPlanes h lm zb0 zb1 ν (fun f => f.value ρ W) bit pin := by
  refine ⟨fun col hc => ?_, fun col hc => ?_, fun col hc => ?_⟩
  · show (bit 0 col).value ρ W = _
    rw [R.bit0 col hc, u3Form_value]
    exact Lw.bits0 col hc
  · show (bit 1 col).value ρ W = _
    rw [R.bit1 col hc, u3Form_value]
    exact Lw.bits1 col hc
  · show (pin col).value ρ W = _
    rw [R.pin col hc, u3Form_value]
    exact Lw.count col hc

/-- **The law for all callers.** -/
theorem host_planes {mats : Array TMat} {funs : Array HFun} {cellM : ℕ → ℕ → ℕ → K}
    {h : FoNums.Sh} {lm iU3 K3 tB0 tB1 tP : ℕ} {zb0 zb1 : List K} {ν : _root_.Fo.Pl → K}
    {f0 f1 fP : HFun}
    (T0 : PlaneTab ρ mats funs cellM f0 tB0 (fun r => (phiBK h lm zb0).getD r 0) h lm ν)
    (T1 : PlaneTab ρ mats funs cellM f1 tB1 (fun r => (phiBK h lm zb1).getD r 0) h lm ν)
    (TP : PlaneTab ρ mats funs cellM fP tP (fun r => (2 : K) ^ (r % 32)) h lm ν)
    {bit : ℕ → ℕ → Aff} {pin : ℕ → Aff} (R : ReadersAre h lm iU3 K3 tB0 tB1 tP bit pin)
    (W : World K) (hA : ReadsAll ρ mats funs W.entry iU3 K3 cellM) :
    K3HostPlanes h lm zb0 zb1 ν (fun f => f.value ρ W) bit pin :=
  host_planes_of_readsLaw ρ R W (readsLaw_of_readsAll ρ hA T0 T1 TP)

/-- The same for all cells and all entries that meet the law of the reads. The three tables are
asked at every μ₀: of their eight clauses the last alone reads μ₀ (the cells of the table's matrix
are the lookup's). -/
theorem host_planes_underReads {J₀ : Type} {mats : Array TMat} {funs : Array HFun}
    {h : FoNums.Sh} {lm iU3 K3 tB0 tB1 tP : ℕ} {zb0 zb1 : List K} {f0 f1 fP : HFun}
    (H : Fork) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀) (cm : ℕ → ℕ → ℕ → J₀)
    (T0 : ∀ μ₀ : J₀ → K, PlaneTab ρ mats funs (fun m r c => μ₀ (cm m r c)) f0 tB0
      (fun r => (phiBK h lm zb0).getD r 0) h lm (fun p => zext μ₀ (placeOf mk pl p)))
    (T1 : ∀ μ₀ : J₀ → K, PlaneTab ρ mats funs (fun m r c => μ₀ (cm m r c)) f1 tB1
      (fun r => (phiBK h lm zb1).getD r 0) h lm (fun p => zext μ₀ (placeOf mk pl p)))
    (TP : ∀ μ₀ : J₀ → K, PlaneTab ρ mats funs (fun m r c => μ₀ (cm m r c)) fP tP
      (fun r => (2 : K) ^ (r % 32)) h lm (fun p => zext μ₀ (placeOf mk pl p)))
    {bit : ℕ → ℕ → Aff} {pin : ℕ → Aff} (R : ReadersAre h lm iU3 K3 tB0 tB1 tP bit pin) :
    K3HostPlanesUnderReads ρ H h lm zb0 zb1 mk pl mats funs iU3 K3 cm bit pin :=
  fun μ₀ entry hA =>
    host_planes ρ (T0 μ₀) (T1 μ₀) (TP μ₀) R (H.worldOf ρ (fun j => μ₀ (mk j)) entry) hA

end

/-! ## The law of the reads can be met -/

/-- How many stretches of len rows a column of the table's matrix has. -/
def stretches (mats : Array TMat) (f : HFun) : ℕ := (mats.getD f.mat {}).m / f.len

/-- The number of a table's entries. -/
def entriesOf (mats : Array TMat) (f : HFun) : ℕ := (mats.getD f.mat {}).k * stretches mats f

variable {K : Type} [CommRing K]

/-- What the law of the reads asks at entry col of the table f, at the cells cellM. -/
def readOf (ρ : Reading K) (mats : Array TMat) (cellM : ℕ → ℕ → ℕ → K) (f : HFun) (col : ℕ) : K :=
  ∑ row ∈ range f.len, ρ.val (f.phi.getD row zeroE) *
    cellM f.mat (col % stretches mats f * f.len + row) (col / stretches mats f)

open Classical in
/-- Entry i of the made vector of reads: what the law asks, where i lies in a table; else 0. -/
noncomputable def madeRead (ρ : Reading K) (mats : Array TMat) (funs : Array HFun)
    (cellM : ℕ → ℕ → ℕ → K) (i : ℕ) : K :=
  if h : ∃ x : HFun × ℕ, x.1 ∈ funs.toList ∧ x.2 < entriesOf mats x.1 ∧ i = x.1.start + x.2
  then readOf ρ mats cellM (choose h).1 (choose h).2 else 0

theorem madeRead_at {ρ : Reading K} {mats : Array TMat} {funs : Array HFun}
    (apart : ∀ f ∈ funs.toList, ∀ f' ∈ funs.toList, ∀ col < entriesOf mats f,
      ∀ col' < entriesOf mats f', f.start + col = f'.start + col' → f = f')
    (cellM : ℕ → ℕ → ℕ → K) {f : HFun} (hf : f ∈ funs.toList) {col : ℕ}
    (hc : col < entriesOf mats f) :
    madeRead ρ mats funs cellM (f.start + col) = readOf ρ mats cellM f col := by
  have h : ∃ x : HFun × ℕ, x.1 ∈ funs.toList ∧ x.2 < entriesOf mats x.1 ∧
      f.start + col = x.1.start + x.2 := ⟨(f, col), hf, hc, rfl⟩
  unfold madeRead
  rw [dif_pos h]
  obtain ⟨a1, a3, a4⟩ := Classical.choose_spec h
  have e1 : f = (Classical.choose h).1 := apart f hf _ a1 col hc _ a3 a4
  have e2 : col = (Classical.choose h).2 := by
    rw [← e1] at a4
    exact Nat.add_left_cancel a4
  rw [← e1, ← e2]

/-- **The law of the reads is met, at any cells of the matrices**, if no entry of the vector of
reads lies in two tables. Entry number e is laid in virtual row e / K3 at index e % K3, as u3Val
reads it: where a table runs past K3 the made reads lie in further virtual rows, whether or not a
ledger has such rows. -/
theorem reads_meet (ρ : Reading K) (mats : Array TMat) (funs : Array HFun) (iU3 K3 : ℕ)
    (apart : ∀ f ∈ funs.toList, ∀ f' ∈ funs.toList, ∀ col < entriesOf mats f,
      ∀ col' < entriesOf mats f', f.start + col = f'.start + col' → f = f')
    (cellM : ℕ → ℕ → ℕ → K) :
    ∃ entry : ℕ → ℕ → ℕ → K, ReadsAll ρ mats funs entry iU3 K3 cellM := by
  refine ⟨fun _ r x => madeRead ρ mats funs cellM (r * K3 + x), ?_⟩
  intro f hf _ col hcol
  have hc : col < entriesOf mats f := hcol
  unfold u3Val
  show madeRead ρ mats funs cellM ((f.start + col) / K3 * K3 + (f.start + col) % K3) = _
  rw [Nat.div_add_mod', madeRead_at apart cellM hf hc]
  rfl

#print axioms host_planes_of_readsLaw
#print axioms host_planes
#print axioms host_planes_underReads
#print axioms reads_meet

end Meaning.Planes
