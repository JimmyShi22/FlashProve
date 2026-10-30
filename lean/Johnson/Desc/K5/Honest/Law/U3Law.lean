-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/U3Law.lean: CONDITIONAL, under seven premises of which none is shown
here: the honest prover's array of an attention segment's tables (`u3Att`,
Johnson/Desc/K5/Honest/U3.lean), read in a field, is entry by entry the stated function of the
committed matrices' cells that the verifier's side speaks of (`uAtt A (funsAt A)`,
Johnson/Desc/First/Att/K05WorldTieAt.lean).

Both sides sum a column's cells in a run of rows under a table's weights. The honest side finds
the table by walking the list for the stretch in which the entry's number lies; the stated
function picks a table, a column and a run whose place (`tabAt`, OnBytes/Model/Tail.lean) is the
entry's number. Where the verifier's text `tablesP` returns, its tables tile the numbers below the
array's length and no two name one number, so the two agree.

Main names:
  `U3Law.elems_sz`, `U3Law.blocks_n`: the honest side's two counts are the library's.
  `U3Law.lay_fits`: every table of a laying whose tables fit the list of matrices fits it.
  `u3Of_reads`: at any list that `tablesP` returns, any reading rho in a field and any matrices M
    that the honest cells read as: rho (u3Of .. n) = entryOf rho tl K3 M .. (n / K3) (n % K3), for
    each n below the array's length and every number K3 of columns.
  `PointsSame g lk p0 p`: a NAMED PREMISE: the two lists of points give every table the same
    matrix, run of rows, weights and number of entries.
  `CellsSame rho tl cell M`: a NAMED PREMISE: inside each matrix the honest cell reads as M's.
  `u3Att_reads`: **the honest array reads as the stated function**, at the entry's row and column.

Limits. `u3Att_reads` is conditional on seven things, none of which is shown here: the two named
premises; that the honest side's function returns; that the verifier's text returns at the
verifier's points, AT THE SAME VALUE lk OF WHAT THE LOOKUP LEFT AS THE HONEST SIDE's (one letter
stands in both: that the honest side makes its array at that value is a tie of its own); that the
list of tables which the verifier's side reads at the state is that return's (hf); that the
smallness test's number of matrices is the length of its list; that the honest side's numbers are
the plan's.
AT WHICH STATES hf CAN HOLD: the verifier's side reads its list off the state, and reads the empty
list wherever its reading returns nothing; there hf is false and the theorem says nothing. The
reading returns at a state at which an attention segment is open, what the lookup returned and
what the segment's own rounds heard are laid, the rows that the sumchecks leave can be read off the
open ledger, AND THE ARRAY OF THE TABLES STANDS IN THAT LEDGER (the last premise of
`K5Law.funsAt_is`, Johnson/Desc/First/Att/Claims/FunsAt.lean).
Nothing is said of entries from the array's length on, of what is committed, or of what is sent.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.U3
import Johnson.Desc.K5.Honest.Law.Read
import Johnson.Desc.First.Att.K05StatedArm
import Johnson.Desc.First.Att.Claims.TablesTile

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model
open OnBytes.Road (Mats)
open VerifiableInference.Desc (First.S)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ matsOfData)

namespace U3Law

/-- The honest side's number of a table's entries is the library's. -/
theorem elems_sz (mats : Array (ℕ × ℕ)) (F : P.Fun1) : elemsOf mats F = K5Law.szOf mats F := by
  unfold elemsOf blocksOf K5Law.szOf
  rw [Array.getD_eq_getD_getElem?]
  cases mats[F.mat]? with
  | none => exact Nat.zero_mul _
  | some M => rfl

/-- A matrix's rows and columns, read off the list of pairs. -/
theorem matsOf_getD (mats : Array TMat) (i : ℕ) :
    (K5Law.matsOf mats).getD i (0, 0) = ((mats.getD i {}).m, (mats.getD i {}).k) := by
  unfold K5Law.matsOf
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases mats[i]? <;> rfl

/-- The honest side's number of runs in a column is the library's. -/
theorem blocks_n (tl : HTailF2) (F : P.Fun1) :
    blocksOf (K5Law.matsOf tl.mats) F = K5Law.nOf tl F := by
  unfold blocksOf K5Law.nOf
  rw [matsOf_getD]

/-- Every table of a laying whose tables fit the list of matrices fits it. -/
theorem lay_fits {mats : Array (ℕ × ℕ)} : ∀ (L : List K5Law.Table) (m : ℕ),
    L.all (K5Law.fitsT mats) = true →
      ∀ f ∈ K5Law.layFrom m L, ∃ e, P.fits mats f.mat f.len e = true
  | [], _, _, f, hf => by cases hf
  | t :: L, m, hL, f, hf => by
    rw [List.all_cons, Bool.and_eq_true] at hL
    rcases List.mem_cons.1 hf with rfl | hf
    · exact ⟨t.entries, hL.1⟩
    · exact lay_fits L _ hL.2 f hf

end U3Law

open U3Law

/-- A NAMED PREMISE: inside each matrix of the smallness test's list the honest cell reads as the
matrices' M. Whoever ties the honest witness to the committed data pays it. Where M is read off
committed data (`matsOfData`), two things stand between: the data holds symbols that pack several
cells, so the tie goes through the packing; and a matrix whose array the open link does not name
reads as 0 there, so the premise can be met only at a state whose link names every matrix's array
(the smallness test's guard of order asks that). No lemma is known that shows it outright; in form
it is two named premises on a chain's invariant, taken together. -/
def CellsSame {K : Type} [CommRing K] (ρ : Reading K) (tl : HTailF2) (cell : ℕ → ℕ → ℕ → E)
    (M : Mats K) : Prop :=
  ∀ a r c, r < (tl.mats.getD a {}).m → c < (tl.mats.getD a {}).k → ρ.val (cell a r c) = M a r c

/-- **An entry of the honest array, read, is the stated sum at the entry's row and column**, at
any list of tables that the verifier's text returns. Conditional: hNM: the smallness test's number
of matrices is the length of its list (the plan's maker pays it); ht: the return; hc: the cells;
hn: the entry lies in the array. K3, the number of columns of the array's rows, is free. -/
theorem u3Of_reads {K : Type} [Field K] (ρ : Reading K) (tl : HTailF2)
    (hNM : tl.NM = tl.mats.size) {g : P.Geo} {nW : ℕ} {lk : P.LookIn} {p : P.Pts} {t : P.TablesP}
    (ht : P.tablesP g (K5Law.matsOf tl.mats) nW lk p = some t) (cell : ℕ → ℕ → ℕ → E)
    (M : Mats K) (hc : CellsSame ρ tl cell M) (K3 n : ℕ) (hn : n < nW) :
    ρ.val (u3Of (K5Law.matsOf tl.mats) cell t.funs n) =
      K5Law.entryOf ρ tl K3 M (t.funs.toList.map K5Law.funBack) 0 (n / K3) (n % K3) := by
  obtain ⟨f, hf, a, b, _⟩ := K5Law.lay_cover (K5Law.laidBy g lk p) 0 (K5Law.tablesP_fits ht) n
    (Nat.zero_le _) (by rw [K5Law.total_is_nW ht, Nat.zero_add]; exact hn)
  rw [← K5Law.tablesP_laid ht] at hf
  unfold u3Of
  rw [← Array.find?_toList]
  cases hfind : t.funs.toList.find? (fun F =>
      decide (F.start ≤ n) && decide (n < F.start + elemsOf (K5Law.matsOf tl.mats) F)) with
  | none =>
    exfalso
    have := List.find?_eq_none.1 hfind f hf
    rw [elems_sz] at this
    simp [a, b] at this
  | some F =>
    have hp := List.find?_some hfind
    have hF := List.mem_of_find?_eq_some hfind
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, elems_sz] at hp
    have hF' := hF
    rw [K5Law.tablesP_laid ht] at hF'
    obtain ⟨e, he⟩ := lay_fits _ 0 (K5Law.tablesP_fits ht) F hF'
    have hpos := K5Law.tabAt_cover rfl hNM he hp.1 hp.2
    have hsum := K5Law.holds_entryOf ρ tl 0 K3 M (t.funs.toList.map K5Law.funBack)
      (K5Law.apart_tablesP ht) {} (fun _ => 0) (K5Law.funBack F) (List.mem_map_of_mem hF) _ _ _ hpos
    obtain ⟨hsg, _, _, _⟩ := K5Law.tabAt_in rfl hpos
    have hcol : (n - F.start) / K5Law.nOf tl F < (tl.mats.getD F.mat {}).k := by
      have h2 := hp.2
      rw [← elems_sz] at h2
      unfold elemsOf at h2
      rw [blocks_n, matsOf_getD] at h2
      have h3 : n < F.start + (tl.mats.getD F.mat {}).k * K5Law.nOf tl F := h2
      have h1 := hp.1
      apply Nat.div_lt_of_lt_mul
      rw [Nat.mul_comm]
      omega
    refine Eq.trans ?_ hsum.symm
    show ρ.val (entryOf (K5Law.matsOf tl.mats) cell F (n - F.start)) = _
    unfold entryOf
    simp only
    rw [read_sumTo, blocks_n]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [ρ.mul]
    congr 1
    refine hc _ _ _ ?_ hcol
    have hj' : j < F.len := Finset.mem_range.1 hj
    have h1 : ((n - F.start) % K5Law.nOf tl F + 1) * F.len ≤ K5Law.nOf tl F * F.len :=
      Nat.mul_le_mul_right _ hsg
    have h2 : K5Law.nOf tl F * F.len ≤ (tl.mats.getD F.mat {}).m := Nat.div_mul_le_self _ _
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega

/-- A NAMED PREMISE: the two lists of points give every table of the segment the same matrix, run
of rows, weights and number of entries. It asks less than that the two are one: the numbers of
hidden values and the forms that a list of points also holds are not read. The weights are
compared word for word, not as read in a field: so it can be met only where the honest side's key
points and challenges are, word for word, those that the verifier heard. Whoever shows that the
honest side's laying of the challenges yields the verifier's points pays it. -/
def PointsSame (g : P.Geo) (lk : P.LookIn) (p₀ p : P.Pts) : Prop :=
  K5Law.laidBy g lk p₀ = K5Law.laidBy g lk p

/-- Under `PointsSame` two returns of the verifier's text hold one list of tables. -/
theorem funs_same {g : P.Geo} {mats : Array (ℕ × ℕ)} {nW : ℕ} {lk : P.LookIn} {p₀ p : P.Pts}
    {t₀ t : P.TablesP} (h : PointsSame g lk p₀ p) (h₀ : P.tablesP g mats nW lk p₀ = some t₀)
    (h₁ : P.tablesP g mats nW lk p = some t) : t₀.funs = t.funs := by
  apply Array.toList_inj.1
  rw [K5Law.tablesP_laid h₀, K5Law.tablesP_laid h₁, h]

/-- **The honest array of an attention segment's tables, read, is the stated function of the
committed cells**, at row n / K and column n % K of the array, K the planned number of columns.
Conditional:
  hg: the honest side's numbers are the plan's shape's (the caller pays it);
  hu: the honest side's functions return;
  ht: the verifier's text returns t at the verifier's points p;
  hP: `PointsSame` (named above);
  hf: the list of tables that the verifier's side reads at the state s is t's (paid by
    `K5Law.funsAt_is`, Johnson/Desc/First/Att/Claims/FunsAt.lean, under its own premises, among
    them that the array of the tables stands in the state's open ledger);
  hNM: the smallness test's number of matrices is the length of its list;
  hc: `CellsSame` (named above), at the matrices read off the committed data Dt. -/
theorem u3Att_reads (A : Attention.Plan) (Pb : Pub5) (c : Chal) (cell : ℕ → ℕ → ℕ → E)
    (lk : P.LookIn) {u : ℕ → E} (hg : Pb.g = P.geoOf A.S)
    (hu : u3Att Pb (P.parCOf A).mats A.nW cell lk c = some u) {p : P.Pts} {t : P.TablesP}
    (ht : P.tablesP (P.geoOf A.S) (P.parCOf A).mats A.nW lk p = some t)
    (hP : ∀ p₀, ptsOf Pb c = some p₀ → PointsSame (P.geoOf A.S) lk p₀ p)
    {s : First.S} (hf : K5Law.funsAt A s = (K5Law.tabBack t).funs.toList)
    (hNM : A.seam.tl.NM = A.seam.tl.mats.size) (Dt : Bound GQ) (cN : ℕ × String)
    (hc : CellsSame Reading.gl A.seam.tl cell
      (matsOfData A.seam.tl ((s.link?.map (·.arrayOf)).getD #[]) Dt)) :
    ∀ n < A.nW, Reading.gl.val (u n) =
      P.uAtt A (K5Law.funsAt A) s Dt cN (n / P.plannedK A) (n % P.plannedK A) := by
  intro n hn
  unfold u3Att at hu
  obtain ⟨p₀, hp₀, hu⟩ := Option.bind_eq_some_iff.1 hu
  obtain ⟨t₀, ht₀, rfl⟩ := Option.map_eq_some_iff.1 hu
  rw [hg] at ht₀
  rw [funs_same (hP p₀ hp₀) ht₀ ht]
  unfold P.uAtt
  rw [hf]
  have e : (K5Law.tabBack t).funs.toList = t.funs.toList.map K5Law.funBack := Array.toList_map
  rw [e]
  exact u3Of_reads Reading.gl A.seam.tl hNM ht cell _ hc _ n hn

end H2K5.Honest

#print axioms H2K5.Honest.U3Law.elems_sz
#print axioms H2K5.Honest.U3Law.matsOf_getD
#print axioms H2K5.Honest.U3Law.blocks_n
#print axioms H2K5.Honest.U3Law.lay_fits
#print axioms H2K5.Honest.u3Of_reads
#print axioms H2K5.Honest.funs_same
#print axioms H2K5.Honest.u3Att_reads
