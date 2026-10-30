-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/PackedTie.lean

The first two clauses of the smallness test's "tie" (K8.TieOf, Johnson/Desc/First/K8/LawItems.lean),
typed with the integers as a letter, and what a trace T gives of each.

K8.TieOf tl A says that there are integers a, one for each cell of each matrix of tl's list, with
three properties. Here the first two are typed with a as a letter ("SmallBy", "PackedBy"; that with
the third they are that definition is tieOf_iff, Johnson/HonestTrace/PackedJoins.lean), and taken at
a := cellsAtOf (cellsC X T) (matsOf X k) (Johnson/HonestTrace/DigitsAtTrace.lean), the cells of
sub-proof k as the smallness test's prover side reads them. There the first is shown, at every tl.
The second is shown only of a table A that is assumed to hold packedPlan tl (T k) (ReadsPacked):
that premise is the clause itself at a := T k.

Main definitions: "SmallBy tl a", "PackedBy tl A a" (the two clauses) · "packedPlan tl a μ i' c"
(the packed array of matrix number μ at tl's own rows of cells: pack3 of
Johnson/HonestTrace/Packed.lean, in the base field) · "ReadsPacked tl A a" (the table A holds
packedPlan at each matrix's symbol array tl.gtTree μ, inside the packed shape).

Main theorems:
* "pack_radb": at columns of integers the library's Alg.pack at the radix radb is pack3: radb is
  2^20.
* "packedBy_iff": PackedBy tl A a holds exactly if ReadsPacked tl A a.
* "packedPlan_eq_packedOf": where S's rows of matrix μ of segment l are tl's, at a column below S's
  columns: packedPlan tl (T l) μ is packedOf S T l μ.
* "cellsAtOf_eq": under NamesFit and MeetsAll, for k < 25: cellsAtOf (cellsC X T) (matsOf X k) = T
  k.
* "smallBy_trace", "packedBy_trace": under the same, at every tl: SmallBy at these cells; and
  PackedBy at them for every table A with ReadsPacked tl A (T k).
* "packedOf_owner": under the same, for a segment of the proof: packedOf Sz.ref T at a matrix of its
  list is packedOf Sz.ref T at the owner's numbers; both are terms of T.

Limits. Like Johnson/HonestTrace/DigitsAtTrace.lean this file can be built only where the files
under Johnson/Desc/K8/Honest/ and Johnson/Desc/ProofFile/Honest/ lie. ReadsPacked is a premise, and
by packedBy_iff it is the clause itself in other letters: what packedBy_trace adds to it is
cellsAtOf_eq. That a prover's arrays are these is not said here, nor that one table A can meet
ReadsPacked at all matrices (two matrices with one number in tl.gtTree would have to have one
packing wherever both shapes reach, since the columns count from 0). No theorem of this file starts
from packedOf or packedCells at all matrices of a list (Johnson/HonestTrace/PackedJoins.lean has
one, under a premise on shapes). At a borrowed matrix the clause asks the packing of the sub-proof's
own list. packedOf_owner is an equation between two values of packedOf Sz.ref; it is not joined here
with packedPlan, and that a sub-proof's table holds at tl.gtTree μ the array that the owner
committed is not said here. A row of cells from the matrix's rows on counts as 0 in both packings.
packedPlan packs at tl's rows, packedOf at S's: they are compared only where these agree. The third
clause of K8.TieOf, on the tables of reads, is not treated here.

Not claimed: K8.TieOf; that a verifier accepts; anything on a prover's program.

-/
import Johnson.HonestTrace.DigitsAtTrace
import Johnson.HonestTrace.Packed
import Johnson.Desc.First.K8.LawItems

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Road
open OnBytes.Model (HTailF2 radb lbz)
open ProofFile.Honest.K8 (cellsAtOf)

/-! ## The clause, with the integers as a letter -/

/-- The first clause of K8.TieOf (Johnson/Desc/First/K8/LawItems.lean), at the integers a: inside
each matrix's shape a is below twice the shift 2^17 in absolute value. -/
def SmallBy (tl : HTailF2) (a : ℕ → ℕ → ℕ → ℤ) : Prop :=
  ∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k → ∀ i, i < (tl.mats.getD μ {}).m →
    |a μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)

/-- The second clause of K8.TieOf, at the integers a: the cells of the symbol arrays in the table A
are the packing of a. -/
def PackedBy (tl : HTailF2) (A : ℕ → ℕ → ℕ → Cb.Gl.E) (a : ℕ → ℕ → ℕ → ℤ) : Prop :=
  ∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
    ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
      A (tl.gtTree.getD μ 0) i' c =
        ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => a μ i c) i' : ℤ) :
          Cb.Gl.E)

/-- The packed array of matrix number μ of tl's list, at tl's own rows of cells, of the integers a:
entry (i', c), in the base field. -/
def packedPlan (tl : HTailF2) (a : ℕ → ℕ → ℕ → ℤ) (μ i' c : ℕ) : Cb.Gl.F :=
  ((pack3 (tl.mats.getD μ {}).m (fun r => a μ r c) i' : ℤ) : Cb.Gl.F)

/-- The table A holds, at each matrix's symbol array and inside its packed shape, packedPlan of a.
-/
def ReadsPacked (tl : HTailF2) (A : ℕ → ℕ → ℕ → Cb.Gl.E) (a : ℕ → ℕ → ℕ → ℤ) : Prop :=
  ∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
    ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
      A (tl.gtTree.getD μ 0) i' c = algebraMap Cb.Gl.F Cb.Gl.E (packedPlan tl a μ i' c)

/-- The library's packing at the radix radb is pack3. -/
theorem pack_radb (m : ℕ) (col : ℕ → ℤ) (i' : ℕ) :
    Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin m => col i) i' = pack3 m col i' := by
  rw [pack3_eq_pack]
  rfl

/-- PackedBy tl A a holds exactly if the table A holds packedPlan tl a (ReadsPacked). -/
theorem packedBy_iff (tl : HTailF2) (A : ℕ → ℕ → ℕ → Cb.Gl.E) (a : ℕ → ℕ → ℕ → ℤ) :
    PackedBy tl A a ↔ ReadsPacked tl A a := by
  unfold PackedBy ReadsPacked packedPlan
  refine forall_congr' fun μ => forall_congr' fun _ => forall_congr' fun c => forall_congr' fun _ =>
    forall_congr' fun i' => forall_congr' fun _ => ?_
  rw [map_intCast, pack_radb _ (fun r => a μ r c) i']

/-- If S's rows of matrix number μ of segment number l are tl's rows of matrix number μ: at a column
below S's columns, packedPlan tl (T l) μ is packedOf S T l μ. -/
theorem packedPlan_eq_packedOf (tl : HTailF2) (S : Sz) (T : ℕ → ℕ → ℕ → ℕ → ℤ) (l μ : ℕ)
    (hm : (S.shapeNo l μ).1 = (tl.mats.getD μ {}).m) {c : ℕ} (hc : c < (S.shapeNo l μ).2)
    (i' : ℕ) : packedPlan tl (T l) μ i' c = packedOf S T l μ i' c := by
  unfold packedPlan packedOf
  rw [if_pos hc, hm]

variable {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- Under NamesFit and MeetsAll, for k < 25: the cells read through matsOf X k are the list T k, as
functions of number, row and column. -/
theorem cellsAtOf_eq (N : NamesFit X T) (M : MeetsAll X i x T) {k : ℕ} (hk : k < 25) :
    cellsAtOf (cellsC X T) (matsOf X k) = T k := by
  funext mu r c
  exact cellsAtOf_matsOf N M hk mu r c

/-- Under NamesFit and MeetsAll, for k < 25, at every tl: SmallBy at the cells read through matsOf X
k. -/
theorem smallBy_trace (N : NamesFit X T) (M : MeetsAll X i x T) {k : ℕ} (hk : k < 25)
    (tl : HTailF2) : SmallBy tl (cellsAtOf (cellsC X T) (matsOf X k)) := by
  rw [cellsAtOf_eq N M hk]
  intro μ _ c _ r _
  have h := M.small k μ r c
  have e : ((2 ^ lbz : ℕ) : ℤ) = 131072 := rfl
  rw [e]
  omega

/-- Under NamesFit and MeetsAll, for k < 25, at every tl: if the table A holds packedPlan tl (T k),
PackedBy holds at the cells read through matsOf X k. -/
theorem packedBy_trace (N : NamesFit X T) (M : MeetsAll X i x T) {k : ℕ} (hk : k < 25)
    (tl : HTailF2) (A : ℕ → ℕ → ℕ → Cb.Gl.E) (hA : ReadsPacked tl A (T k)) :
    PackedBy tl A (cellsAtOf (cellsC X T) (matsOf X k)) := by
  rw [cellsAtOf_eq N M hk]
  exact (packedBy_iff tl A (T k)).2 hA

/-- Under NamesFit and MeetsAll, for a segment σ of the proof and member number mu of its list: the
owner has a number a for the matrix, and packedOf Sz.ref T at σ's number and mu is packedOf Sz.ref T
at the owner's number and a, at every row and column. -/
theorem packedOf_owner (N : NamesFit X T) (M : MeetsAll X i x T) {σ : Seg} (hσ : σ.Below 12)
    {mu : ℕ} {μ : MatName} (hμ : (MatName.all 3 1 1 4 σ)[mu]? = some μ) :
    ∃ a, MatName.no? 3 1 1 4 (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2 = some a ∧
      ∀ i' c, packedOf Sz.ref T (σ.no 12) mu i' c =
        packedOf Sz.ref T ((Sz.ref.owner σ μ).1.no 12) a i' c := by
  obtain ⟨a, ob, on, -⟩ := owner_entries N M hσ hμ 0 0
  refine ⟨a, on, fun i' c => ?_⟩
  have ent : ∀ r, T ((Sz.ref.owner σ μ).1.no 12) a r c = T (σ.no 12) mu r c := fun r => by
    obtain ⟨a', -, on', oe⟩ := owner_entries N M hσ hμ r c
    obtain rfl : a = a' := Option.some.inj (on.symm.trans on')
    exact oe
  have mu1 : Sz.ref.mu σ μ = some mu := by
    show (if σ.Below 12 then MatName.no? 3 1 1 4 σ μ else none) = some mu
    rw [if_pos hσ]
    exact all_no_ref σ hμ
  have mu2 : Sz.ref.mu (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2 = some a := by
    show (if (Sz.ref.owner σ μ).1.Below 12 then
      MatName.no? 3 1 1 4 (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2 else none) = some a
    rw [if_pos ob]
    exact on
  have s1 : Sz.ref.shapeNo (σ.no 12) mu = Sz.ref.shape σ μ := by
    unfold Sz.shapeNo
    rw [(matAt_eq_some_iff Sz.ref (σ.no 12) mu σ μ).2 ⟨hσ, rfl, mu1⟩]
  have s2 : Sz.ref.shapeNo ((Sz.ref.owner σ μ).1.no 12) a = Sz.ref.shape σ μ := by
    unfold Sz.shapeNo
    rw [(matAt_eq_some_iff Sz.ref ((Sz.ref.owner σ μ).1.no 12) a (Sz.ref.owner σ μ).1
      (Sz.ref.owner σ μ).2).2 ⟨ob, rfl, mu2⟩]
    exact shape_owner Sz.ref ref_ok.1 σ μ (by rw [mu1]; rfl)
  unfold packedOf
  rw [s1, s2]
  simp only [ent]

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.pack_radb
#print axioms OnBytes.HonestTrace.packedBy_iff
#print axioms OnBytes.HonestTrace.packedPlan_eq_packedOf
#print axioms OnBytes.HonestTrace.cellsAtOf_eq
#print axioms OnBytes.HonestTrace.smallBy_trace
#print axioms OnBytes.HonestTrace.packedBy_trace
#print axioms OnBytes.HonestTrace.packedOf_owner
