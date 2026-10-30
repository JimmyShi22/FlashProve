-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/TieBack.lean: the smallness test (K8): from the library's `TieOf`
(Johnson/Desc/First/K8/LawItems.lean: there are small integers of which the tie's two clauses hold)
to `TieBy` (Johnson/Desc/ProofFile/Honest/K8/SmallLaw.lean) AT INTEGERS THAT ARE NAMED, WHERE THESE
ARE SMALL AND THE FIRST CLAUSE HOLDS OF THEM. A record, a table of cells and integers are letters:
no thread, no prover, no Script. Three statements with their proofs; no definition.

  `uniq_here`      the three inequalities of `Alg.small_unique` (Alg/Range.lean) at the shift
                  2 ^ lbz, the radix radb and the field's prime
  `row_in_range`   where a table has an entry for column c and segment sg, its matrix is counted, c
                  is one of its columns, and each of the segment's rows is one of its rows
  **`tieBy_of_tieOf`**   TieOf tl A · the symbol arrays of A are the packing of a₀ · a₀ is small in
                  range ⊢ TieBy tl A a₀: the integers that TieOf gives are a₀ in range, since a
                  packing has one small column; so its clause on the reads is TieBy's
What it is for. The item "tie l" of the table of joints says `TieOf`; the kind's law wants `TieBy`
at the cells of the input's trace. With this law the clause on the reads need not be shown of these
cells a second time.
No option is raised, no instance taken away. Tactics that search: `norm_num` on four lines, on
closed numbers; `simp only` with a closed list on one line. `dsimp only` on one line lays a `let`
open.
Limits. An implication. That any table meets the premises is not said. Out of range nothing is said
of a₀.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.SmallLaw
import Johnson.Desc.First.K8.LawItems
import Alg.Range
import Cb.Gl.GlField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.K8 (TieOf)
open VerifiableInference.Desc.First.K8.Honest (CellsAt)

/-- The three inequalities under which a packing has one small column, at the library's numbers. -/
theorem uniq_here : (0 : ℤ) < ((2 ^ lbz : ℕ) : ℤ) ∧
    4 * ((2 ^ lbz : ℕ) : ℤ) - 1 ≤ ((radb : ℕ) : ℤ) ∧
    (4 * ((2 ^ lbz : ℕ) : ℤ) - 2) * (1 + ((radb : ℕ) : ℤ) + ((radb : ℕ) : ℤ) ^ 2) <
      ((Cb.Gl.p : ℕ) : ℤ) := by
  have hp : ((Cb.Gl.p : ℕ) : ℤ) = 2 ^ 64 - 2 ^ 32 + 1 := by
    show (((2 ^ 64 - 2 ^ 32 + 1 : ℕ) : ℕ) : ℤ) = 2 ^ 64 - 2 ^ 32 + 1
    norm_num
  have hb : ((2 ^ lbz : ℕ) : ℤ) = 2 ^ 17 := by
    show ((2 ^ 17 : ℕ) : ℤ) = 2 ^ 17
    norm_num
  have hr : ((radb : ℕ) : ℤ) = 2 ^ 20 := by
    show ((2 ^ 20 : ℕ) : ℤ) = 2 ^ 20
    norm_num
  rw [hp, hb, hr]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- What an entry of a table says of its matrix, column and rows. -/
theorem row_in_range (tl : HTailF2) (Fn : HFun) {c sg pos : ℕ} (h : tl.tabAt Fn c sg = some pos)
    {j : ℕ} (hj : j < Fn.len) :
    Fn.mat < tl.NM ∧ c < (tl.mats.getD Fn.mat {}).k ∧
      sg * Fn.len + j < (tl.mats.getD Fn.mat {}).m := by
  unfold HTailF2.tabAt at h
  split at h
  · rename_i h1
    dsimp only at h
    split at h
    · rename_i h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2
      refine ⟨h1.1, h2.1, ?_⟩
      calc sg * Fn.len + j < sg * Fn.len + Fn.len := Nat.add_lt_add_left hj _
        _ = (sg + 1) * Fn.len := (Nat.succ_mul sg Fn.len).symm
        _ ≤ ((tl.mats.getD Fn.mat {}).m / Fn.len) * Fn.len := Nat.mul_le_mul_right _ h2.2
        _ ≤ (tl.mats.getD Fn.mat {}).m := Nat.div_mul_le_self _ _
    · cases h
  · cases h

/-- **From the library's tie to the tie at named integers**, where these are small and the symbol
arrays are their packing. -/
theorem tieBy_of_tieOf (tl : HTailF2) (A : TableE) (a₀ : CellsAt) (hT : TieOf tl A)
    (h1 : ∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
      ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
        A (tl.gtTree.getD μ 0) i' c =
          ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => a₀ μ i c) i' : ℤ) :
            Cb.Gl.E))
    (hs : ∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k → ∀ i, i < (tl.mats.getD μ {}).m →
      |a₀ μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) : TieBy tl A a₀ := by
  obtain ⟨a, ha, hp, hr⟩ := hT
  refine ⟨h1, fun n Fn hFn c sg pos hpos => ?_⟩
  rw [hr n Fn hFn c sg pos hpos]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨hμ, hc, hi⟩ := row_in_range tl Fn hpos (Finset.mem_range.1 hj)
  have key : (fun i : Fin (tl.mats.getD Fn.mat {}).m => a Fn.mat i c) =
      fun i : Fin (tl.mats.getD Fn.mat {}).m => a₀ Fn.mat i c :=
    Alg.small_unique (E := Cb.Gl.E) Cb.Gl.p uniq_here.1 uniq_here.2.1 uniq_here.2.2
      (Nat.le_refl (Alg.symRows (tl.mats.getD Fn.mat {}).m))
      (fun i => ha Fn.mat hμ c hc i i.2) (fun i => hs Fn.mat hμ c hc i i.2)
      (fun i' => by rw [← hp Fn.mat hμ c hc i' i'.2, ← h1 Fn.mat hμ c hc i' i'.2])
  have e := congrFun key ⟨sg * Fn.len + j, hi⟩
  have e' : a Fn.mat (sg * Fn.len + j) c = a₀ Fn.mat (sg * Fn.len + j) c := e
  rw [e']

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.uniq_here
#print axioms ProofFile.Honest.K8.row_in_range
#print axioms ProofFile.Honest.K8.tieBy_of_tieOf
