-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K9/Honest/LensPaid/ReadsLay.lean: at a layers' segment the reads that the public test lensEqB
(Johnson/Desc/K9/Honest/LensEq.lean) counts, by the library's K9Asks.readsB over K9Asks.layPairs
(Johnson/Desc/First/Link/K9RowsAsk.lean), are the reads that the library's planner counts (Layer.readsCount,
OnBytes/Model/LayerPlan.lean). Statements and proofs; nothing is evaluated in this file but seven comparisons of
numerals. layTables_in_scope, which reads_lay_eq calls, rests, in its own file, on six closed facts that Lean's kernel
evaluates at the hand-written shape; the library's lemmas on the scope beneath it evaluate more.

  sum_layers: general in the layout: over the families of a group, written as numbers (K8.Asks.layers,
    Johnson/Desc/First/K8/Asks.lean), the families' reads add up to Layer.readsCount, where the rows are those of the
    group's own list of matrices and the layout's T is 2 ^ lt and g is one of the layout's groups. Built as end_lay
    (Johnson/Road/K4/Plan/TabsEndLay.lean): each family's matrices have one size (tails_pair,
    Johnson/Road/FormsKeysTab.lean; the matrix b as there); the nine lists are lists of equal members; then arithmetic.
  reads_lay_core: general in the layout: where Layer.layTables returns at the group's own sizes, at every list of
    matrices with these sizes and at NM its length, under the same two premises on the layout (T is 2 ^ lt; g is one of
    its groups): readsB over what is laid is Layer.readsCount. By layTables_pairs, sum_flat and flat_below
    (LayFlat.lean), readsB_flat (ReadsFlat.lean), asks_layers (Johnson/Desc/First/K8/LawShapes.lean), asks_bound
    (Johnson/Meaning/ReadsPlan.lean) and sum_layers.
  reads_lay_eq: in the goals' scope, at each of the twelve groups and the group's plan: layPairs returns, and readsB
    at the plan's own matrices is Layer.readsCount. That the laying returns: layTables_in_scope
    (Johnson/Desc/First/Link/Law/LayTablesInScope.lean). The plan's sizes: tails_of_public, mats_of_public
    (Johnson/Goal/Meaning/Pub34Scope.lean). T: Laid2.T (Johnson/Road/FormsKeysAddr.lean).

Limits. The scope enters reads_lay_eq in three places alone: the laying returns; there are twelve groups; the layout is
one that the library's own layout returns. That a group has a plan is a premise of reads_lay_eq. Nothing is said of what
a read holds or of where a table lies. No property of the protocol is claimed: nothing is said on its soundness,
completeness, binding or hiding.
-/
import Johnson.Desc.K9.Honest.LensPaid.ReadsFlat
import Johnson.Desc.K9.Honest.LensPaid.LayFlat
import Johnson.Desc.First.Link.Law.LayTablesInScope
import Johnson.Desc.First.K8.LawShapes
import Johnson.Road.K4.Plan.TabsEndLay
import Johnson.Meaning.ReadsPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Lay Reads TableAsk TableAt layTables tableAsks)
open OnBytes.Road (matsR tails_pair tails_pairs tails_sizes getD_three)
open VerifiableInference.Desc.First.K8 (triOf asks_layers)
open VerifiableInference.Desc.K9Asks (readsB layPairs)

/-! ## The families' reads add up to the planner's count -/

/-- Over a group's families the reads add up to the planner's count, at the rows of the group's own matrices. -/
theorem sum_layers {y : Lay} (rd : Reads) {g : ℕ} (hg : g < y.NGr) (hT : y.T = 2 ^ y.h.lt) (rows : ℕ → ℕ)
    (hrow : ∀ M, rows M = ((matsR y g).getD M (0, 0)).1) :
    ((VerifiableInference.Desc.First.K8.Asks.layers y rd g).map (famReads rows)).sum =
      OnBytes.Model.Layer.readsCount y rd g := by
  have at' : ∀ {M m k : ℕ}, (matsR y g).getD M (0, 0) = (m, k) → rows M = m :=
    fun t => by rw [hrow, t]
  have tB : (matsR y g).getD (y.parts.getD 0 0 + y.parts.getD 1 0 + 1) (0, 0) =
      (2 ^ y.h.lmb, y.kbm) := by
    have t3 := (getD_three (y.parts.getD 0 0) (y.parts.getD 1 0)
      (y.mrow.getD 0 0, y.kcol.getD 0 0) (y.mrow.getD 1 0, y.kcol.getD 1 0)
      [(y.mrow.getD 2 0, y.kcol.getD 2 0), (2 ^ y.h.lmb, y.kbm),
       (y.mrow.getD 3 0, y.kcol.getD 3 0), (y.mxb, y.kxb), (y.mxb, y.kxb)] (0, 0)).2.2 1
    unfold matsR
    rw [tails_pairs y hg, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      ← List.getD_eq_getElem?_getD]
    exact t3
  have fAF : famReads rows (0, y.parts.getD 0 0, 2 ^ y.h.la) =
      y.parts.getD 0 0 * (y.mrow.getD 0 0 / 2 ^ y.h.la) :=
    famReads_const rows fun q hq => at' (tails_pair y hg (mat := 0) (by decide) hq)
  have fAD : famReads rows (y.parts.getD 0 0, y.parts.getD 1 0, 2 ^ y.h.lt) =
      y.parts.getD 1 0 * (y.mrow.getD 1 0 / 2 ^ y.h.lt) :=
    famReads_const rows fun q hq => at' (tails_pair y hg (mat := 1) (by decide) hq)
  have fAR : famReads rows (y.parts.getD 0 0 + y.parts.getD 1 0, 1, 2 ^ y.h.lt) =
      y.mrow.getD 2 0 / 2 ^ y.h.lt :=
    famReads_one rows fun q hq => at' (tails_pair y hg (mat := 2) (by decide) hq)
  have fQA : famReads rows (y.parts.getD 0 0 + y.parts.getD 1 0 + 2, 1, 2 ^ y.h.la) =
      y.mrow.getD 3 0 / 2 ^ y.h.la :=
    famReads_one rows fun q hq => at' (tails_pair y hg (mat := 3) (by decide) hq)
  have fQS : famReads rows (y.parts.getD 0 0 + y.parts.getD 1 0 + 2, 1, 2 ^ y.h.lt) =
      y.mrow.getD 3 0 / 2 ^ y.h.lt :=
    famReads_one rows fun q hq => at' (tails_pair y hg (mat := 3) (by decide) hq)
  have fXI : famReads rows (y.parts.getD 0 0 + y.parts.getD 1 0 + 4, 1, 2 ^ y.h.la) =
      y.mxb / 2 ^ y.h.la :=
    famReads_one rows fun q hq => at' (tails_pair y hg (mat := 4) (by decide) hq)
  have fXO : famReads rows (y.parts.getD 0 0 + y.parts.getD 1 0 + 3, 1, 2 ^ y.h.la) =
      y.mxb / 2 ^ y.h.la :=
    famReads_one rows fun q hq => at' (tails_pair y hg (mat := 5) (by decide) hq)
  have fB : famReads rows (y.parts.getD 0 0 + y.parts.getD 1 0 + 1, 1, 2 ^ y.h.lmb) = 1 := by
    have e : famReads rows (y.parts.getD 0 0 + y.parts.getD 1 0 + 1, 1, 2 ^ y.h.lmb) =
        2 ^ y.h.lmb / 2 ^ y.h.lmb :=
      famReads_one rows fun q hq => by
        obtain rfl : q = 0 := by omega
        exact at' tB
    rw [e, Nat.div_self (Nat.two_pow_pos _)]
  unfold VerifiableInference.Desc.First.K8.Asks.layers OnBytes.Model.Layer.readsCount
  by_cases h0 : (g == 0) = true <;> by_cases h4 : y.h.p4 = true <;>
    simp only [h0, h4, hT, Bool.false_eq_true, ↓reduceIte, List.map_append, List.sum_append,
      List.map_replicate, List.sum_replicate, smul_eq_mul, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, fAF, fAD, fAR, fQA, fQS, fXI, fXO, fB] <;>
    ring

/-! ## The test's count over what is laid -/

/-- Where the laying returns at the group's own sizes, the test's count over what is laid is the planner's count. -/
theorem reads_lay_core {y : Lay} {rd : Reads} {g : ℕ} (hT : y.T = 2 ^ y.h.lt) (hg : g < y.NGr)
    {mats : Array TMat} {NM : ℕ} (htm : (mats.map fun M => (M.m, M.k)) = matsR y g)
    (hNM : NM = mats.size) {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hr : layTables (matsR y g) (tableAsks y rd g) 0 = some r) :
    readsB NM mats (r.2.1.flatMap fun a => a.2.map fun m => (m.1, a.1.L)) =
      OnBytes.Model.Layer.readsCount y rd g := by
  have hsz : mats.size = y.parts.getD 0 0 + y.parts.getD 1 0 + 5 := by
    have e := congrArg Array.size htm
    unfold matsR at e
    rw [Array.size_map, Array.size_map, (tails_sizes y hg).1] at e
    exact e
  have hb : ∀ t ∈ ((tableAsks y rd g).map triOf).flatMap famPairs, t.1 < NM := by
    rw [hNM, hsz]
    refine flat_below fun a ha => ?_
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    exact _root_.Meaning.Reads.asks_bound y rd g b hb
  have hrow : ∀ M, (mats.getD M {}).m = ((matsR y g).getD M (0, 0)).1 := by
    intro M
    have e := OnBytes.Road.K4.Plan.pair_of mats M
    rw [htm] at e
    exact (congrArg Prod.fst e).symm
  rw [layTables_pairs _ _ _ _ hr, readsB_flat NM mats _ hb]
  refine (sum_flat (fun M => (mats.getD M {}).m) _).trans ?_
  rw [asks_layers]
  exact sum_layers rd hg hT _ hrow

/-! ## In the goals' scope -/

section
open OnBytes.Model.Verify (publicOf Public)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- In scope, at each of the twelve groups with its plan, the test's list of tables is there, and the reads that the
test counts over it at the plan's matrices are the planner's count. -/
theorem reads_lay_eq (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hpub : publicOf Pb.pol Pb.KL lay = .ok X) {g : ℕ} (hg : g < 12) {hp : Layer.HPlan2}
    (hG : X.G[g]? = some hp) :
    ∃ ps, layPairs X.layers g = some ps ∧
      readsB hp.tl.NM hp.tl.mats ps = Layer.readsCount X.layers.y X.layers.rd g := by
  obtain ⟨r, hr, -, -⟩ := VerifiableInference.Desc.K9Asks.layTables_in_scope hS hR hpub hg
  have B := OnBytes.Road.Hd.public_of_core hpub (OnBytes.Road.Hd.core_of_scope hS hR hpub)
  have L2 := OnBytes.Road.laid2_of_layout B.lay
  have ey : X.layers.y = X.y := rfl
  obtain ⟨htm, hNM⟩ := _root_.Meaning.P34.tails_of_public hpub hG
  refine ⟨r.2.1.flatMap fun a => a.2.map fun m => (m.1, a.1.L), ?_, ?_⟩
  · unfold VerifiableInference.Desc.K9Asks.layPairs
    rw [hr, Option.map_some]
  · rw [_root_.Meaning.P34.mats_of_public hpub g, ey] at hr
    rw [ey]
    exact reads_lay_core L2.T (by rw [B.groups]; exact hg) htm hNM hr

end

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.sum_layers
#print axioms ProofFile.Honest.K9.reads_lay_core
#print axioms ProofFile.Honest.K9.reads_lay_eq
