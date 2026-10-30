-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ReadsLay.lean: THE PROOFS OF THE THREE STATEMENTS OF
Johnson/P1K8R/ReadsLayStatement.lean: at a layers' segment the reads that the public test `rowsFitB`
counts off the segment's tables are at most the planner's own count `Layer.readsCount`. BY THE MAKE
OF THE LAYOUT: no size is evaluated (the numerals are "twelve groups" and the kit's numbers 0 to 5
of the six matrices). Statements with their proofs; no definition.

  `layParts_sum`   one family's laying, from any number of parts still to place
  `pairs_sum`      `PairsSum`
  `fam_sum`        a list of families that differ in their names and points alone
  `rows_tie`       a list of matrices with the layout's rows and columns has the layout's rows
  `reads_lay_of`   `ReadsLayOf`
  `reads_lay`      `ReadsLay`

By: the library's `tails_sizes` (Johnson/Road/FormsKeysTab.lean: the rows of af, ad, ar, qa and the
two matrices of the stream) · `Fo.PlaneMatG.tailsOf_b`
(OnBytes/Tie/Pv/Lookup/Ends/FoPlaneMatPubG.lean: the matrix b) · `K4.Plan.pair_of`
(Johnson/Road/K4/Plan/TabsEndLay.lean) · `Meaning.P34.tails_of_public`, `mats_of_public`,
`more_of_public`, `pub_more` (Johnson/Goal/Meaning/Pub34Scope.lean) · `pub34_all` (Pub34All.lean) ·
`laid2_of_layout` (Johnson/Road/FormsKeysAddr.lean) · `Hd.core_of_scope`, `public_of_core`,
`eleven_of_core`, `public_plans`, `plan_labels` (as `Meaning.planG_there`,
Johnson/Goal/Meaning/HidOwner.lean, calls them: twelve plans) · `layTables_in_scope`
(Johnson/Desc/First/Link/Law/LayTablesInScope.lean: the laying returns) · `readsB_le`
(Johnson/Desc/First/Link/Law/K9RowsParts.lean).

NEAR RELATIVES, NOT CALLED. Of `layParts_sum`: the library has one family's laying AS A LIST, twice:
`layParts_eq` with `layParts_run` (Johnson/Road/FormsKeysTab.lean), where all parts have the same
rows and columns; `layParts_eq` (Johnson/Desc/First/K8/LawShapes.lean), with no such premise,
through its own `goFam`. The first would lay a premise on every family's matrices on `PairsSum`,
which a layout could pay only by a second walk over the nine lists; the second wants an induction on
`goFam` of this one's length. This one ends in a sum under any function and asks nothing of the
matrices. Of `pairs_sum`: the library's laws on `layTables` (`layTables_chain`, `_len`, `_laid`,
`_both`, `_mem`, `_seq`, `_within`, `_below`, `_bound`, `tiles_layTables`) have the names in order,
membership, stretches of entries or bounds: none has the laid families in order.

HOW THE WALK GOES. `tableAsks` and `readsCount` are unfolded; four cases (the first group or not;
the switch p4); in each the families' sums are rewritten and `ring` closes. THE REWRITING IS UP TO
UNFOLDING (`erw`, four times): the families are stated here through the kit's `firstM` and `partsM`
(Johnson/Road/FormsKeysMat.lean), `tableAsks` has `matIx`'s fields and the layout's own: a turn of
these definitions' reducibility could break it. `simp` without a list closes two goals on constant
lists. The line `attribute [-instance] Inst.Model.Scl.ref` stands as in the library's neighbours: no
default table of scales is in sight.

Limits. Those of the statements' file. The last stands in the goals' scope because the laying's
return, the twelve groups and the layout's own return are had there. Nothing on any property.
-/
import Johnson.P1K8R.ReadsLayStatement
import Johnson.Desc.First.Link.Law.K9RowsParts
import Johnson.Desc.First.Link.Law.LayTablesInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Reads TableAsk TableAt layParts layTables tableAsks matIx tailsOf
  readsCount)
open VerifiableInference.Desc.K9Asks (layPairs readsB)

/-- One family's laying: n parts still to place. -/
theorem layParts_sum (mats : Array (ℕ × ℕ)) (a : TableAsk) (f : ℕ → ℕ → ℕ) : ∀ (n p : ℕ),
    n ≤ a.parts →
    (((layParts mats a n p).1.map fun m => (m.1, a.L)).map fun t => f t.1 t.2).sum =
      ((List.range n).map fun q => f (a.M0 + (a.parts - n) + q) a.L).sum
  | 0, _, _ => rfl
  | n + 1, p, h => by
    simp only [layParts, List.map_cons, List.sum_cons]
    rw [layParts_sum mats a f n _ (by omega), List.range_succ_eq_map, List.map_cons,
      List.sum_cons, List.map_map, Nat.add_zero]
    congr 2
    refine List.map_congr_left fun q _ => ?_
    show f (a.M0 + (a.parts - n) + q) a.L = f (a.M0 + (a.parts - (n + 1)) + (q + 1)) a.L
    congr 1
    omega

/-- **The sum over the pairs that are laid.** -/
theorem pairs_sum : PairsSum := by
  intro mats f asks
  induction asks with
  | nil =>
    intro p x h
    obtain rfl : (([], [], p) : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ) = x :=
      Option.some.inj h
    rfl
  | cons a rest ih =>
    intro p x h
    simp only [layTables] at h
    split at h
    · cases h
    · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      rw [ih _ r hr, layParts_sum mats a f a.parts p (Nat.le_refl _), Nat.sub_self]
      simp only [Nat.add_zero]

/-- A list of families with one first matrix, one number of parts and one block. -/
theorem fam_sum (f : ℕ → ℕ → ℕ) (mk : String → TableAsk) (M0 parts L c : ℕ)
    (h1 : ∀ n, (mk n).M0 = M0 ∧ (mk n).parts = parts ∧ (mk n).L = L)
    (hc : ∀ q, q < parts → f (M0 + q) L = c) (pts : List String) :
    ((pts.map mk).map fun a => ((List.range a.parts).map fun q => f (a.M0 + q) a.L).sum).sum =
      pts.length * (parts * c) := by
  have e : ∀ n, ((List.range (mk n).parts).map fun q => f ((mk n).M0 + q) (mk n).L).sum =
      parts * c := by
    intro n
    obtain ⟨a1, a2, a3⟩ := h1 n
    rw [a1, a2, a3, List.map_congr_left (g := fun _ => c) fun q hq => hc q (List.mem_range.1 hq)]
    simp
  have e' : ((fun a : TableAsk => ((List.range a.parts).map fun q => f (a.M0 + q) a.L).sum) ∘ mk) =
      fun _ => parts * c := funext e
  rw [List.map_map, e']
  simp

/-- A list of matrices with the layout's rows and columns has the layout's rows. -/
theorem rows_tie {y : Lay} {g : ℕ} {mats : Array TMat}
    (hm : (mats.map fun M => (M.m, M.k)) = matsR y g) (M : ℕ) :
    (mats.getD M {}).m = (((tailsOf y).getD g {}).mats.getD M {}).m := by
  have e := congrArg (fun a => (a.getD M (0, 0)).1) hm
  unfold matsR at e
  simp only [K4.Plan.pair_of] at e
  exact e

/-- **At a layout: the sum over the pairs is the planner's count.** -/
theorem reads_lay_of : ReadsLayOf := by
  intro y rd g mats x hg hT hm hx
  rw [pairs_sum (matsR y g) (fun M L => (mats.getD M {}).m / L) _ 0 x hx]
  obtain ⟨-, hs⟩ := tails_sizes y hg
  have row : ∀ mat p, mat ≤ 5 → p < partsM y mat →
      (mats.getD (firstM y mat + p) {}).m = rowsM y mat := fun mat p h1 h2 => by
    rw [rows_tie hm]
    exact (hs mat p h1 h2).2.1
  have rb : (mats.getD ((matIx y).iB + 0) {}).m = 2 ^ y.h.lmb := by
    rw [rows_tie hm]
    exact (_root_.Fo.PlaneMatG.tailsOf_b y g hg).1
  have one : 2 ^ y.h.lmb / 2 ^ y.h.lmb = 1 := Nat.div_self (Nat.two_pow_pos _)
  have F := fun (mn : String) (mat : ℕ) (hmat : mat ≤ 5) (L : ℕ) (lng : Bool)
      (pts : List String) =>
    fam_sum (fun M L => (mats.getD M {}).m / L)
      (fun n => ⟨mn ++ "@" ++ n, firstM y mat, partsM y mat, L, n, lng⟩) (firstM y mat)
      (partsM y mat) L (rowsM y mat / L) (fun _ => ⟨rfl, rfl, rfl⟩)
      (fun q hq => by
        show (mats.getD (firstM y mat + q) {}).m / L = _
        rw [row mat q hmat hq]) pts
  have f0 := F "af" 0 (by omega) (2 ^ y.h.la) true rd.rdAF
  have f3 := F "qa" 3 (by omega) (2 ^ y.h.la) true rd.rdQA
  have f4 := F "xbI" 4 (by omega) (2 ^ y.h.la) true rd.rdXI
  have f4' := F "xbI" 4 (by omega) (2 ^ y.h.la) true ["Z_E"]
  have f5 := F "xbO" 5 (by omega) (2 ^ y.h.la) true rd.rdXO
  have f1 := F "ad" 1 (by omega) y.T false rd.rdAD
  have f2 := F "ar" 2 (by omega) y.T false rd.rdAR
  have f3' := F "qa" 3 (by omega) y.T false rd.rdQS
  unfold tableAsks readsCount
  simp only [List.map_append, List.sum_append]
  by_cases h0 : (g == 0) = true <;> by_cases h4 : y.h.p4 = true <;>
    simp only [h0, h4, if_true, if_false, Bool.false_eq_true, List.map_nil, List.sum_nil]
  · erw [f0, f3, f4, f4', f5, f1, f2, f3']
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.range_one, rb, one,
      partsM, rowsM, hT, List.length_cons, List.length_nil]
    ring
  · erw [f0, f3, f4, f4', f5, f1, f2]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.range_one, rb, one,
      partsM, rowsM, hT, List.length_cons, List.length_nil]
    ring
  · erw [f0, f3, f4, f5, f1, f2, f3']
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.range_one, rb, one,
      partsM, rowsM, hT]
    ring
  · erw [f0, f3, f4, f5, f1, f2]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.range_one, rb, one,
      partsM, rowsM, hT]
    ring

/-- **In scope: the segment's pairs are there, and the reads counted off them are at most the
planner's.** -/
theorem reads_lay : ReadsLay := by
  intro Pb pp lay X g hp hS hR hpub hg
  have C := Hd.core_of_scope hS hR hpub
  have hg12 : g < 12 := by
    have B := (Hd.eleven_of_core hpub C (Hd.npOf X.hS)).1
    obtain ⟨sc, rope, wsLay, V, tokv, set, hP, hG⟩ := Hd.public_plans hpub
    obtain ⟨hsz, -⟩ := Hd.plan_labels hP hG
    have h0 : g < X.G.size := (Array.getElem?_eq_some_iff.1 hg).1
    rw [hsz, B.groups] at h0
    exact h0
  obtain ⟨r, hr, -, -⟩ := VerifiableInference.Desc.K9Asks.layTables_in_scope hS hR hpub hg12
  refine ⟨_, by unfold layPairs; rw [hr]; rfl, ?_⟩
  refine (VerifiableInference.Desc.K9Asks.readsB_le _ _ _).trans (Nat.le_of_eq ?_)
  have ey : X.layers.y = X.y :=
    (_root_.Meaning.P34.pub_more (_root_.Meaning.P34.more_of_public hpub).2.2.2.1).1
  have hN : X.y.NGr = 12 := (_root_.Meaning.P34.pub34_all hS hR hpub gl_numerals).2.1
  have L2 := laid2_of_layout (Hd.public_of_core hpub C).lay
  rw [_root_.Meaning.P34.mats_of_public hpub g, ey] at hr
  rw [ey]
  exact reads_lay_of X.y X.layers.rd g hp.tl.mats r (by rw [hN]; exact hg12) L2.T
    (_root_.Meaning.P34.tails_of_public hpub hg).1 hr

end P1K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms P1K8.layParts_sum
#print axioms P1K8.pairs_sum
#print axioms P1K8.fam_sum
#print axioms P1K8.rows_tie
#print axioms P1K8.reads_lay_of
#print axioms P1K8.reads_lay
