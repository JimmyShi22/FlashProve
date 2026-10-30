-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SumRowsStart.lean: CONDITIONAL. Statements with their proofs;
no definition.

What is here. The total of the cube of the sumcheck on the norms' row products (`rowsJobOf`,
SumRows.lean beside this file: the job that `jobRows`, Johnson/Desc/K4/Honest/Norms.lean, returns
where its cube fits: `jobRows_eq` there), which is that job's lead, is the batch of the honest row
products (`rowProducts`, Johnson/Desc/K4/Honest/Norms.lean) under the powers omV; and so the
verifier's form "the sumcheck starts from the batch" (`rowBatchForm`,
OnBytes/Desc/First/K4/Claims.lean) is worth 0 in a world that holds the lead and the row products
under their slots.

  `flatMap_getD`, `sum_range_stretches`   lists of one length laid end to end; a sum by stretches
  `list_sum_range`, `product_read`, `rowProducts_read`   one honest row product, read
  `rows_total`   **the total is the batch of the row products**
  `rowBatch_zero`, `rowBatch_zero'`   **the verifier's form is worth 0**; the second at norms of
     five limbs, as the verifier's test on the plan has it

Limits. At the reading `Reading.gl` alone. Premises: the tables are made (`rowMaps` returns); the
layout has 2 ^ lt tokens; the point PV has lt coordinates; for `rowBatch_zero` a norm's row has
seven products (`ledNP`), THE POWERS omV THAT THE VERIFIER HAS HEARD ARE THOSE THAT THE MAKER LAYS,
and THE WORLD HOLDS the lead and the row products under their slots. Nothing on what the tables
hold. Following import lines, and stopping unopened at every module under Johnson/Goal/, Johnson/D/,
Johnson/Bridge/ or ThirdParty/ and at every module whose name begins Cb.Bridge, its imports reach 2
modules under Johnson/Bridge/, and none of the others; what lies behind these is not counted; none
of the modules that it reaches has RecCompile in its name.

Kin. The library has a law of the same name on the same form: `rowBatch_zero`
(Johnson/Road/K4/W/Join.lean): the form is worth 0 where the claimed sum's slot holds the batch of
what lies under the products' slots, at every reading with numerals. That equation is a hypothesis
there; here it comes from `rows_total` and the world's two premises. This file does not build on
that one; both unfold the form by the library's `rowBatch_value`. `sum_flatMap`, which is spent
here, is SumRows.lean's: what that file's head says of its kin holds here. `flatMap_getD` stands
once more, to the letter, in a file that is no part of the library yet: `flat_getD`
(Johnson/Road/K4/C/NormsKit.lean), on which this one does not build.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SumRows
import Johnson.Road.FormsKeysIdnW
import Johnson.Road.K4.ListsTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E F addE mulE maddE zeroE oneE)
open OnBytes.Model (Reading World eqTab ledNP)
open OnBytes.Desc.First (P6.rowProducts)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw

/-! ## 1 Lists and sums -/

/-- Lists of one length k laid end to end: member k i + r is member r of list number i. -/
theorem flatMap_getD {α β : Type} (G : α → List β) (k : ℕ) (hk : ∀ a, (G a).length = k) (d : β) :
    ∀ (l : List α) (i r : ℕ) (hi : i < l.length), r < k →
      (l.flatMap G).getD (k * i + r) d = (G l[i]).getD r d
  | [], i, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | a :: l, 0, r, _, hr => by
    rw [List.flatMap_cons, Nat.mul_zero, Nat.zero_add,
      List.getD_append _ _ _ _ (by rw [hk]; exact hr)]
    rfl
  | a :: l, i + 1, r, hi, hr => by
    have e : k * (i + 1) + r - k = k * i + r := by
      rw [Nat.mul_succ]
      omega
    rw [List.flatMap_cons, List.getD_append_right _ _ _ _ (by rw [hk, Nat.mul_succ]; omega), hk, e]
    exact flatMap_getD G k hk d l i r (by simpa using hi) hr

/-- A sum over k N numbers, by N stretches of k. -/
theorem sum_range_stretches (k : ℕ) (g : ℕ → Cb.Gl.E) : ∀ N : ℕ,
    ∑ n ∈ Finset.range (k * N), g n =
      ∑ i ∈ Finset.range N, ∑ r ∈ Finset.range k, g (k * i + r)
  | 0 => by simp
  | N + 1 => by
    rw [Nat.mul_succ, Finset.sum_range_add, sum_range_stretches k g N, Finset.sum_range_succ]

/-- A list's sum as a sum over the members' numbers. -/
theorem list_sum_range {α : Type} (h : α × ℕ → Cb.Gl.E) : ∀ (l : List α) (k : ℕ) (d : α),
    ((l.zipIdx k).map h).sum = ∑ r ∈ Finset.range l.length, h (l.getD r d, k + r)
  | [], _, _ => by simp
  | a :: l, k, d => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, list_sum_range h l (k + 1) d,
      List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    have e : ∀ r, k + 1 + r = k + (r + 1) := fun r => by omega
    simp only [e]
    ring

/-! ## 2 The row products -/

/-- The loop of one honest row product, read. -/
theorem product_read (e ta tb : Array E) : ∀ N : ℕ,
    Reading.gl.val ((List.range N).foldl
      (fun s t => maddE s (e.getD t zeroE) (mulE (ta.getD t zeroE) (tb.getD t zeroE))) zeroE) =
      ∑ t ∈ Finset.range N, Reading.gl.val (e.getD t zeroE) *
        (Reading.gl.val (ta.getD t zeroE) * Reading.gl.val (tb.getD t zeroE))
  | 0 => by simp [Reading.gl.zero]
  | N + 1 => by
    have hm : ∀ x y z : E, Reading.gl.val (maddE x y z) =
        Reading.gl.val x + Reading.gl.val y * Reading.gl.val z := OnBytes.Slice.readE_maddE
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hm,
      product_read e ta tb N, Reading.gl.mul, Finset.sum_range_succ]

/-- Honest row product number 7 i + r, read. -/
theorem rowProducts_read (Q : K4Pub) (w : K4In) (p : Pts) (ms : Array Tab)
    (hms : rowMaps Q w p = some ms) (i r : ℕ) (hi : i < Q.P.y.NI) (hr : r < 7) :
    Reading.gl.val ((rowProducts Q w p).getD (7 * i + r) zeroE) =
      ∑ t ∈ Finset.range Q.P.y.T, Reading.gl.val ((eqTab p.PV).getD t zeroE) *
        (Reading.gl.val ((ms.getD (4 * i + (P6.rowProducts.getD r (0, 0)).1) #[]).getD t zeroE) *
          Reading.gl.val
            ((ms.getD (4 * i + (P6.rowProducts.getD r (0, 0)).2) #[]).getD t zeroE)) := by
  have e : rowProducts Q w p = (List.range Q.P.y.NI).flatMap fun i =>
      P6.rowProducts.map fun x =>
        (List.range Q.P.y.T).foldl (fun s t => maddE s ((eqTab p.PV).getD t zeroE)
          (mulE ((ms.getD (4 * i + x.1) #[]).getD t zeroE)
            ((ms.getD (4 * i + x.2) #[]).getD t zeroE))) zeroE := by
    unfold rowProducts
    rw [hms]
  rw [e, flatMap_getD _ 7 (fun a => by rw [List.length_map]; rfl) zeroE _ i r
    (by rw [List.length_range]; exact hi) hr, List.getElem_range]
  have hr' : r < P6.rowProducts.length := hr
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hr']
  have e2 : P6.rowProducts.getD r (0, 0) = P6.rowProducts[r] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr']
    rfl
  rw [e2]
  exact product_read _ _ _ _

/-! ## 3 The total -/

/-- **The total of the cube, which is the job's lead, is the batch of the honest row products under
the powers omV.** -/
theorem rows_total (Q : K4Pub) (w : K4In) (p : Pts) (ms : Array Tab)
    (hms : rowMaps Q w p = some ms) (hT : Q.P.y.T = 2 ^ Q.P.y.h.lt)
    (hPV : p.PV.size = Q.P.y.h.lt) :
    Reading.gl.val (rowsJobOf Q p ms).cube.total = ∑ n ∈ Finset.range (7 * Q.P.y.NI),
      Reading.gl.val (p.omV.getD n zeroE) * Reading.gl.val ((rowProducts Q w p).getD n zeroE) := by
  rw [sum_range_stretches, total_point Reading.gl _ p.PV rfl hPV]
  show ∑ t ∈ Finset.range (2 ^ Q.P.y.h.lt), _ = _
  have hterm : ∀ t, Reading.gl.val (termsAt (rowsJobOf Q p ms).cube.pairs
      (rowsJobOf Q p ms).cube.maps t) = ∑ i ∈ Finset.range Q.P.y.NI, ∑ r ∈ Finset.range 7,
        Reading.gl.val (p.omV.getD (7 * i + r) zeroE) *
          (Reading.gl.val ((ms.getD (4 * i + (P6.rowProducts.getD r (0, 0)).1) #[]).getD t zeroE) *
            Reading.gl.val
              ((ms.getD (4 * i + (P6.rowProducts.getD r (0, 0)).2) #[]).getD t zeroE)) := by
    intro t
    rw [termsAt_read]
    show (((List.range Q.P.y.NI).flatMap fun i => P6.rowProducts.zipIdx.map fun x =>
      (p.omV.getD (7 * i + x.2) zeroE, 4 * i + x.1.1, 4 * i + x.1.2)).map _).sum = _
    rw [sum_flatMap, OnBytes.Road.list_range_sumM]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [List.map_map, list_sum_range _ P6.rowProducts 0 (0, 0)]
    refine Finset.sum_congr rfl fun r _ => ?_
    show Reading.gl.val (p.omV.getD (7 * i + (0 + r)) zeroE) * _ = _
    rw [Nat.zero_add]
    rfl
  have hR : ∀ i ∈ Finset.range Q.P.y.NI, ∀ r ∈ Finset.range 7,
      Reading.gl.val (p.omV.getD (7 * i + r) zeroE) *
        Reading.gl.val ((rowProducts Q w p).getD (7 * i + r) zeroE) =
      ∑ t ∈ Finset.range (2 ^ Q.P.y.h.lt), Reading.gl.val ((eqTab p.PV).getD t zeroE) *
        (Reading.gl.val (p.omV.getD (7 * i + r) zeroE) *
          (Reading.gl.val ((ms.getD (4 * i + (P6.rowProducts.getD r (0, 0)).1) #[]).getD t zeroE) *
            Reading.gl.val
              ((ms.getD (4 * i + (P6.rowProducts.getD r (0, 0)).2) #[]).getD t zeroE))) := by
    intro i hi r hr
    rw [rowProducts_read Q w p ms hms i r (Finset.mem_range.mp hi) (Finset.mem_range.mp hr), hT,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun r hr => hR i hi r hr]
  simp only [hterm, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

/-- **The verifier's form "the sumcheck on the row products starts from their batch" is worth 0**,
in a world that holds the job's lead under the claimed sum's slot and the honest row products under
theirs. H: what the verifier has heard (not the maker's `heardOf`, whose slots' numbers are
defaults); of it the powers omV and two slots' numbers are read. -/
theorem rowBatch_zero (Q : K4Pub) (w : K4In) (p : Pts) (ms : Array Tab)
    (hms : rowMaps Q w p = some ms) (hT : Q.P.y.T = 2 ^ Q.P.y.h.lt)
    (hPV : p.PV.size = Q.P.y.h.lt) (hNP : ledNP Q.P.y.h.xl = 7) (H : OnBytes.Model.Layer.Heard)
    (hom : H.omV = p.omV) (Wd : World Cb.Gl.E)
    (h1 : Wd.slot H.tV.sCl = Reading.gl.val (rowsJobOf Q p ms).cube.total)
    (h2 : ∀ n, n < 7 * Q.P.y.NI →
      Wd.slot (H.sPv + n) = Reading.gl.val ((rowProducts Q w p).getD n zeroE)) :
    (OnBytes.Desc.First.K4.rowBatchForm Q.P.y H).value Reading.gl Wd = 0 := by
  rw [OnBytes.Road.K4.rowBatchForm_eq,
    OnBytes.Road.rowBatch_value Reading.gl Wd OnBytes.Road.gl_numerals, hNP, h1,
    rows_total Q w p ms hms hT hPV, hom, sub_eq_zero]
  exact Finset.sum_congr rfl fun n hn => by rw [h2 n (Finset.mem_range.mp hn)]

/-- The same at norms of five limbs. -/
theorem rowBatch_zero' (Q : K4Pub) (w : K4In) (p : Pts) (ms : Array Tab)
    (hms : rowMaps Q w p = some ms) (hT : Q.P.y.T = 2 ^ Q.P.y.h.lt)
    (hPV : p.PV.size = Q.P.y.h.lt) (hxl : Q.P.y.h.xl = 5) (H : OnBytes.Model.Layer.Heard)
    (hom : H.omV = p.omV) (Wd : World Cb.Gl.E)
    (h1 : Wd.slot H.tV.sCl = Reading.gl.val (rowsJobOf Q p ms).cube.total)
    (h2 : ∀ n, n < 7 * Q.P.y.NI →
      Wd.slot (H.sPv + n) = Reading.gl.val ((rowProducts Q w p).getD n zeroE)) :
    (OnBytes.Desc.First.K4.rowBatchForm Q.P.y H).value Reading.gl Wd = 0 :=
  rowBatch_zero Q w p ms hms hT hPV (by rw [hxl]; rfl) H hom Wd h1 h2

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.flatMap_getD
#print axioms ProofFile.Honest.K4.sum_range_stretches
#print axioms ProofFile.Honest.K4.list_sum_range
#print axioms ProofFile.Honest.K4.product_read
#print axioms ProofFile.Honest.K4.rowProducts_read
#print axioms ProofFile.Honest.K4.rows_total
#print axioms ProofFile.Honest.K4.rowBatch_zero
#print axioms ProofFile.Honest.K4.rowBatch_zero'
