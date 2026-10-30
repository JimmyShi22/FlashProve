-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/ReadShape.lean: THE SMALLNESS TEST: THE VERIFIER's TEST ON THE READS' SHAPES
(`readShapeHeld`, OnBytes/Model/Tail.lean: the size of the reads' row's column weights; each table
that is read divides its matrix's rows into whole segments and has a weight a place; the number of
segments is the number of reads that the list has laid; the matrices' rows add up to the plan's
number) SAYS YES BEHIND THE ADDING. ITS CORE IS A COUNT: the test counts the segments table by
table, in the tables' order; the library's list of the reads (`readsList`,
OnBytes/Tie/Pv/Tail/EndLoops.lean) goes matrix by matrix: both count the same. How many reads the
list has laid, and that each read's table has a weight a place, are the library's (`eqTail_total`,
Johnson/Desc/First/TailClaims/EquationsTotal.lean). What a yes of the test means is the library's
(`readShapeHeld_iff`, Johnson/Desc/First/TailClaims/AgainMeans.lean; `readShapeHeld_eq`,
AgainAgrees.lean). None of the library's goals.

  `cntOf tl Fn`   the number of segments of the table Fn, where it is read; else 0
  `pick_sum`, `segs_len`, `one_count`, `swap_sums`   sums over lists
  `readsLen_tables`   (readsList tl funs).length = the sum of cntOf over the tables
  `fold_count`   the test's own count is that sum
  **`reads_count`**   the test's own count = (readsList tl funs).length: NO PREMISE
  `rows_all`   ColsFacts tl ⊢ the matrices' rows add up to tl.mz
  `ReadsPub tl`   each table that is read has a length other than 0 that divides its matrix's number
                   of rows
  **`Added8.readShape`**   what a yes of the batching block opens (Added8) · nbW = tl.zzBlocks ·
                   ColsFacts tl · ReadsPub tl · at the ledger behind the runs the reads' row has 2
                   mz column weights ⊢ tl'.readShapeHeld ‹the reads' row's column weights behind the
                   adding› = true
KIN IN THE LIBRARY, NOT CALLED: two laws count the list of the reads matrix by matrix, as the list
itself goes: `LinkJoin.reads_length` (Johnson/Desc/First/Link/Law/ReadsLenOfSkel.lean: where every
table lies on the third vector) and `Closed.reads_length` (OnBytes/Tie/Pv/Tail/ClosedRec.lean: at a
list of tables made from shapes), each over a `segs_length` of its own. Neither speaks of the test's
own count, which goes table by table: the change of the two sums' places is what stands here.
Limits. AN IMPLICATION: `Added8`, "nbW = tl.zzBlocks", `ColsFacts`, `ReadsPub` AND THE ROW's SIZE
ARE PAID BY NOBODY HERE. `ReadsPub` IS WHAT THE RUN "K8.equations" ITSELF TESTS OF EACH TABLE THAT
IT READS (its guard "shape-functional"); the library's law on that run hands on one third of the
guard alone (a weight a place); THE OTHER TWO THIRDS ARE NOT DRAWN HERE:
Johnson/Desc/K8/Honest/EqTailGuard.lean draws them. The row's size is asked at the ledger behind the
runs, not in front of the batching.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.ReadEqs
import Johnson.Desc.K8.Honest.PlanesShape
import Johnson.Desc.First.TailClaims.EquationsTotal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- The number of segments of a table, where it is read. -/
def cntOf (tl : HTailF2) (Fn : HFun) : Nat :=
  if (decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2)) = true then
    (tl.mats.getD Fn.mat {}).m / Fn.len else 0

/-- A sum that has one term. -/
theorem pick_sum (a : Nat) (v : Nat → Nat) : ∀ n : Nat,
    ((List.range n).map fun mu => if a = mu then v mu else 0).sum = if a < n then v a else 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, pick_sum a v n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases h : a = n
    · subst h
      simp
    · have h1 : (a < n + 1) ↔ a < n := by omega
      simp [h, h1]

/-- How many segments of a table the list has at a matrix and a vector. -/
theorem segs_len (tl : HTailF2) (mu un : Nat) (Fn : HFun) :
    (segsOf tl mu un Fn).length =
      if Fn.mat = mu ∧ Fn.tree = un then (tl.mats.getD mu {}).m / Fn.len else 0 := by
  unfold segsOf
  by_cases h : Fn.mat = mu ∧ Fn.tree = un
  · rw [if_pos h, if_pos (by simp [h.1, h.2]), List.length_map, List.length_range]
  · rw [if_neg h, if_neg (by simpa using h)]
    rfl

/-- One table's segments, over all matrices and both vectors. -/
theorem one_count (tl : HTailF2) (Fn : HFun) :
    ((List.range tl.NM).map fun mu =>
      (segsOf tl mu 0 Fn).length + (segsOf tl mu 2 Fn).length).sum = cntOf tl Fn := by
  have e : ∀ mu, (segsOf tl mu 0 Fn).length + (segsOf tl mu 2 Fn).length =
      if Fn.mat = mu then
        (fun nu => if Fn.tree = 0 ∨ Fn.tree = 2 then (tl.mats.getD nu {}).m / Fn.len else 0) mu
      else 0 := by
    intro mu
    rw [segs_len, segs_len]
    by_cases h1 : Fn.mat = mu
    · by_cases h0 : Fn.tree = 0
      · simp [h1, h0]
      · by_cases h2 : Fn.tree = 2
        · simp [h1, h2]
        · simp [h1, h0, h2]
    · simp [h1]
  rw [List.map_congr_left fun mu _ => e mu, pick_sum]
  unfold cntOf
  by_cases h1 : Fn.mat < tl.NM <;> by_cases h2 : Fn.tree = 0 ∨ Fn.tree = 2 <;> simp [h1, h2]

/-- Two sums change places. -/
theorem swap_sums (w : Nat → HFun → Nat) (n : Nat) : ∀ l : List HFun,
    ((List.range n).map fun mu => (l.map (w mu)).sum).sum =
      (l.map fun Fn => ((List.range n).map fun mu => w mu Fn).sum).sum
  | [] => by simp
  | Fn :: l => by
    simp only [List.map_cons, List.sum_cons]
    rw [List.sum_map_add, swap_sums w n l]

/-- The list of the reads has as many members as the tables have segments. -/
theorem readsLen_tables (tl : HTailF2) (funs : Array HFun) :
    (readsList tl funs).length = (funs.toList.map (cntOf tl)).sum := by
  have e : (readsList tl funs).length = ((List.range tl.NM).map fun mu =>
      (funs.toList.map fun Fn =>
        (segsOf tl mu 0 Fn).length + (segsOf tl mu 2 Fn).length).sum).sum := by
    unfold readsList
    simp only [List.length_flatMap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, List.sum_map_add]
  rw [e, swap_sums (fun mu Fn => (segsOf tl mu 0 Fn).length + (segsOf tl mu 2 Fn).length)]
  exact congrArg List.sum (List.map_congr_left fun Fn _ => one_count tl Fn)

/-- The test's own count is that sum. -/
theorem fold_count (tl : HTailF2) : ∀ (l : List HFun) (q : Nat),
    (l.filter fun Fn => decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2)).foldl
      (fun q Fn => q + (tl.mats.getD Fn.mat {}).m / Fn.len) q = q + (l.map (cntOf tl)).sum
  | [], q => by simp
  | Fn :: l, q => by
    by_cases h : (decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2)) = true
    · simp only [List.filter_cons]
      rw [if_pos h, List.foldl_cons, fold_count tl l, List.map_cons, List.sum_cons]
      have e : cntOf tl Fn = (tl.mats.getD Fn.mat {}).m / Fn.len := if_pos h
      rw [e, Nat.add_assoc]
    · simp only [List.filter_cons]
      rw [if_neg h, fold_count tl l, List.map_cons, List.sum_cons]
      have e : cntOf tl Fn = 0 := if_neg h
      rw [e, Nat.zero_add]

/-- **THE TEST's OWN COUNT OF THE SEGMENTS IS THE LENGTH OF THE LIST OF THE READS.** -/
theorem reads_count (tl : HTailF2) (funs : Array HFun) :
    (funs.filter fun Fn => decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2)).foldl
      (fun q Fn => q + (tl.mats.getD Fn.mat {}).m / Fn.len) 0 = (readsList tl funs).length := by
  rw [readsLen_tables, ← Array.foldl_toList, Array.toList_filter, fold_count, Nat.zero_add]

/-- The matrices' rows add up to the plan's number. -/
theorem rows_all {tl : HTailF2} (C : ColsFacts tl) : rowsBefore tl tl.NM = tl.mz := by
  rcases Nat.eq_zero_or_pos tl.NM with h | h
  · rw [h, C.empty h]
    rfl
  · obtain ⟨n, hn⟩ : ∃ n, tl.NM = n + 1 := ⟨tl.NM - 1, by omega⟩
    have h1 := C.next n (by omega)
    rw [if_neg (by omega), off_sum C n (by omega)] at h1
    rw [hn, rowsBefore_succ]
    exact h1

/-- Each table that is read divides its matrix's rows into whole segments. -/
def ReadsPub (tl : HTailF2) : Prop :=
  ∀ Fn ∈ tl.funs.toList, Fn.mat < tl.NM → (Fn.tree = 0 ∨ Fn.tree = 2) →
    Fn.len ≠ 0 ∧ (tl.mats.getD Fn.mat {}).m % Fn.len = 0

section
variable {tl tl' : HTailF2} {funs : Array HFun} {Y G F₁ F₂ : Fork} {fr k8 bk : List Claim}
  {n₀ : Nat}

/-- **THE TEST ON THE READS' SHAPES SAYS YES BEHIND THE ADDING.** -/
theorem Added8.readShape (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) (g : Forest.Heard)
    (nbW : Nat) (hn : nbW = tl.zzBlocks) (C : ColsFacts tl) (P : ReadsPub tl)
    (hsz : ((Y.trees.getD tl.ix.ZZ {}).rows.getD tl.zzRowReads {}).L.size = 2 * tl.mz) :
    tl'.readShapeHeld
      (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * nbW) {}).L = true := by
  have hfr := A.core.2.2.1
  have eI : tl'.ix = tl.ix :=
    eq_same (·.ix) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  have eM : tl'.mz = tl.mz :=
    eq_same (·.mz) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  have eN : tl'.NM = tl.NM :=
    eq_same (·.NM) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  have eMa : tl'.mats = tl.mats :=
    eq_same (·.mats) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  have eFu : tl'.funs = tl.funs :=
    eq_same (·.funs) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  have eF : tl.funs = funs := (eq_funs A.eq).symm
  have eR : 2 * nbW = tl.zzRowReads := by
    unfold HTailF2.zzRowReads
    rw [hn]
  have eL : (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * nbW) {}).L =
      weightsOf G tl.ix.ZZ tl.zzRowReads := by
    rw [eI, eR]
    exact weights_coefBody tl' g G _ _
  obtain ⟨before, tla, tlb, s1, s2, arr, -, -, k9, -⟩ := eq_parts A.eq
  obtain ⟨tl1, -, -, hlaid, etl, hphi, -⟩ :=
    eqTail_total Reading.gl allZero F₁ before tlb tl' funs _ s2 _ k9
  have eRL : readsList tl1 funs = readsList tl funs := by
    have a1 : readsList tl' funs = readsList tl funs :=
      eq_same (fun t : HTailF2 => readsList t funs) A.eq (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ => rfl) (fun _ _ _ _ => rfl)
    have a2 : readsList tl' funs = readsList tl1 funs :=
      (congrArg (fun t : HTailF2 => readsList t funs) etl).trans rfl
    exact a2.symm.trans a1
  have h := (readShapeHeld_iff tl'
    (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * nbW) {}).L).2 (by
      dsimp only
      rw [eL, eM, eN, eMa, eFu]
      refine ⟨?_, fun Fn hFn => ?_, ?_, rows_all C⟩
      · show ((G.trees.getD tl.ix.ZZ {}).rows.getD tl.zzRowReads {}).L.size = _
        rw [lsize_of_frame, hfr, ← lsize_of_frame]
        exact hsz
      · obtain ⟨hm, hp⟩ := Array.mem_filter.1 hFn
        rw [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hp
        obtain ⟨hl, hd⟩ := P Fn (Array.mem_toList_iff.2 hm) hp.1 hp.2
        have hpos := C.pos Fn.mat hp.1
        have hle : Fn.len ≤ (tl.mats.getD Fn.mat {}).m :=
          Nat.le_of_dvd hpos (Nat.dvd_of_mod_eq_zero hd)
        refine ⟨by omega, hl, hd, ?_⟩
        refine hphi (Fn, 0) ?_
        rw [eRL, ← eF]
        exact (mem_readsList tl tl.funs Fn 0).2
          ⟨Array.mem_toList_iff.2 hm, hp.1, hp.2, Nat.div_pos hle (by omega)⟩
      · rw [hlaid, eRL, ← eF]
        exact reads_count tl tl.funs)
  rw [readShapeHeld_eq] at h
  exact h

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.pick_sum
#print axioms VerifiableInference.Desc.First.K8.Honest.segs_len
#print axioms VerifiableInference.Desc.First.K8.Honest.one_count
#print axioms VerifiableInference.Desc.First.K8.Honest.swap_sums
#print axioms VerifiableInference.Desc.First.K8.Honest.readsLen_tables
#print axioms VerifiableInference.Desc.First.K8.Honest.fold_count
#print axioms VerifiableInference.Desc.First.K8.Honest.reads_count
#print axioms VerifiableInference.Desc.First.K8.Honest.rows_all
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.readShape
