-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/Starts.lean: CONDITIONAL. THE COEFFICIENTS OF FORMS THAT
ARE SUMS OF SLOTS UNDER WEIGHTS: the start forms of the merge and of the second gated layer, and the
batch of the row products.

What is here. A KIT ON THE VERIFIER's FORMS: no prover is in it. Statements and proofs.

  `cf_fold`: a form made by adding, for each member a of a list, the slot k a under the weight c
      a: its coefficient on slot j is the first form's plus the sum of the weights of the members
      with k a = j.
  `cf_fold_one`, `cf_fold_none`: at the slot of a member, where the slots are pairwise different:
      the first form's coefficient plus that member's weight; at a slot of no member: the first
      form's. KIN: of a like end, at the library's field and over lists of numbers, by the authors
      of the kind "lookup": `sc_fold` (Honest/K3/Good/Live/Pure.lean) beside `cf_fold_none`;
      `sc_join_fold` and `sc_join` (Honest/K3/Good/Join.lean) beside `cf_fold` and `cf_fold_one`.
  `wsForkStart_live`: the merge's start form (`wsForkStart`, OnBytes/Model/Merge.lean) under the
      powers of an element x that reads as not 0 has a coefficient that is not 0 on each of its
      slots, if these are pairwise different.
  `start2_live`: the second gated layer's start form (`start2`,
      Johnson/Road/Rows/GatedEnds.lean) has one on slot sH1 + 1 + lm, for lm < LamM and lm < 2 ^
      (the point's length), if no coordinate of the point reads as 0 or as 1.
  `rowBatch_cl`: the batch of the row products (`rowBatchForm`,
      OnBytes/Desc/First/K4/Claims.lean) has the coefficient 1 on the slot of the claimed sum, if
      that slot is none of the products'.
  `eqTab_all_ne`, `eqTab_getD_ne`, `powersArr_ne`: the weights: no entry of the table of equality
      weights reads as 0 under that premise on the point; nor does a power of x. `eqTab_getD_ne` IS
      A TWIN: it is, up to implicit letters, the library's
      `VerifiableInference.Desc.First.K8.Honest.eqTab_ne`
      (Johnson/Desc/K8/Honest/PlanesLiveOf.lean), typed again so that that file's imports stay out.
      The library has the fact once more, at every reading into a field, with the premise by the
      coordinates' numbers: `H2K5.Honest.eqTab_val_ne` (Johnson/Desc/K5/Honest/Law/EqTabNz.lean);
      and at the reversed point: `ProofFile.Honest.K3.Good.weight_ne` (Honest/K3/Good/Join.lean).

Not shown here. THE PREMISES: that an element reads as not 0 or not 1; that slots are different.
Nothing on entries. Nothing on what a form is worth.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.Coef
import Johnson.Road.FormsKeysEq
import Johnson.Road.Rows.GatedEnds
import OnBytes.Desc.First.P1.BatchPoint
import OnBytes.Desc.First.K4.Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The default instance `Inst.Model.Scl.ref` (a table of scales) is switched off in this file, so
that no statement picks a table of scales silently. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.Live
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Heard aff0)
open OnBytes.Road (stepL eqTab_toList eqTab_size)
open OnBytes.Road.Rows (start2)
open OnBytes.Desc.First.K4 (rowBatchForm)

section ring
variable {K : Type} [CommRing K] (ρ : Reading K) {α : Type}

/-- **A sum of slots under weights**, laid onto a form. -/
theorem cf_fold (k : α → ℕ) (c : α → E) (j : ℕ) : ∀ (l : List α) (a : Aff),
    cf ρ (l.foldl (fun s x => Aff.addMul s (Aff.slot (k x)) (c x)) a) j =
      cf ρ a j + (l.map fun x => if k x = j then ρ.val (c x) else 0).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, cf_fold k c j l, cf_addMul, List.map_cons, List.sum_cons]
    by_cases h : k x = j
    · rw [if_pos h, h, cf_slot_self]
      ring
    · rw [if_neg h, cf_slot_ne ρ h]
      ring

/-- At a slot of no member. -/
theorem cf_fold_none (k : α → ℕ) (c : α → E) {j : ℕ} (l : List α) (a : Aff)
    (h : ∀ x ∈ l, k x ≠ j) :
    cf ρ (l.foldl (fun s x => Aff.addMul s (Aff.slot (k x)) (c x)) a) j = cf ρ a j := by
  rw [cf_fold, sum_zero_of _ l fun x hx => if_neg (h x hx), add_zero]

/-- At the slot of a member, where the slots are pairwise different. -/
theorem cf_fold_one (k : α → ℕ) (c : α → E) : ∀ (l : List α) (a : Aff) {x : α}, x ∈ l →
    (l.map k).Nodup →
    cf ρ (l.foldl (fun s y => Aff.addMul s (Aff.slot (k y)) (c y)) a) (k x) =
      cf ρ a (k x) + ρ.val (c x)
  | [], _, _, hx, _ => by cases hx
  | y :: l, a, x, hx, hn => by
    rw [List.map_cons, List.nodup_cons] at hn
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [cf_fold_none ρ k c l _ fun z hz e => hn.1 (List.mem_map.2 ⟨z, hz, e⟩), cf_addMul,
        cf_slot_self]
      ring
    · have hne : k y ≠ k x := fun e => hn.1 (List.mem_map.2 ⟨x, hx, e.symm⟩)
      rw [cf_fold_one k c l _ hx hn.2, cf_addMul, cf_slot_ne ρ hne]
      ring

end ring

/-- No entry of the table of equality weights reads as 0, where no coordinate of the point reads as
0 or as 1. -/
theorem eqTab_all_ne (z : Array E)
    (hz : ∀ e ∈ z.toList, Reading.gl.val e ≠ 0 ∧ Reading.gl.val e ≠ 1) :
    ∀ b ∈ (eqTab z).toList, Reading.gl.val b ≠ 0 := by
  have step : ∀ (tab : List E) (zv : E), (∀ a ∈ tab, Reading.gl.val a ≠ 0) →
      Reading.gl.val zv ≠ 0 → Reading.gl.val zv ≠ 1 → ∀ b ∈ stepL tab zv, Reading.gl.val b ≠ 0 := by
    intro tab zv ht h0 h1 b hb
    obtain ⟨a, ha, hb⟩ := List.mem_flatMap.1 hb
    rcases List.mem_cons.1 hb with rfl | hb
    · rw [Reading.gl.sub, Reading.gl.mul]
      have e : Reading.gl.val a - Reading.gl.val a * Reading.gl.val zv =
          Reading.gl.val a * (1 - Reading.gl.val zv) := by ring
      rw [e]
      exact mul_ne_zero (ht a ha) (sub_ne_zero.2 (Ne.symm h1))
    · rw [List.mem_singleton.1 hb, Reading.gl.mul]
      exact mul_ne_zero (ht a ha) h0
  have fold : ∀ (zs tab : List E), (∀ e ∈ zs, Reading.gl.val e ≠ 0 ∧ Reading.gl.val e ≠ 1) →
      (∀ a ∈ tab, Reading.gl.val a ≠ 0) → ∀ b ∈ zs.foldl stepL tab, Reading.gl.val b ≠ 0 := by
    intro zs
    induction zs with
    | nil => exact fun _ _ ht => ht
    | cons zv zs ih =>
      intro tab hzs ht
      rw [List.foldl_cons]
      exact ih _ (fun e he => hzs e (List.mem_cons_of_mem _ he))
        (step tab zv ht (hzs zv List.mem_cons_self).1 (hzs zv List.mem_cons_self).2)
  rw [eqTab_toList]
  refine fold _ _ hz fun a ha => ?_
  rw [List.mem_singleton.1 ha, Reading.gl.one]
  exact one_ne_zero

/-- An entry inside the table. -/
theorem eqTab_getD_ne (z : Array E)
    (hz : ∀ e ∈ z.toList, Reading.gl.val e ≠ 0 ∧ Reading.gl.val e ≠ 1) {c : ℕ}
    (hc : c < 2 ^ z.size) : Reading.gl.val ((eqTab z).getD c zeroE) ≠ 0 := by
  have hs : c < (eqTab z).size := by
    rw [eqTab_size]
    exact hc
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs, Option.getD_some]
  exact eqTab_all_ne z hz _ (Array.getElem_mem_toList hs)

/-- A power of an element that reads as not 0. -/
theorem powersArr_ne {x : E} (hx : Reading.gl.val x ≠ 0) {n i : ℕ} (h : i < n) :
    Reading.gl.val ((powers x n).getD i zeroE) ≠ 0 := by
  rw [OnBytes.Desc.First.P1.powers_val Reading.gl x n i h]
  exact pow_ne_zero _ hx

/-- **The merge's start form**: on each of its slots, if these are pairwise different. -/
theorem wsForkStart_live {sv : Array ℕ} (hn : sv.toList.Nodup) {x : E}
    (hx : Reading.gl.val x ≠ 0) {i : ℕ} (hi : i < sv.size) :
    cf Reading.gl (wsForkStart sv (powers x sv.size)) (sv.getD i 0) ≠ 0 := by
  have hp : (powers x sv.size).size = sv.size := OnBytes.Desc.First.P1.powers_size x sv.size
  have hl : sv.toList.length = (powers x sv.size).toList.length := by
    rw [Array.length_toList, Array.length_toList, hp]
  have hk : ((sv.toList.zip (powers x sv.size).toList).map (·.1)) = sv.toList :=
    List.map_fst_zip (Nat.le_of_eq hl)
  have hi1 : i < sv.toList.length := by rw [Array.length_toList]; exact hi
  have hi2 : i < (powers x sv.size).toList.length := hl ▸ hi1
  have hm : (sv.toList[i], (powers x sv.size).toList[i]) ∈
      sv.toList.zip (powers x sv.size).toList := by
    have hz : i < (sv.toList.zip (powers x sv.size).toList).length := by
      rw [List.length_zip]
      omega
    have e := List.getElem_mem hz
    rw [List.getElem_zip] at e
    exact e
  have e1 : sv.getD i 0 = sv.toList[i] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some,
      Array.getElem_toList]
  have e2 : (powers x sv.size).getD i zeroE = (powers x sv.size).toList[i] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hp]; exact hi),
      Option.getD_some, Array.getElem_toList]
  unfold wsForkStart
  rw [← Array.foldl_toList, Array.toList_zip, e1]
  have := cf_fold_one Reading.gl (fun y : ℕ × E => y.1) (fun y => y.2)
    (sv.toList.zip (powers x sv.size).toList) {} hm (by rw [hk]; exact hn)
  rw [this, cf_empty, zero_add, ← e2]
  exact powersArr_ne hx hi

/-- **The second gated layer's start form**: on slot sH1 + 1 + lm. -/
theorem start2_live (LamM sH1 : ℕ) (rhoM : Array E)
    (hz : ∀ e ∈ rhoM.toList, Reading.gl.val e ≠ 0 ∧ Reading.gl.val e ≠ 1) {lm : ℕ}
    (h1 : lm < LamM) (h2 : lm < 2 ^ rhoM.size) :
    cf Reading.gl (start2 LamM sH1 rhoM) (sH1 + 1 + lm) ≠ 0 := by
  unfold start2
  have hn : ((List.range LamM).map fun l => sH1 + 1 + l).Nodup :=
    (List.nodup_range).map fun a b e => by omega
  rw [cf_fold_one Reading.gl (fun l => sH1 + 1 + l) (fun l => (eqTab rhoM).getD l zeroE)
    (List.range LamM) aff0 (List.mem_range.2 h1) hn]
  have e0 : cf Reading.gl aff0 (sH1 + 1 + lm) = 0 := cf_ofConst _ _ _
  rw [e0, zero_add]
  exact eqTab_getD_ne rhoM hz h2

/-- **The batch of the row products**: the coefficient 1 on the slot of the claimed sum. -/
theorem rowBatch_cl (y : Layer.Lay) (H : Heard)
    (h : ∀ i, i < ledNP y.h.xl * y.NI → H.sPv + i ≠ H.tV.sCl) :
    cf Reading.gl (rowBatchForm y H) H.tV.sCl = 1 := by
  unfold rowBatchForm
  rw [cf_fold_none Reading.gl (fun i => H.sPv + i) (fun i => negE (H.omV.getD i zeroE)) _ _
    fun i hi => h i (List.mem_range.1 hi), cf_slot_self]

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K4.Live.cf_fold
#print axioms ProofFile.Honest.K4.Live.cf_fold_none
#print axioms ProofFile.Honest.K4.Live.cf_fold_one
#print axioms ProofFile.Honest.K4.Live.eqTab_all_ne
#print axioms ProofFile.Honest.K4.Live.eqTab_getD_ne
#print axioms ProofFile.Honest.K4.Live.powersArr_ne
#print axioms ProofFile.Honest.K4.Live.wsForkStart_live
#print axioms ProofFile.Honest.K4.Live.start2_live
#print axioms ProofFile.Honest.K4.Live.rowBatch_cl
