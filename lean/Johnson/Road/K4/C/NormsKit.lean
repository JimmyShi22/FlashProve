-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/NormsKit.lean: loops read as sums; limbSums_read is CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side: the loops of the norms'
makers (Johnson/Desc/K4/Honest/Norms.lean: limbSumsAt, wSums), read into the field, are sums.
Statements and proofs.

  `flat_getD`        a member of a list made of stretches of one length.
  `toList_getD`, `modify_getD`   a member of an array's list; of an array behind a change at one
                     place.
  `Adds`, `adds_foldl`   a step that adds to each member of an array of words; a loop of such steps.
  `limbSums_word`    the sums of limb products of one norm at one token, in the base field.
  `limbSums_read`    the same in the extension field: the library's Wsum: AT FIVE LIMBS ALONE (hxl;
                     the files that call it have it from Fits).
  `tokens_read`      the loop over the tokens.
  `wSums_read`       a member of wSums is a sum over the tokens.

Not shown here. Nothing on the cells, on a world or on a verifier: these are laws on loops over
arrays of the program's words and elements.
No property is claimed.
-/
import Johnson.Road.K4.C.Fold
import Johnson.Desc.K4.Honest.Norms
import Johnson.Road.FormsKeysLook
import Inst.Model.Common.Ledger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Slice (toF)
open OnBytes.Desc.First.K4.Honest

/-- A member of a list made of stretches of one length. -/
theorem flat_getD {α β : Type} (G : α → List β) (k : ℕ) (hk : ∀ a, (G a).length = k) (d : β) :
    ∀ (l : List α) (i r : ℕ) (hi : i < l.length), r < k →
      (l.flatMap G).getD (k * i + r) d = (G l[i]).getD r d
  | [], i, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | a :: l, 0, r, _, hr => by
    rw [List.flatMap_cons, Nat.mul_zero, Nat.zero_add,
      List.getD_append _ _ _ _ (by rw [hk]; exact hr)]
    rfl
  | a :: l, i + 1, r, hi, hr => by
    have e : k * (i + 1) + r = (G a).length + (k * i + r) := by
      rw [hk, Nat.mul_succ]
      omega
    rw [List.flatMap_cons, e, List.getD_append_right _ _ _ _ (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, flat_getD G k hk d l i r (Nat.lt_of_succ_lt_succ hi) hr]
    rfl

/-- A member of an array's list. -/
theorem toList_getD {α : Type} (a : Array α) (i : ℕ) (d : α) : a.toList.getD i d = a.getD i d := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

/-- A member of an array behind a change at one place. -/
theorem modify_getD (a : Array F) (k s : ℕ) (f : F → F) (hs : s < a.size) :
    (a.modify k f).getD s 0 = if k = s then f (a.getD s 0) else a.getD s 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_modify, Array.getD_eq_getD_getElem?]
  by_cases h : k = s
  · rw [if_pos h, if_pos h, Array.getElem?_eq_getElem hs]
    rfl
  · rw [if_neg h, if_neg h]

/-- The step keeps the array's size n and adds g x s, read in the base field, to member s. -/
def Adds {α : Type} (n : ℕ) (step : Array F → α → Array F) (g : α → ℕ → Cb.Gl.F) : Prop :=
  ∀ acc x, acc.size = n → (step acc x).size = n ∧
    ∀ s, s < n → toF ((step acc x).getD s 0) = toF (acc.getD s 0) + g x s

/-- A loop of such steps adds the sum. -/
theorem adds_foldl {α : Type} {n : ℕ} {step : Array F → α → Array F} {g : α → ℕ → Cb.Gl.F}
    (h : Adds n step g) : ∀ (l : List α) (acc : Array F), acc.size = n →
      (l.foldl step acc).size = n ∧
        ∀ s, s < n → toF ((l.foldl step acc).getD s 0) =
          toF (acc.getD s 0) + (l.map fun x => g x s).sum
  | [], acc, ha => ⟨ha, fun s _ => by simp⟩
  | x :: l, acc, ha => by
    obtain ⟨h1, h2⟩ := h acc x ha
    obtain ⟨h3, h4⟩ := adds_foldl h l (step acc x) h1
    refine ⟨h3, fun s hs => ?_⟩
    rw [List.foldl_cons, h4 s hs, h2 s hs, List.map_cons, List.sum_cons, add_assoc]

/-- A loop of such steps is such a step. -/
theorem adds_loop {α β : Type} {n : ℕ} (l : β → List α) {step : β → Array F → α → Array F}
    {g : β → α → ℕ → Cb.Gl.F} (h : ∀ b, Adds n (step b) (g b)) :
    Adds n (fun acc b => (l b).foldl (step b) acc) fun b s => ((l b).map fun x => g b x s).sum :=
  fun acc b ha => adds_foldl (h b) (l b) acc ha

/-- **The sums of limb products of one norm at one token**, in the base field. -/
theorem limbSums_word (Q : K4Pub) (w : K4In) (i t : ℕ) {s : ℕ} (hs : s < ledNS Q.P.y.h.xl) :
    toF ((limbSumsAt Q w i t).getD s 0) =
      ∑ j ∈ range Q.P.y.h.d, ∑ l ∈ range Q.P.y.h.xl, ∑ l' ∈ range Q.P.y.h.xl,
        if l + l' = s then
          toF (streamLimb Q.P.y w.cell (tensorOf Q.P.y "xs") i l j t) *
            toF (streamLimb Q.P.y w.cell (tensorOf Q.P.y "xs") i l' j t)
        else 0 := by
  have inner : ∀ (x : ℕ × ℕ), Adds (ledNS Q.P.y.h.xl)
      (fun (acc : Array F) lc => acc.modify (x.2 + lc) fun v =>
        addF v (mulF
          (((Array.range Q.P.y.h.xl).map fun lb =>
            streamLimb Q.P.y w.cell (tensorOf Q.P.y "xs") i lb x.1 t).getD x.2 0)
          (((Array.range Q.P.y.h.xl).map fun lb =>
            streamLimb Q.P.y w.cell (tensorOf Q.P.y "xs") i lb x.1 t).getD lc 0)))
      (fun lc s => if x.2 + lc = s then
        toF (((Array.range Q.P.y.h.xl).map fun lb =>
            streamLimb Q.P.y w.cell (tensorOf Q.P.y "xs") i lb x.1 t).getD x.2 0) *
          toF (((Array.range Q.P.y.h.xl).map fun lb =>
            streamLimb Q.P.y w.cell (tensorOf Q.P.y "xs") i lb x.1 t).getD lc 0)
        else 0) := by
    intro x acc lc ha
    refine ⟨by rw [Array.size_modify]; exact ha, fun s hs => ?_⟩
    rw [modify_getD _ _ _ _ (by rw [ha]; exact hs)]
    show toF (if x.2 + lc = s then _ else _) = _ + (if x.2 + lc = s then _ else 0)
    by_cases h : x.2 + lc = s
    · rw [if_pos h, if_pos h, Slice.toF_addF, Slice.toF_mulF]
    · rw [if_neg h, if_neg h, add_zero]
  have mid : ∀ j : ℕ, Adds (ledNS Q.P.y.h.xl) _ _ :=
    fun j => adds_loop (fun _ : ℕ => List.range Q.P.y.h.xl) fun lb => inner (j, lb)
  have outer := adds_loop (fun _ : ℕ => List.range Q.P.y.h.xl) mid
  have all := (adds_foldl outer (List.range Q.P.y.h.d)
    (Array.replicate (ledNS Q.P.y.h.xl) 0) Array.size_replicate).2 s hs
  have e0 : toF ((Array.replicate (ledNS Q.P.y.h.xl) (0 : F)).getD s 0) = 0 := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> exact Slice.toF_zero
  unfold limbSumsAt
  refine all.trans ?_
  rw [e0, zero_add, list_range_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [list_range_sum]
  refine sum_congr rfl fun l hl => ?_
  rw [list_range_sum]
  refine sum_congr rfl fun l' hl' => ?_
  rw [range_map_getD' _ _ _ (mem_range.mp hl), range_map_getD' _ _ _ (mem_range.mp hl')]

/-- **The same in the extension field: the library's sum W_s**, of the limbs as they read. -/
theorem limbSums_read (Q : K4Pub) (w : K4In) (i t : ℕ) (hxl : Q.P.y.h.xl = 5) {s : ℕ}
    (hs : s < 9) :
    Reading.gl.val (ofF ((limbSumsAt Q w i t).getD s 0)) =
      Inst.Model.Ledger.Wsum Q.P.y.h.d
        (fun l j => Reading.gl.val
          (ofF (streamLimb Q.P.y w.cell (tensorOf Q.P.y "xs") i l j t))) s := by
  have hNS : ledNS Q.P.y.h.xl = 9 := by rw [hxl]; rfl
  show Slice.readE _ = _
  rw [Slice.readE_ofF, limbSums_word Q w i t (by rw [hNS]; exact hs), hxl]
  unfold Inst.Model.Ledger.Wsum
  rw [map_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [map_sum]
  refine sum_congr rfl fun l' _ => ?_
  by_cases h : l + l' = s
  · rw [if_pos h, if_pos h, map_mul]
    show _ = Slice.readE _ * Slice.readE _
    rw [Slice.readE_ofF, Slice.readE_ofF]
  · rw [if_neg h, if_neg h, map_zero]

/-- **The loop over the tokens**: member s gathers, token by token, the word c t s times k t. -/
theorem tokens_read (n : ℕ) (c : ℕ → Array F) (k : ℕ → E) {s : ℕ} (hs : s < n) : ∀ T : ℕ,
    Reading.gl.val (((List.range T).foldl
      (fun (acc : Array E) t =>
        (Array.range n).map fun s => maddS (acc.getD s zeroE) ((c t).getD s 0) (k t))
      (Array.replicate n zeroE)).getD s zeroE) =
      ∑ t ∈ range T, Reading.gl.val (ofF ((c t).getD s 0)) * Reading.gl.val (k t)
  | 0 => by
    rw [List.range_zero, List.foldl_nil, Finset.sum_range_zero, Array.getD_eq_getD_getElem?,
      Array.getElem?_replicate, if_pos hs]
    exact Reading.gl.zero
  | T + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      range_map_getD' _ _ _ hs, gl_maddS, tokens_read n c k hs T, Finset.sum_range_succ]

/-- **A member of wSums is a sum over the tokens.** -/
theorem wSums_read (Q : K4Pub) (w : K4In) (p : Pts) {ν s : ℕ} (hν : ν < Q.P.y.NI)
    (hs : s < ledNS Q.P.y.h.xl) :
    Reading.gl.val ((wSums Q w p).getD (ledNS Q.P.y.h.xl * ν + s) zeroE) =
      ∑ t ∈ range Q.P.y.T, Reading.gl.val (ofF ((limbSumsAt Q w ν t).getD s 0)) *
        Reading.gl.val ((eqTab p.PV).getD t zeroE) := by
  have hlen : ∀ i : ℕ, (((List.range Q.P.y.T).foldl
      (fun (acc : Array E) t =>
        (Array.range (ledNS Q.P.y.h.xl)).map fun s =>
          maddS (acc.getD s zeroE) ((limbSumsAt Q w i t).getD s 0) ((eqTab p.PV).getD t zeroE))
      (Array.replicate (ledNS Q.P.y.h.xl) zeroE)).toList).length = ledNS Q.P.y.h.xl := by
    intro i
    rw [Array.length_toList]
    induction Q.P.y.T with
    | zero => exact Array.size_replicate
    | succ T _ =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Array.size_map,
        Array.size_range]
  unfold wSums
  rw [flat_getD _ _ hlen zeroE (List.range Q.P.y.NI) ν s (by rw [List.length_range]; exact hν) hs,
    List.getElem_range, toList_getD]
  exact tokens_read _ (fun t => limbSumsAt Q w ν t) (fun t => (eqTab p.PV).getD t zeroE) hs _

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.flat_getD
#print axioms OnBytes.Road.K4.C.toList_getD
#print axioms OnBytes.Road.K4.C.modify_getD
#print axioms OnBytes.Road.K4.C.adds_foldl
#print axioms OnBytes.Road.K4.C.adds_loop
#print axioms OnBytes.Road.K4.C.limbSums_word
#print axioms OnBytes.Road.K4.C.limbSums_read
#print axioms OnBytes.Road.K4.C.tokens_read
#print axioms OnBytes.Road.K4.C.wSums_read
