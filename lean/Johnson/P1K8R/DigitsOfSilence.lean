-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/DigitsOfSilence.lean: THE SMALLNESS TEST: WHERE THE LOOKUP's SECOND TEST ON ITS OWN
SAMPLES (`goodK3Out`, Johnson/Desc/ProofFile/Honest/K3/GoodDraws.lean) SAYS YES, WHAT THE DATA HOLD
AS HEARD AGREES WITH THESE SAMPLES IN THE ELEVEN OPEN FIELDS (`OpenSame`, `lookHeardAt`,
Johnson/Desc/ProofFile/Honest/K3/HeardWhole.lean), AND THREE TESTS ON PUBLIC NUMBERS PASS:
`digitsLive` (Johnson/Desc/K8/Honest/DigitsFew.lean) SAYS YES. Lemmas; NONE OF THE LIBRARY's GOALS.
Nothing on completeness, soundness or hiding.

ds, own: the lookup's own samples, by round, from its first round on. h: the lookup's shape.
  **`callWeight_ne`**   no coordinate that a call's weight reads has the value 0 or 1: the weight
      does not have the value 0
  `fold_fine`, **`layBack_fine`**   the order names each bit just once, there are challenges enough,
      none has the value 0 or 1: then no coordinate of the point that they are laid back into has
  **`keyPt_fine`**, `keyPt_size`   a yes of `goodK3Out (faceOf h) ds`, the last key level's order in
      order: no coordinate of the key side's last point has the value 0 or 1; the point has h.v
      coordinates
  `KeyFit tl`   on public numbers, by name: the key side has a level; its last level's order names
      each bit just once; there are two calls at least; each of the two calls' numbers of
      coordinates fits the shape's
  **`digits_of_silence`**   tl.heard = some g; g agrees with `lookHeardAt tl.f9 0 own` in the eleven
      fields; a yes of `goodK3Out (faceOf tl.f9) own`; the form of the key side's end names no
      entry; `KeyFit tl`, `piecesFit tl`, `digitsCover tl`: then `digitsLive tl` says yes
By: `digitsGood_of` (Johnson/Desc/K8/Honest/GoodOf.lean) · `digitsLive_of` (DigitsLiveOf.lean) ·
`fine_vals`, `chals_fine`, `out_spots` (Johnson/P1K8R/PlanesOfSilence.lean) · ProdV.pt_set,
size_set, layBack_size, orderOk_facts (Johnson/Desc/First/ProdV/LevelKit.lean).
Limits. The agreement, the form's emptiness and the three public tests are premises: that the state
in front of a segment's batching meets them is not shown here. Nothing on any measure.
-/
import Johnson.P1K8R.PlanesOfSilence
import Johnson.Desc.First.ProdV.LevelKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open ProofFile.Honest.K3 (LFace Spot goodK3Out spotsOut varChals elemAt roundAt firstRound lookHeardAt
  OpenSame ptsOf keyPtsOf keyPtsAt behind)

/-- The value is neither 0 nor 1. -/
def Fine (w : E) : Prop := Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1

theorem weight_fold (zy : Array E) (pre hi : Nat) : ∀ (l : List Nat) (e : E),
    Reading.gl.val e ≠ 0 → (∀ i ∈ l, Fine (zy.getD i zeroE)) →
    Reading.gl.val (l.foldl (fun e i =>
      let z := zy.getD i zeroE
      mulE e (if (pre / 2 ^ (hi - 1 - i)) % 2 = 1 then z else subE oneE z)) e) ≠ 0
  | [], _, he, _ => he
  | i :: l, e, he, h => by
    rw [List.foldl_cons]
    refine weight_fold zy pre hi l _ ?_ fun j hj => h j (List.mem_cons_of_mem _ hj)
    obtain ⟨h0, h1⟩ := h i List.mem_cons_self
    show Reading.gl.val (mulE e (if (pre / 2 ^ (hi - 1 - i)) % 2 = 1 then zy.getD i zeroE
      else subE oneE (zy.getD i zeroE))) ≠ 0
    rw [Reading.gl.mul]
    refine mul_ne_zero he ?_
    split
    · exact h0
    · rw [Reading.gl.sub, Reading.gl.one]
      exact sub_ne_zero.2 (Ne.symm h1)

/-- **A call's weight is not 0.** -/
theorem callWeight_ne (h : Forest.Shape) (zy : Array E) (c : Nat)
    (hz : ∀ i, i < h.rK - h.iota.getD c 0 → Fine (zy.getD i zeroE)) :
    Reading.gl.val (Forest.callWeight h zy c) ≠ 0 := by
  unfold Forest.callWeight
  refine weight_fold zy _ _ _ oneE ?_ fun i hi => hz i (List.mem_range.1 hi)
  rw [Reading.gl.one]
  exact one_ne_zero

/-- The fold of `layBack`: a place that is fine, or that a later pair names, ends fine. -/
theorem fold_fine (m : Nat) : ∀ (l : List (Nat × E)) (r : Array E), r.size = m →
    (∀ x ∈ l, x.1 < m ∧ Fine x.2) → ∀ pos,
    (Fine (r.getD pos zeroE) ∨ ∃ x ∈ l, m - 1 - x.1 = pos) →
    Fine ((l.foldl (fun (r : Array E) x => r.set! (m - 1 - x.1) x.2) r).getD pos zeroE)
  | [], _, _, _, _, h => by
    rcases h with h | ⟨x, hx, -⟩
    · exact h
    · exact absurd hx List.not_mem_nil
  | y :: l, r, hr, hl, pos, h => by
    rw [List.foldl_cons]
    obtain ⟨hy1, hy2⟩ := hl y List.mem_cons_self
    have hj : m - 1 - y.1 < r.size := by omega
    have hp := congrFun (ProdV.pt_set Reading.gl r (m - 1 - y.1) y.2 hj) pos
    refine fold_fine m l _ (by rw [ProdV.size_set, hr])
      (fun x hx => hl x (List.mem_cons_of_mem _ hx)) pos ?_
    by_cases hpos : pos = m - 1 - y.1
    · left
      have e : Reading.gl.val ((r.set! (m - 1 - y.1) y.2).getD pos zeroE) = Reading.gl.val y.2 := by
        have hp' : Reading.gl.val ((r.set! (m - 1 - y.1) y.2).getD pos zeroE) =
          Function.update (ProdV.pt Reading.gl r) (m - 1 - y.1) (Reading.gl.val y.2) pos := hp
        rw [hp', hpos, Function.update_self]
      unfold Fine
      rw [e]
      exact hy2
    · have e : Reading.gl.val ((r.set! (m - 1 - y.1) y.2).getD pos zeroE) =
          Reading.gl.val (r.getD pos zeroE) := by
        have hp' : Reading.gl.val ((r.set! (m - 1 - y.1) y.2).getD pos zeroE) =
          Function.update (ProdV.pt Reading.gl r) (m - 1 - y.1) (Reading.gl.val y.2) pos := hp
        rw [hp', Function.update_of_ne hpos]
        rfl
      rcases h with h | ⟨x, hx, hxp⟩
      · left
        unfold Fine at h ⊢
        rw [e]
        exact h
      · rcases List.mem_cons.1 hx with rfl | hx'
        · exact absurd hxp.symm hpos
        · exact Or.inr ⟨x, hx', hxp⟩

/-- **The point that the challenges are laid back into.** -/
theorem layBack_fine (m : Nat) (order : List Nat) (cs : List E)
    (ho : ProdV.orderOk m order = true) (hc : m ≤ cs.length) (hf : ∀ w ∈ cs, Fine w) :
    ∀ w ∈ (ProdV.layBack m order cs).toList, Fine w := by
  obtain ⟨h1, h2, h3⟩ := ProdV.orderOk_facts ho
  intro w hw
  obtain ⟨pos, hpos, rfl⟩ := List.mem_iff_getElem.1 hw
  have hsz : (ProdV.layBack m order cs).size = m := ProdV.layBack_size m order cs
  have hpm : pos < m := by
    rw [Array.length_toList, hsz] at hpos
    exact hpos
  have hb : m - 1 - pos ∈ order := List.count_pos_iff.1 (by rw [h3 _ (by omega)]; exact Nat.one_pos)
  obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.1 hb
  have hjc : j < cs.length := by omega
  have hz : (m - 1 - pos, cs[j]) ∈ order.zip cs := by
    refine List.mem_iff_getElem.2 ⟨j, by rw [List.length_zip]; omega, ?_⟩
    rw [List.getElem_zip, hjb]
  have key := fold_fine m (order.zip cs) (Array.replicate m zeroE) (by simp)
    (fun x hx => ⟨h2 _ (List.of_mem_zip hx).1, hf _ (List.of_mem_zip hx).2⟩) pos
    (Or.inr ⟨_, hz, by show m - 1 - (m - 1 - pos) = pos; omega⟩)
  have e : (ProdV.layBack m order cs).toList[pos] =
      (ProdV.layBack m order cs).getD pos zeroE := by
    rw [ProdV.getD_toList, List.getD_eq_getElem _ _ hpos]
  rw [e]
  exact key

/-- **The key side's last point.** -/
theorem keyPt_fine (h : Forest.Shape) (ds : List Fmt.Drawn) (m : Nat) (hv : h.v = m + 1)
    (ho : ProdV.orderOk m (K3.keyOrders h m) = true) (hg : goodK3Out (K3.faceOf h) ds = true) :
    ∀ w ∈ ((ptsOf (K3.faceOf h) 0 ds).keyPt 0 h.v).toList, Fine w := by
  rw [hv]
  show ∀ w ∈ (#[elemAt ds (roundAt (K3.faceOf h) 0 (.keyLine 0 m))] ++
    ProdV.layBack m (K3.keyOrders h m) (varChals (K3.faceOf h) 0 ds (.key 0 m) m)).toList, Fine w
  have hsp := out_spots (K3.faceOf h) ds hg
  have hmem : ∀ p : Spot, p ∈ ((List.range (h.v - 1)).map
      (fun l => (⟨.key 0 (h.v - 1), 1 + l, 0, true⟩ : Spot)) ++
      [⟨.keyLine 0 (h.v - 1), 0, 0, true⟩]) → p ∈ spotsOut (K3.faceOf h) := by
    intro p hp
    unfold spotsOut
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
    show p ∈ ([h.v].zipIdx.flatMap _)
    simpa using hp
  have hm1 : h.v - 1 = m := by omega
  rw [hm1] at hmem
  intro w hw
  rw [Array.toList_append] at hw
  rcases List.mem_append.1 hw with hw | hw
  · obtain rfl : w = elemAt ds (roundAt (K3.faceOf h) 0 (.keyLine 0 m)) := by simpa using hw
    have hf := fine_vals (K3.faceOf h) ds (.keyLine 0 m) 0
      (hsp _ (hmem _ (List.mem_append_right _ (List.mem_singleton.2 rfl))))
    have e : roundAt (K3.faceOf h) 0 (.keyLine 0 m) =
        firstRound (K3.faceOf h) (.keyLine 0 m) + 0 := by
      unfold roundAt
      omega
    rw [e]
    exact hf
  · refine layBack_fine m _ _ ho (by unfold varChals; simp) ?_ w hw
    exact chals_fine (K3.faceOf h) ds (.key 0 m) m fun l hl =>
      hsp _ (hmem _ (List.mem_append_left _ (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩)))

theorem keyPt_size (h : Forest.Shape) (ds : List Fmt.Drawn) (m : Nat) (hv : h.v = m + 1) :
    ((ptsOf (K3.faceOf h) 0 ds).keyPt 0 h.v).size = h.v := by
  rw [hv]
  show (#[elemAt ds (roundAt (K3.faceOf h) 0 (.keyLine 0 m))] ++
    ProdV.layBack m (K3.keyOrders h m) (varChals (K3.faceOf h) 0 ds (.key 0 m) m)).size = m + 1
  rw [Array.size_append, ProdV.layBack_size]
  simp
  omega

/-- On public numbers, by name. -/
structure KeyFit (tl : HTailF2) : Prop where
  level : 0 < tl.f9.v
  order : ProdV.orderOk (tl.f9.v - 1) (K3.keyOrders tl.f9 (tl.f9.v - 1)) = true
  calls : 2 ≤ tl.f9.NC
  iota : ∀ q, q < 2 → tl.f9.iota.getD q 0 ≤ tl.f9.rK
  fits : ∀ q, q < 2 → tl.f9.iota.getD q 0 + tl.f9.dT = (tl.zOf q).call.n

theorem look_e (h : Forest.Shape) (ds : List Fmt.Drawn) :
    (lookHeardAt h 0 ds).e = (Array.range h.NC).map (Forest.callWeight h
      (((ptsOf (K3.faceOf h) 0 ds).keyPt 0 h.v).extract h.dT
        ((ptsOf (K3.faceOf h) 0 ds).keyPt 0 h.v).size)) := rfl

theorem look_zk (h : Forest.Shape) (ds : List Fmt.Drawn) :
    (lookHeardAt h 0 ds).zk = (Array.range h.NC).map fun c =>
      ((((ptsOf (K3.faceOf h) 0 ds).keyPt 0 h.v).extract h.dT
        ((ptsOf (K3.faceOf h) 0 ds).keyPt 0 h.v).size).extract (h.rK - h.iota.getD c 0)
        (((ptsOf (K3.faceOf h) 0 ds).keyPt 0 h.v).extract h.dT
          ((ptsOf (K3.faceOf h) 0 ds).keyPt 0 h.v).size).size) ++
        ((ptsOf (K3.faceOf h) 0 ds).keyPt 0 h.v).extract 0 h.dT := rfl

theorem map_range_getD {α : Type} (n q : Nat) (f : Nat → α) (d : α) (hq : q < n) :
    ((Array.range n).map f).getD q d = f q := by
  simp [Array.getD_eq_getD_getElem?, hq]

theorem getD_mem (a : Array E) (i : Nat) (h : i < a.size) : a.getD i zeroE ∈ a.toList := by
  rw [ProdV.getD_toList, List.getD_eq_getElem _ _ (by rw [Array.length_toList]; exact h)]
  exact List.getElem_mem _

/-- **From the second test's yes to `digitsLive`.** -/
theorem digits_of_silence (tl : HTailF2) (g : Forest.Heard) (own : List Fmt.Drawn)
    (hg : tl.heard = some g) (ho : OpenSame g (lookHeardAt tl.f9 0 own))
    (hs : goodK3Out (K3.faceOf tl.f9) own = true) (hc : g.cEnd.ents.isEmpty = true)
    (K : KeyFit tl) (hP : piecesFit tl = true) (hC : digitsCover tl = true) :
    digitsLive tl = true := by
  obtain ⟨m, hv⟩ : ∃ m, tl.f9.v = m + 1 := ⟨tl.f9.v - 1, by have := K.level; omega⟩
  have hm : tl.f9.v - 1 = m := by omega
  have hord := K.order
  rw [hm] at hord
  have hfine := keyPt_fine tl.f9 own m hv hord hs
  have hsize := keyPt_size tl.f9 own m hv
  have hvd : tl.f9.v = tl.f9.dT + tl.f9.rK := rfl
  have he := ho.e.trans (look_e tl.f9 own)
  have hk := ho.zk.trans (look_zk tl.f9 own)
  obtain ⟨p0, hp0⟩ : ∃ p0, p0 = (ptsOf (K3.faceOf tl.f9) 0 own).keyPt 0 tl.f9.v := ⟨_, rfl⟩
  rw [← hp0] at he hk hfine hsize
  have hNC := K.calls
  refine digitsLive_of tl g hg hC (digitsGood_of tl g hc ?_ ?_ ?_ hP)
  · intro q hq
    rw [he, map_range_getD _ _ _ _ (by omega)]
    refine callWeight_ne _ _ _ fun i hi => ?_
    have hsz : (p0.extract tl.f9.dT p0.size).size = tl.f9.rK := by
      rw [Array.size_extract, hsize]
      omega
    exact hfine _ (mem_extract _ _ _ _ (getD_mem _ i (by omega)))
  · intro q hq w hw
    rw [hk, map_range_getD _ _ _ _ (by omega), Array.toList_append] at hw
    rcases List.mem_append.1 hw with hw | hw
    · exact hfine _ (mem_extract _ _ _ _ (mem_extract _ _ _ _ hw))
    · exact hfine _ (mem_extract _ _ _ _ hw)
  · intro q hq
    have h1 := K.iota q hq
    have h2 := K.fits q hq
    rw [hk, map_range_getD _ _ _ _ (by omega), Array.size_append, Array.size_extract,
      Array.size_extract, Array.size_extract, hsize]
    omega

end P1K8

#print axioms P1K8.Fine
#print axioms P1K8.weight_fold
#print axioms P1K8.callWeight_ne
#print axioms P1K8.fold_fine
#print axioms P1K8.layBack_fine
#print axioms P1K8.keyPt_fine
#print axioms P1K8.keyPt_size
#print axioms P1K8.KeyFit
#print axioms P1K8.look_e
#print axioms P1K8.look_zk
#print axioms P1K8.map_range_getD
#print axioms P1K8.getD_mem
#print axioms P1K8.digits_of_silence
