-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/OffPlanes.lean: CONDITIONAL.

Not shown here. That a form's entries lie in front of the first place of the family "b-bits-0": a
hypothesis (hlt), one inequality between public numbers for each entry. That layTables and funsOf
return. No example is known. No property is claimed.

ONE WAY TO SHOW THAT A FORM's ENTRIES LIE OFF THE MATRIX OF THE LOOKUP's PLANES, which the laws of
ValAff.lean ask (hG). The three families on that matrix are the last three of the verifier's list
(tableAsks, OnBytes/Model/LayerForms.lean), and the families lie one behind the other. So a place
in front of the first of the three belongs to a table on another matrix.

  parts_mat      a part's matrix lies among the family's.
  pre_off, pre_of_named   no part of a family in front of the three stands on the planes' matrix;
                 a family with none of the three names stands in front of them.
  off_of_named   a part of a family with none of the three names stands off that matrix.
  laid_split, laid_first_ge, laid_head   lists of families that lie one behind the other.
  planes_last    no family with one of the three names begins in front of the family "b-bits-0".
  off_of_lt      a table that has a place in front of that family stands off the planes' matrix.
  hG_of_lt       the hypothesis hG of ValAff.lean, at G := off the planes' matrix.
-/
import Johnson.Road.K4.C.ReadsKit
import Johnson.Road.K4.C.Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Reads Env TableAsk TableAt layParts layTables tableAsks funsOf matIx)
open OnBytes.Desc.First.K4.Honest (K4Pub matsOf)

/-- A part's matrix lies among the family's. n: the parts still to lay. -/
theorem parts_mat (mats : Array (ℕ × ℕ)) (a : TableAsk) : ∀ n p, n ≤ a.parts →
    ∀ m ∈ (layParts mats a n p).1, a.M0 ≤ m.1 ∧ m.1 < a.M0 + a.parts
  | 0, _, _, m, hm => by cases hm
  | n + 1, p, hn, m, hm => by
    rw [layParts_step] at hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨Nat.le_add_right _ _, by show a.M0 + (a.parts - (n + 1)) < _; omega⟩
    · exact parts_mat mats a n _ (by omega) m hm

/-- No part of a family in front of the three stands on the planes' matrix. -/
theorem pre_off {y : Lay} {rd : Reads} {g : ℕ} {a : TableAsk} (ha : a ∈ Fo.preAsks y rd g) {M : ℕ}
    (h1 : a.M0 ≤ M) (h2 : M < a.M0 + a.parts) : M ≠ (matIx y).iB := by
  have eB : (matIx y).iB = y.parts.getD 0 0 + y.parts.getD 1 0 + 1 := rfl
  have fam : ∀ (mn : String) (M0 parts : ℕ) (pts : List String) (lng : Bool),
      a ∈ Fo.famAsks y mn M0 parts pts lng → a.M0 = M0 ∧ a.parts = parts := by
    intro mn M0 parts pts lng hb
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hb
    exact ⟨rfl, rfl⟩
  unfold Fo.preAsks at ha
  simp only [List.mem_append] at ha
  rw [eB]
  rcases ha with ((((((hb | hb) | hb) | hb) | hb) | hb) | hb) | hb
  · obtain ⟨e1, e2⟩ := fam _ _ _ _ _ hb
    have e0 : (matIx y).iAF = 0 := rfl
    omega
  · obtain ⟨e1, e2⟩ := fam _ _ _ _ _ hb
    have e0 : (matIx y).iQA = y.parts.getD 0 0 + y.parts.getD 1 0 + 2 := rfl
    omega
  · obtain ⟨e1, e2⟩ := fam _ _ _ _ _ hb
    have e0 : (matIx y).iXI = y.parts.getD 0 0 + y.parts.getD 1 0 + 4 := rfl
    omega
  · split at hb
    · obtain ⟨e1, e2⟩ := fam _ _ _ _ _ hb
      have e0 : (matIx y).iXI = y.parts.getD 0 0 + y.parts.getD 1 0 + 4 := rfl
      omega
    · exact absurd hb List.not_mem_nil
  · obtain ⟨e1, e2⟩ := fam _ _ _ _ _ hb
    have e0 : (matIx y).iXO = y.parts.getD 0 0 + y.parts.getD 1 0 + 3 := rfl
    omega
  · obtain ⟨e1, e2⟩ := fam _ _ _ _ _ hb
    have e0 : (matIx y).iAD = y.parts.getD 0 0 := rfl
    omega
  · obtain ⟨e1, e2⟩ := fam _ _ _ _ _ hb
    have e0 : (matIx y).iAR = y.parts.getD 0 0 + y.parts.getD 1 0 := rfl
    omega
  · split at hb
    · obtain ⟨e1, e2⟩ := fam _ _ _ _ _ hb
      have e0 : (matIx y).iQA = y.parts.getD 0 0 + y.parts.getD 1 0 + 2 := rfl
      omega
    · exact absurd hb List.not_mem_nil

/-- A family of the verifier's list with none of the three names stands in front of the three. -/
theorem pre_of_named {y : Lay} {rd : Reads} {g : ℕ} {a : TableAsk} (ha : a ∈ tableAsks y rd g)
    (hn : Named a) : a ∈ Fo.preAsks y rd g := by
  rw [Fo.tableAsks_eq] at ha
  rcases List.mem_append.mp ha with h | h
  · exact h
  · exfalso
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact absurd hn.1 (by simp [Fo.planeAsk])
    · exact absurd hn.2.1 (by simp [Fo.planeAsk])
    · exact absurd hn.2.2 (by simp [Fo.planeAsk])

variable {Q : K4Pub} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- **A part of a family with none of the three names stands off the planes' matrix.** -/
theorem off_of_named (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    {q : TableAsk × List (ℕ × ℕ)} (hq : q ∈ r.2.1) {m : ℕ × ℕ} (hmq : m ∈ q.2) (hn : Named q.1) :
    m.1 ≠ (matIx Q.P.y).iB := by
  obtain ⟨L1, L2⟩ := laid_of_layTables _ _ _ _ hl
  obtain ⟨p1, -⟩ := laid_mem (matsOf Q) r.2.1 0 L1 q hq
  have hask : q.1 ∈ tableAsks Q.P.y Q.P.rd Q.g := by
    rw [← L2]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  rw [p1] at hmq
  obtain ⟨h1, h2⟩ := parts_mat (matsOf Q) q.1 q.1.parts _ (Nat.le_refl _) m hmq
  exact pre_off (pre_of_named hask hn) h1 h2

/-- The hind part of such a list is such a list. -/
theorem laid_split (mats : Array (ℕ × ℕ)) : ∀ (l1 l2 : List (TableAsk × List (ℕ × ℕ))) (p : ℕ),
    Laid mats (l1 ++ l2) p → ∃ p2, Laid mats l2 p2
  | [], _, p, h => ⟨p, h⟩
  | _ :: l1, l2, _, h => laid_split mats l1 l2 _ h.2.2

/-- No family of such a list begins in front of the list. -/
theorem laid_first_ge (mats : Array (ℕ × ℕ)) : ∀ (l : List (TableAsk × List (ℕ × ℕ))) (p : ℕ),
    Laid mats l p → ∀ q ∈ l, p ≤ famFirst q
  | [], _, _, q, hq => by cases hq
  | x :: l, p, hL, q, hq => by
    obtain ⟨e1, e2, e3⟩ := hL
    rcases List.mem_cons.mp hq with rfl | hq
    · have f1 : famFirst q = p := by
        unfold famFirst
        rw [e1]
        exact parts_first mats q.1 q.1.parts p e2
      omega
    · have := laid_first_ge mats l _ e3 q hq
      omega

/-- The first family begins where the list begins. -/
theorem laid_head (mats : Array (ℕ × ℕ)) {x : TableAsk × List (ℕ × ℕ)}
    {l : List (TableAsk × List (ℕ × ℕ))} {p : ℕ} (hL : Laid mats (x :: l) p) : famFirst x = p := by
  obtain ⟨e1, e2, -⟩ := hL
  unfold famFirst
  rw [e1]
  exact parts_first mats x.1 x.1.parts p e2

/-- **No family with one of the three names begins in front of the family "b-bits-0".** -/
theorem planes_last (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    {q0 : TableAsk × List (ℕ × ℕ)} (h0 : q0 ∈ r.2.1) (e0 : q0.1 = Fo.planeAsk Q.P.y "b-bits-0") :
    ∀ q ∈ r.2.1, ¬ Named q.1 → famFirst q0 ≤ famFirst q := by
  obtain ⟨L1, L2⟩ := laid_of_layTables _ _ _ _ hl
  rw [Fo.tableAsks_eq] at L2
  obtain ⟨l1, l2, e, m1, m2⟩ := List.map_eq_append_iff.mp L2
  rw [e] at L1
  obtain ⟨p2, L3⟩ := laid_split _ l1 l2 0 L1
  have pre : ∀ q ∈ l1, Named q.1 := by
    intro q h
    have hp : q.1 ∈ Fo.preAsks Q.P.y Q.P.rd Q.g := by
      rw [← m1]
      exact List.mem_map.mpr ⟨q, h, rfl⟩
    exact ⟨beq_eq_false_iff_ne.mpr (Fo.ask_ne hp _ (by decide)),
      beq_eq_false_iff_ne.mpr (Fo.ask_ne hp _ (by decide)),
      beq_eq_false_iff_ne.mpr (Fo.ask_ne hp _ (by decide))⟩
  obtain ⟨x0, t0, rfl, -, m3⟩ := List.map_eq_cons_iff.mp m2
  obtain ⟨x1, t1, rfl, a1, m4⟩ := List.map_eq_cons_iff.mp m3
  obtain ⟨x2, t2, rfl, a2, m5⟩ := List.map_eq_cons_iff.mp m4
  obtain rfl := List.map_eq_nil_iff.mp m5
  have hq0 : q0 = x0 := by
    rw [e] at h0
    rcases List.mem_append.mp h0 with h | h
    · exfalso
      have hn := (pre q0 h).1
      rw [e0] at hn
      exact absurd hn (by simp [Fo.planeAsk])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h
      · exact h
      · exfalso
        rw [h, a1] at e0
        have : ("b-bits-1" : String) = "b-bits-0" := congrArg TableAsk.name e0
        exact absurd this (by decide)
      · exfalso
        rw [h, a2] at e0
        have : ("b-pin" : String) = "b-bits-0" := congrArg TableAsk.name e0
        exact absurd this (by decide)
  intro q hq hn
  rw [e] at hq
  rcases List.mem_append.mp hq with h | h
  · exact absurd (pre q h) hn
  · rw [hq0, laid_head _ L3]
    exact laid_first_ge _ _ _ L3 q h

variable {fo' : Forest.Heard} {pts : List (String × Array E)} {tl : HTailF2} {funs : Array HFun}

/-- **A table that has a place in front of every family with one of the three names stands off the
planes' matrix.** tB0: a place in front of which none of these begins. -/
theorem off_of_lt (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hf : funsOf Q.P.y fo' pts r.2.1 = some funs) {tB0 pos : ℕ}
    (hB : ∀ q ∈ r.2.1, ¬ Named q.1 → tB0 ≤ famFirst q) (hlt : pos < tB0) :
    ∀ z : HFun × ℕ × ℕ, z.1 ∈ funs → tl.tabAt z.1 z.2.1 z.2.2 = some pos →
      z.1.mat ≠ (matIx Q.P.y).iB := by
  intro z hz hzp
  obtain ⟨L1, -⟩ := laid_of_layTables _ _ _ _ hl
  obtain ⟨t, ht, phi, -, e⟩ := funsOf_inv hf hz
  obtain ⟨q, hq, hm'⟩ := List.mem_flatMap.mp ht
  obtain ⟨m, hmq, rfl⟩ := List.mem_map.mp hm'
  obtain ⟨-, -, -, -, hp⟩ := tailAt_inv tl _ hzp
  rw [e] at hp ⊢
  have hp' : pos = m.2 + z.2.1 * ((tl.mats.getD m.1 {}).m / q.1.L) + z.2.2 := hp
  obtain ⟨p1, -⟩ := laid_mem (matsOf Q) r.2.1 0 L1 q hq
  have hmq' := hmq
  rw [p1] at hmq'
  obtain ⟨g1, -⟩ := parts_ge (matsOf Q) q.1 q.1.parts _ m hmq'
  by_cases hn : Named q.1
  · exact off_of_named hl hq hmq hn
  · have := hB q hq hn
    omega

/-- **The hypothesis hG of ValAff.lean**, at G := off the planes' matrix: from one inequality for
each entry. tB0: the first place of the family "b-bits-0", as the verifier's structure has it. -/
theorem hG_of_lt (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hf : funsOf Q.P.y fo' pts r.2.1 = some funs) {v : Env} (hv : v.tab = r.1) {tB0 : ℕ}
    (hB : v.tabAt "b-bits-0" = some tB0) {a : Aff}
    (hlt : ∀ x ∈ a.ents.toList, x.row * v.K3 + x.idx < tB0) :
    ∀ x ∈ a.ents.toList, ∀ z : HFun × ℕ × ℕ, z.1 ∈ funs →
      tl.tabAt z.1 z.2.1 z.2.2 = some (x.row * v.K3 + x.idx) → z.1.mat ≠ (matIx Q.P.y).iB := by
  have hl' : layTables (matsOf Q) (Fo.preAsks Q.P.y Q.P.rd Q.g ++ Fo.planeAsk Q.P.y "b-bits-0" ::
      [Fo.planeAsk Q.P.y "b-bits-1", Fo.planeAsk Q.P.y "b-pin"]) 0 = some (r.1, r.2.1, r.2.2) := hl
  obtain ⟨p0, hp0, hmem⟩ := Fo.lay_find (matsOf Q) (Fo.planeAsk Q.P.y "b-bits-0") rfl _ _ 0 _ _ _
    (fun b hb => Fo.ask_ne hb "b-bits-0" (by decide)) hl'
  have hB' : (r.1.find? fun t => t.name == "b-bits-0").map (·.first) = some tB0 := by
    rw [← hv]
    exact hB
  obtain rfl : tB0 = p0 := Option.some.inj (hB'.symm.trans hp0)
  intro x hx
  exact off_of_lt hl hf (planes_last hl hmem rfl) (hlt x hx)

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.parts_mat
#print axioms OnBytes.Road.K4.C.pre_off
#print axioms OnBytes.Road.K4.C.pre_of_named
#print axioms OnBytes.Road.K4.C.off_of_named
#print axioms OnBytes.Road.K4.C.laid_split
#print axioms OnBytes.Road.K4.C.laid_first_ge
#print axioms OnBytes.Road.K4.C.laid_head
#print axioms OnBytes.Road.K4.C.planes_last
#print axioms OnBytes.Road.K4.C.off_of_lt
#print axioms OnBytes.Road.K4.C.hG_of_lt
