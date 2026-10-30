-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/WeighedScope.lean: weighedOf never refuses on the placing rule's own placing:
so the premise hw of the bridge from a lookup's calls to a group's key vectors is struck too. A
theorem on every layout that the verifier returns under the switches; nothing is evaluated.

weighedOf (OnBytes/Model/LayerForms.lean:591) marks, layer after layer, the columns that a call's
segments list, and refuses if a column is marked twice or lies outside the call. The columns are
laid by the rule place (OnBytes/Model/Calls.lean:100). For the head's like marking the library has
shown that the rule's own placing is never refused (place_marks,
Johnson/Road/HeadCallsLaid.lean:367): the pieces' ranges of columns rise without overlap, a
segment's columns rise strictly inside its own pieces, and all lie below the call's number of
columns. The same facts serve here.
  marks_some: a marking of indices that are all different, unmarked and inside the array returns:
    the converse of marks_spec (Johnson/Road/FormsKeysRun8.lean:365).
  cols_of_place: the columns that a placed call's segments list on a layer are all different and lie
    below the call's number of columns.
  weighed_of_place: weighedOf returns on every placed call whose segments are shorter than 2^41.
  weighed_of_layout: so it returns on every call of every layout that the verifier returns under the
    switches, in every environment.
  weighed_in_scope: Weighed X (Johnson/Goal/Meaning/HlScope.lean).
  layerKeys_of_scope, layerOrd_of_scope, layerOrds_of_scope: from the lookup's own clause ForInG to
    LayerKeys, and the layers' joint, under the three facts on the files and g < 12 ALONE.
-/
import Johnson.Goal.Meaning.HlScope
import Johnson.Road.HeadCallsLaid
import Johnson.Road.FormsKeysRun8

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.P34

open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.L5
open OnBytes.Model (SegAsk topBit piecesBelow place CallD Seg)
open OnBytes.Model.Layer (Env Lay Shape layout)
open OnBytes.Model.Verify (publicOf Public layerShape)
open Inst.Model (Mat)

/-! ## A marking of indices that are apart returns -/

theorem marks_some : ∀ (l : List ℕ) (w : Array Bool), (∀ i ∈ l, w.getD i true = false) →
    l.Nodup → ∃ w', l.foldlM markAt w = some w'
  | [], w, _, _ => ⟨w, by simp⟩
  | i :: l, w, h, hn => by
    have hi : w.getD i true = false := h i List.mem_cons_self
    obtain ⟨hni, hnl⟩ := List.nodup_cons.mp hn
    obtain ⟨w', hw'⟩ := marks_some l (w.setIfInBounds i true)
      (fun k hk => by
        by_contra hc
        have hc' : (w.setIfInBounds i true).getD k true = true := by simpa using hc
        rcases (getD_marked w i k).mp hc' with a | a
        · rw [h k (List.mem_cons_of_mem _ hk)] at a
          cases a
        · exact hni (a ▸ hk)) hnl
    have e : markAt w i = some (w.setIfInBounds i true) := by
      unfold markAt
      rw [hi]
      rfl
    refine ⟨w', ?_⟩
    rw [List.foldlM_cons, e]
    exact hw'

/-! ## The columns of a placed call -/

/-- A member of an array's list stands at a place of the array. -/
theorem mem_at {a : Array ℕ} {j : ℕ} (h : j ∈ a.toList) : ∃ x, x < a.size ∧ a.getD x 0 = j := by
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem h
  have hi' : i < a.size := by simpa using hi
  refine ⟨i, hi', ?_⟩
  rw [← e]
  simp [Array.getD, hi']

/-- An array that rises strictly lists nothing twice. -/
theorem rising_nodup {a : Array ℕ} {Q : ℕ → Prop} {top : ℕ} (R : Hd.Rising a Q top) :
    a.toList.Nodup := by
  have hp : a.toList.Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hi' : i < a.size := by simpa using hi
    have hj' : j < a.size := by simpa using hj
    have y := R.mono i j hij hj'
    simpa [Array.getD, hi', hj'] using y
  exact hp.imp fun h => Nat.ne_of_lt h

/-- The first free column lies within the call. -/
theorem free_le_J (name kind : String) (asks : List SegAsk) (fl : ℕ) :
    (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).2 ≤ (place name kind asks fl).J := by
  show (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).2 ≤
    2 ^ max (ceilLog2 (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).2) fl
  exact Nat.le_trans (le_two_pow_ceilLog2 _)
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_max_left _ _))

/-- The columns that a placed call's segments list on a layer. -/
theorem cols_of_place (v : Env) (name kind : String) (asks : List SegAsk) (fl : ℕ)
    (hlen : ∀ a ∈ asks, a.2.1 < 2 ^ (topBit + 1)) (lam : ℕ) :
    (colsOn v (place name kind asks fl) lam).Nodup ∧
      ∀ j ∈ colsOn v (place name kind asks fl) lam, j < (place name kind asks fl).J := by
  have hT := Hd.ranged_piecesBelow (asks.map (·.2.1)) (topBit + 1) 0
  constructor
  · unfold colsOn
    rw [Hd.place_segs_eq]
    refine List.nodup_flatMap.mpr ⟨fun s hs => ?_, ?_⟩
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hs
      split
      · exact List.nodup_nil
      · exact rising_nodup (Hd.segAt_rising asks hlen z hz).2
    · rw [List.pairwise_map]
      refine List.Pairwise.imp_of_mem ?_ (Hd.zipIdx_rising asks 0)
      intro z z' hz hz' hlt j hj hj'
      have r1 := (Hd.segAt_rising asks hlen z hz).2
      have r2 := (Hd.segAt_rising asks hlen z' hz').2
      dsimp only at hj hj'
      split at hj
      · cases hj
      · split at hj'
        · cases hj'
        · obtain ⟨x, hx, ex⟩ := mem_at hj
          obtain ⟨x', hx', ex'⟩ := mem_at hj'
          have q1 := r1.inQ x hx
          have q2 := r2.inQ x' hx'
          rw [ex] at q1
          rw [ex'] at q2
          exact Hd.inPiece_apart hT (Nat.ne_of_lt hlt) q1 q2
  · intro j hj
    obtain ⟨s, hs, -, hjs⟩ := mem_colsOn.mp hj
    rw [Hd.place_segs_eq] at hs
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hs
    obtain ⟨x, hx, ex⟩ := mem_at hjs
    have y := (Hd.segAt_rising asks hlen z hz).2.lt x hx
    rw [ex] at y
    exact Nat.lt_of_lt_of_le y (free_le_J name kind asks fl)

/-! ## weighedOf returns -/

/-- From the two facts on a call's columns. -/
theorem weighed_of_cols (v : Env) (c : CallD)
    (H : ∀ lam, (colsOn v c lam).Nodup ∧ ∀ j ∈ colsOn v c lam, j < c.J) :
    ∃ wg, v.weighedOf c = some wg := by
  rw [weighedOf_eq]
  refine marks_some _ _ ?_ ?_
  · intro i hi
    unfold marksOn at hi
    obtain ⟨lam, hlam, hi⟩ := List.mem_flatMap.mp hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have h1 : lam < v.y.Lam := List.mem_range.mp hlam
    have h2 := (H lam).2 j hj
    have h3 : (lam + 1) * c.J ≤ v.y.Lam * c.J := Nat.mul_le_mul_right _ h1
    rw [Nat.succ_mul] at h3
    have h4 : lam * c.J + j < v.y.Lam * c.J := by omega
    simp [Array.getD, h4]
  · unfold marksOn
    refine List.nodup_flatMap.mpr ⟨fun lam _ => ?_, ?_⟩
    · exact (H lam).1.map fun a b hab => Nat.add_left_cancel hab
    · refine List.Pairwise.imp ?_ List.pairwise_lt_range
      intro lam lam' hlt i hi hi'
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      obtain ⟨j', hj', e⟩ := List.mem_map.mp hi'
      have h2 := (H lam).2 j hj
      have h3 : (lam + 1) * c.J ≤ lam' * c.J := Nat.mul_le_mul_right _ hlt
      rw [Nat.succ_mul] at h3
      have e' : lam' * c.J + j' = lam * c.J + j := e
      omega

/-- weighedOf never refuses on the rule's own placing, for segments of lengths below 2^41. -/
theorem weighed_of_place (v : Env) (name kind : String) (asks : List SegAsk) (fl : ℕ)
    (hlen : ∀ a ∈ asks, a.2.1 < 2 ^ (topBit + 1)) :
    ∃ wg, v.weighedOf (place name kind asks fl) = some wg :=
  weighed_of_cols v _ (cols_of_place v name kind asks fl hlen)

/-- weighedOf RETURNS ON EVERY CALL OF EVERY LAYOUT THAT THE VERIFIER RETURNS under the switches, in
every environment. -/
theorem weighed_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (S : Switches h) (v : Env) :
    ∀ cd ∈ y.calls, ∃ wg, v.weighedOf cd = some wg := by
  intro cd hcd
  have A := admitted_of_layout hy S.p3
  obtain ⟨cl, taken, ht, -, hc⟩ := A.calls
  rw [hc] at hcd
  have hcd' : cd ∈ taken.1.map fun c => place c.1 c.2.1 c.2.2 (h.nmin - h.ll - h.lt) :=
    Array.mem_def.mp hcd
  obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hcd'
  refine weighed_of_place v _ _ _ _ fun a ha => ?_
  obtain ⟨q, hq, rfl⟩ := takeCalls_mem _ cl [] [] taken ht c hcm a ha
  obtain ⟨fam, -, f2, -⟩ := segmentList_fam h S q hq
  show q.2.2.1 < 2 ^ (topBit + 1)
  rw [f2]
  exact len_lt A fam

/-! ## In scope -/

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- hw, at all public files in the goals' scope. -/
theorem weighed_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : Weighed X := by
  have B := Hd.public_of_core h (Hd.core_of_scope hZ hR h)
  exact weighed_of_layout B.lay B.switches _

/-- FROM THE LOOKUP's OWN CLAUSE TO THE LOOKUP CLAUSE OF THE GROUP, under the three facts on the
files and g < 12 alone. -/
theorem layerKeys_of_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (tokv : Array ℕ) {g : ℕ} (hg : g < 12) {Mz : Mats ℤ}
    {Wi : Mat} (I : Alg.ForInG (pubAt X tokv) g Mz Wi) :
    LayerKeys (layerShape X.P) X.layers.sc X.y g Mz Wi :=
  layerKeys_of_weighed hZ hR h (weighed_in_scope hZ hR h) tokv hg I

/-- The layers' joint, under the three facts on the files and g < 12 alone. -/
theorem layerOrd_of_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (tokv : Array ℕ) {g : ℕ} (hg : g < 12) {Mz : Mats ℤ}
    {Wi : Mat} {x : Cm.Seg.XI} (R : LayerR0 (layerShape X.P) X.layers.sc X.y g Mz Wi x)
    (I : Alg.ForInG (pubAt X tokv) g Mz Wi) :
    LayerOrd (layerShape X.P) X.layers.sc X.y g Mz Wi x :=
  layerOrd_of_weighed hZ hR h (weighed_in_scope hZ hR h) tokv hg R I

/-- All twelve groups, at a family of lists. -/
theorem layerOrds_of_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (tokv : Array ℕ) (own : ℕ → Mats ℤ) {Wi : Mat}
    {x : Cm.Seg.XI}
    (R : ∀ g < 12, LayerR0 (layerShape X.P) X.layers.sc X.y g (own (2 * g)) Wi x)
    (I : ∀ g < 12, Alg.ForInG (pubAt X tokv) g (own (2 * g)) Wi) :
    ∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g (own (2 * g)) Wi x :=
  layerOrds_of_weighed hZ hR h (weighed_in_scope hZ hR h) tokv own R I

#print axioms marks_some
#print axioms cols_of_place
#print axioms weighed_of_place
#print axioms weighed_of_layout
#print axioms weighed_in_scope
#print axioms layerKeys_of_scope
#print axioms layerOrds_of_scope

end Meaning.P34
