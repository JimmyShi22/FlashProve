-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HlScope.lean: the premise hl of the bridge from a lookup's calls to a group's
key vectors is struck, at all public files in the goals' scope; the premise hw is said without a
table.

layerBridge_of_calls and layerKeys_of_forIn (Johnson/Road/Ends/AlgBridgeL5.lean:58;
Johnson/Road/Lane5ForInG.lean:120) ask hl: layTables mats (tableAsks P.y rd g) 0 = some r. There
mats is a free letter, and the conclusion names neither mats nor r. So hl is owed at SOME list of
matrices only. layTables refuses a family without an entry and nothing else.
  layParts_end: at a list in which the first N matrices have B rows and one column, a family's parts
    take B / L entries each.
  layTables_some: so layTables returns there, if every family has a part, lies within the first N
    matrices, and sums over at least one and at most B rows.
  asks_good: every family of tableAsks y rd g is such, at N := parts 0 + parts 1 + 5 and
    B := 2^la + T + 2^lmb, if af and ad have a part and T is not 0. General in the layout.
  hl_in_scope: so in scope, for every group, layTables returns at that list.
  weighed_free: weighedOf reads of its environment the layout alone: not the tables' places.
  layerKeys_of_weighed, layerOrd_of_weighed, layerOrds_of_weighed: layerKeys_in_scope and the
    layers' joint (Johnson/Goal/Meaning/ForInScope.lean) with hl struck and hw at the empty list of
    places.
What stays: hw: for every call of the layout, weighedOf returns (no two segments of a call list one
column, and all columns lie within the call).
-/
import Johnson.Goal.Meaning.ForInScope

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.P34

open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Layer (Lay Reads TableAsk TableAt layParts layTables tableAsks matIx)
open OnBytes.Model (CallD)
open OnBytes.Model.Verify (publicOf Public layerShape)
open Inst.Model (Mat)

/-! ## layTables returns at a list of wide enough matrices -/

/-- The list: N matrices of B rows and one column. -/
def wideMats (N B : ℕ) : Array (ℕ × ℕ) := Array.replicate N (B, 1)

theorem wide_get {N B M : ℕ} (h : M < N) : (wideMats N B).getD M (0, 0) = (B, 1) := by
  simp [wideMats, Array.getD, h]

/-- Where a family's last n parts end. -/
theorem layParts_end {N B : ℕ} (a : TableAsk) (ha : a.M0 + a.parts ≤ N) :
    ∀ (n p : ℕ), n ≤ a.parts → (layParts (wideMats N B) a n p).2 = p + n * (B / a.L)
  | 0, p, _ => by simp [layParts]
  | n + 1, p, hn => by
    have e : (layParts (wideMats N B) a (n + 1) p).2 =
        (layParts (wideMats N B) a n
          (p + ((wideMats N B).getD (a.M0 + (a.parts - (n + 1))) (0, 0)).2 *
            (((wideMats N B).getD (a.M0 + (a.parts - (n + 1))) (0, 0)).1 / a.L))).2 := rfl
    rw [e, wide_get (by omega), layParts_end a ha n _ (by omega)]
    show p + 1 * (B / a.L) + n * (B / a.L) = p + (n + 1) * (B / a.L)
    rw [Nat.one_mul, Nat.add_mul, Nat.one_mul]
    omega

/-- What is asked of a family. -/
def GoodAsk (N B : ℕ) (a : TableAsk) : Prop :=
  1 ≤ a.parts ∧ a.M0 + a.parts ≤ N ∧ 0 < a.L ∧ a.L ≤ B

theorem layTables_some {N B : ℕ} : ∀ (asks : List TableAsk), (∀ a ∈ asks, GoodAsk N B a) →
    ∀ p, ∃ r, layTables (wideMats N B) asks p = some r
  | [], _, p => ⟨_, rfl⟩
  | a :: rest, H, p => by
    obtain ⟨h1, h2, h3, h4⟩ := H a List.mem_cons_self
    have e := layParts_end (B := B) a h2 a.parts p (Nat.le_refl _)
    have hq : 0 < B / a.L := Nat.div_pos h4 h3
    have hne : ((layParts (wideMats N B) a a.parts p).2 == p) = false := by
      rw [e, beq_eq_false_iff_ne]
      have : 0 < a.parts * (B / a.L) := Nat.mul_pos h1 hq
      omega
    obtain ⟨r, hr⟩ := layTables_some rest (fun b hb => H b (List.mem_cons_of_mem _ hb))
      (layParts (wideMats N B) a a.parts p).2
    rw [layTables]
    simp only [hne, Bool.false_eq_true, if_false, hr, Option.map_some]
    exact ⟨_, rfl⟩

/-! ## The families of a group are such -/

/-- A family with a part, within the first N matrices, that sums over La or over T rows. -/
theorem good_of {N B La T : ℕ} (a : TableAsk) (h1 : 1 ≤ a.parts) (h2 : a.M0 + a.parts ≤ N)
    (hL : a.L = La ∨ a.L = T) (hLa : 0 < La ∧ La ≤ B) (hT : 0 < T ∧ T ≤ B) : GoodAsk N B a := by
  rcases hL with e | e
  · exact ⟨h1, h2, by rw [e]; exact hLa.1, by rw [e]; exact hLa.2⟩
  · exact ⟨h1, h2, by rw [e]; exact hT.1, by rw [e]; exact hT.2⟩

/-- Every family of a group's reads. -/
theorem asks_good (y : Lay) (rd : Reads) (g : ℕ) (h0 : 1 ≤ y.parts.getD 0 0)
    (h1 : 1 ≤ y.parts.getD 1 0) (hT : 0 < y.T) :
    ∀ a ∈ tableAsks y rd g,
      GoodAsk (y.parts.getD 0 0 + y.parts.getD 1 0 + 5) (2 ^ y.h.la + y.T + 2 ^ y.h.lmb) a := by
  have pa : 0 < 2 ^ y.h.la := Nat.two_pow_pos _
  have pb : 0 < 2 ^ y.h.lmb := Nat.two_pow_pos _
  have hLa : 0 < 2 ^ y.h.la ∧ 2 ^ y.h.la ≤ 2 ^ y.h.la + y.T + 2 ^ y.h.lmb := ⟨pa, by omega⟩
  have hTT : 0 < y.T ∧ y.T ≤ 2 ^ y.h.la + y.T + 2 ^ y.h.lmb := ⟨hT, by omega⟩
  have bb : ∀ nm : String, GoodAsk (y.parts.getD 0 0 + y.parts.getD 1 0 + 5)
      (2 ^ y.h.la + y.T + 2 ^ y.h.lmb) ⟨nm, (matIx y).iB, 1, 2 ^ y.h.lmb, "", false⟩ := fun nm =>
    ⟨Nat.le_refl 1, by show y.parts.getD 0 0 + y.parts.getD 1 0 + 1 + 1 ≤ _; omega, pb,
      by show 2 ^ y.h.lmb ≤ _; omega⟩
  intro a ha
  unfold tableAsks at ha
  simp only [List.mem_append] at ha
  rcases ha with (((((((ha | ha) | ha) | ha) | ha) | ha) | ha) | ha) | ha
  · obtain ⟨n, -, rfl⟩ := List.mem_map.mp ha
    exact good_of _ h0 (by show 0 + y.parts.getD 0 0 ≤ _; omega) (by simp) hLa hTT
  · obtain ⟨n, -, rfl⟩ := List.mem_map.mp ha
    exact good_of _ (Nat.le_refl 1)
      (by show y.parts.getD 0 0 + y.parts.getD 1 0 + 2 + 1 ≤ _; omega) (by simp) hLa hTT
  · obtain ⟨n, -, rfl⟩ := List.mem_map.mp ha
    exact good_of _ (Nat.le_refl 1)
      (by show y.parts.getD 0 0 + y.parts.getD 1 0 + 4 + 1 ≤ _; omega) (by simp) hLa hTT
  · split at ha
    · obtain ⟨n, -, rfl⟩ := List.mem_map.mp ha
      exact good_of _ (Nat.le_refl 1)
        (by show y.parts.getD 0 0 + y.parts.getD 1 0 + 4 + 1 ≤ _; omega) (by simp) hLa hTT
    · cases ha
  · obtain ⟨n, -, rfl⟩ := List.mem_map.mp ha
    exact good_of _ (Nat.le_refl 1)
      (by show y.parts.getD 0 0 + y.parts.getD 1 0 + 3 + 1 ≤ _; omega) (by simp) hLa hTT
  · obtain ⟨n, -, rfl⟩ := List.mem_map.mp ha
    exact good_of _ h1 (by show y.parts.getD 0 0 + y.parts.getD 1 0 ≤ _; omega) (by simp) hLa hTT
  · obtain ⟨n, -, rfl⟩ := List.mem_map.mp ha
    exact good_of _ (Nat.le_refl 1)
      (by show y.parts.getD 0 0 + y.parts.getD 1 0 + 1 ≤ _; omega) (by simp) hLa hTT
  · split at ha
    · obtain ⟨n, -, rfl⟩ := List.mem_map.mp ha
      exact good_of _ (Nat.le_refl 1)
        (by show y.parts.getD 0 0 + y.parts.getD 1 0 + 2 + 1 ≤ _; omega) (by simp) hLa hTT
    · cases ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact bb _
    · exact bb _
    · exact bb _

/-! ## In scope -/

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- hl AT SOME LIST OF MATRICES, for every group, at all public files in the goals' scope. -/
theorem hl_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (g : ℕ) :
    ∃ mats r, layTables mats (tableAsks X.y X.layers.rd g) 0 = some r := by
  have B := Hd.public_of_core h (Hd.core_of_scope hZ hR h)
  have L2 := laid2_of_layout B.lay
  have hh := (shape_of_public h).trans (shape_in_scope hZ hR h)
  have hp : X.y.parts = #[3, 1, 1, 1] := by
    rw [L2.parts, hh]
    show ((sizesOf hKF).map (·.2.2.2.2)).toArray = #[3, 1, 1, 1]
    decide +kernel
  have hT : 0 < X.y.T := by
    rw [L2.T]
    exact Nat.two_pow_pos _
  obtain ⟨r, hr⟩ := layTables_some _
    (asks_good X.y X.layers.rd g (by rw [hp]; decide) (by rw [hp]; decide) hT) 0
  exact ⟨_, r, hr⟩

/-- weighedOf reads of its environment the layout alone. -/
theorem weighed_free (P : Layer.Pub) (g g' : ℕ) (tab tab' : List TableAt) (cd : CallD) :
    (Alg.envG P g tab).weighedOf cd = (Alg.envG P g' tab').weighedOf cd := rfl

/-- hw in the layout's letters alone: for every call of the layout, weighedOf returns. -/
def Weighed (X : Public) : Prop :=
  ∀ cd ∈ X.y.calls, ∃ wg, (Alg.envG X.layers 0 []).weighedOf cd = some wg

/-- From the lookup's own clause to the lookup clause of the group, with hl struck. -/
theorem layerKeys_of_weighed (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (hw : Weighed X) (tokv : Array ℕ) {g : ℕ}
    (hg : g < 12) {Mz : Mats ℤ} {Wi : Mat} (I : Alg.ForInG (pubAt X tokv) g Mz Wi) :
    LayerKeys (layerShape X.P) X.layers.sc X.y g Mz Wi := by
  obtain ⟨mats, r, hl⟩ := hl_in_scope hZ hR h g
  exact layerKeys_in_scope hZ hR h tokv hg hl (fun cd hcd => hw cd hcd) I

/-- The layers' joint, with hl struck. -/
theorem layerOrd_of_weighed (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (hw : Weighed X) (tokv : Array ℕ) {g : ℕ}
    (hg : g < 12) {Mz : Mats ℤ} {Wi : Mat} {x : Cm.Seg.XI}
    (R : LayerR0 (layerShape X.P) X.layers.sc X.y g Mz Wi x)
    (I : Alg.ForInG (pubAt X tokv) g Mz Wi) :
    LayerOrd (layerShape X.P) X.layers.sc X.y g Mz Wi x :=
  layerOrd_iff_split.2 ⟨R, layerKeys_of_weighed hZ hR h hw tokv hg I⟩

/-- All twelve groups, at a family of lists. -/
theorem layerOrds_of_weighed (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (hw : Weighed X) (tokv : Array ℕ) (own : ℕ → Mats ℤ)
    {Wi : Mat} {x : Cm.Seg.XI}
    (R : ∀ g < 12, LayerR0 (layerShape X.P) X.layers.sc X.y g (own (2 * g)) Wi x)
    (I : ∀ g < 12, Alg.ForInG (pubAt X tokv) g (own (2 * g)) Wi) :
    ∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g (own (2 * g)) Wi x :=
  fun g hg => layerOrd_of_weighed hZ hR h hw tokv hg (R g hg) (I g hg)

#print axioms layTables_some
#print axioms asks_good
#print axioms hl_in_scope
#print axioms layerKeys_of_weighed
#print axioms layerOrds_of_weighed

end Meaning.P34
