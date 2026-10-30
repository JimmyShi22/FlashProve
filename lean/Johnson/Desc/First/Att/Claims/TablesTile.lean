-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/TablesTile.lean: kind K5: the tables that tablesP
(Johnson/Desc/First/Att/TablesP.lean) returns TILE the vector of reads: every position below nW, the
vector's length, is named by one of them. (That no two name one position: Claims/ReadsApart.lean.)

Main names:
  `lay_cover`: tables that fit, laid one behind the other from entry m on, leave no gap: every
    position from m up to m plus their total lies in the stretch of one of them, and that one fits.
  `tabAt_cover`: inside the stretch of a table that fits, tabAt (OnBytes/Model/Tail.lean) answers
    the position x at column (x - first entry) / n and run (x - first entry) % n, n the runs in a
    column (nOf). The converse of `tabAt_in`.
  `NQ`, `nq_bind`, `nq_placeAll`: where the placing returns, the first free entry behind it is nW
    (its last test). After FQ, fq_bind, fq_placeAll (Claims/ReadsOfIs.lean).
  `total_is_nW`: so the laid tables' numbers of entries add up to nW.
  `tables_tile`: tablesP g (matsOf tl.mats) nW lk p = some t → tl.NM = tl.mats.size →
    ∀ x < nW, ∃ Fn ∈ t.funs.toList.map funBack, ∃ c sg, tl.tabAt Fn c sg = some x.
  `tile_needs_NM`: a negative test of the second premise: tablesP reads the list of matrices and not
    the field NM; with NM set to 0 the same return stands, and no position is named at all: so,
    wherever nW is not 0, the conclusion fails there.
Premises. The return of tablesP; NM, a field of the tail's structure that tabAt's first guard reads,
is the number of matrices. Whether they are met is not shown in this file.
Used of OnBytes: the structures HTailF2, HFun, TMat and the pure function HTailF2.tabAt.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.ReadsApart

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Placed Fun1 Geo T TablesP LookIn Pts)

variable {α : Type} {mats : Array (ℕ × ℕ)}

/-- **No gap**: every position of the laid stretch lies in one table's stretch; that table fits. -/
theorem lay_cover : ∀ (L : List Table) (m : ℕ), L.all (fitsT mats) = true → ∀ x, m ≤ x →
    x < m + total L → ∃ f ∈ layFrom m L, f.start ≤ x ∧ x < f.start + szOf mats f ∧
      ∃ e, P.fits mats f.mat f.len e = true
  | [], m, _, x, h1, h2 => by
    rw [total_nil] at h2
    omega
  | t :: L, m, hL, x, h1, h2 => by
    rw [List.all_cons, Bool.and_eq_true] at hL
    rw [total_cons] at h2
    by_cases hx : x < m + t.entries
    · refine ⟨⟨t.mat, t.len, t.phi, 2, m⟩, List.mem_cons_self, h1, ?_, t.entries, hL.1⟩
      rw [fits_sz hL.1]
      exact hx
    · obtain ⟨f, hf, a, b, c⟩ := lay_cover L (m + t.entries) hL.2 x (by omega) (by omega)
      exact ⟨f, List.mem_cons_of_mem _ hf, a, b, c⟩

/-- **Inside a fitting table's stretch tabAt answers the position.** -/
theorem tabAt_cover {tl : HTailF2} (hm : mats = matsOf tl.mats) (hNM : tl.NM = tl.mats.size)
    {f : Fun1} {e x : ℕ} (hf : P.fits mats f.mat f.len e = true) (h1 : f.start ≤ x)
    (h2 : x < f.start + szOf mats f) :
    tl.tabAt (funBack f) ((x - f.start) / nOf tl f) ((x - f.start) % nOf tl f) = some x := by
  unfold P.fits at hf
  cases hM : mats[f.mat]? with
  | none => rw [hM] at hf; cases hf
  | some M =>
    rw [hM] at hf
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hf
    have hlen : f.len ≠ 0 := hf.1.1
    have hk : f.mat < tl.mats.size := by
      have := (Array.getElem?_eq_some_iff.1 hM).1
      rw [hm, matsOf, Array.size_map] at this
      exact this
    have hMe : M = ((tl.mats.getD f.mat {}).m, (tl.mats.getD f.mat {}).k) := by
      have h' := hM
      rw [hm, matsOf, Array.getElem?_map, Array.getElem?_eq_getElem hk] at h'
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
      exact (Option.some.inj h').symm
    have hs : szOf mats f = (tl.mats.getD f.mat {}).k * nOf tl f := by
      unfold szOf nOf
      rw [hM, hMe]
    rw [hs] at h2
    have hy : x - f.start < (tl.mats.getD f.mat {}).k * nOf tl f := by omega
    have hn : 0 < nOf tl f := by
      rcases Nat.eq_zero_or_pos (nOf tl f) with h0 | h0
      · rw [h0, Nat.mul_zero] at hy
        omega
      · exact h0
    have hc : (x - f.start) / nOf tl f < (tl.mats.getD f.mat {}).k :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hy)
    have hsg : (x - f.start) % nOf tl f < nOf tl f := Nat.mod_lt _ hn
    have hsum : f.start + (x - f.start) / nOf tl f * nOf tl f + (x - f.start) % nOf tl f = x := by
      have := Nat.div_add_mod' (x - f.start) (nOf tl f)
      omega
    unfold HTailF2.tabAt
    have g1 : (decide ((funBack f).mat < tl.NM) && (funBack f).len != 0) = true := by
      rw [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, hNM]
      exact ⟨hk, hlen⟩
    rw [if_pos g1]
    have g2 : (decide ((x - f.start) / nOf tl f < (tl.mats.getD (funBack f).mat {}).k) &&
        decide ((x - f.start) % nOf tl f <
          (tl.mats.getD (funBack f).mat {}).m / (funBack f).len)) = true := by
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨hc, hsg⟩
    simp only
    rw [if_pos g2]
    exact congrArg some hsum

/-- Where a placing returns, the first free entry behind it is nW. -/
def NQ (nW : ℕ) (r : T TablesP) : Prop := ∀ s a s', r s = some (a, s') → s'.next = nW

theorem nq_bind {nW : ℕ} {r : T α} {k : α → T TablesP} (h : ∀ a, NQ nW (k a)) :
    NQ nW (r >>= k) := by
  intro s b s' e
  obtain ⟨y, _, e2⟩ := tbind_some e
  exact h y.1 y.2 b s' e2

theorem nq_placeAll (g : Geo) (mats : Array (ℕ × ℕ)) (nW : ℕ) (lk : LookIn) (p : Pts) :
    NQ nW (P.placeAll g mats nW lk p) := by
  unfold P.placeAll
  iterate 26 (refine nq_bind fun _ => ?_)
  intro s a s' h
  obtain ⟨_, rfl, hb⟩ := lq_tail s.next _ _ _ s a s' rfl h
  exact beq_iff_eq.1 hb

/-- **The laid tables' numbers of entries add up to the vector's length.** -/
theorem total_is_nW {g : Geo} {nW : ℕ} {lk : LookIn} {p : Pts} {t : TablesP}
    (h : P.tablesP g mats nW lk p = some t) : total (laidBy g lk p) = nW := by
  unfold P.tablesP at h
  have a : (P.placeAll g mats nW lk p {}).bind (fun y => some y.1) = some t := h
  obtain ⟨y, hy, _⟩ := Option.bind_eq_some_iff.1 a
  obtain ⟨_, _, n⟩ := lq_placeAll g mats nW lk p {} y.1 y.2 rfl hy
  rw [nq_placeAll g mats nW lk p {} y.1 y.2 hy, Nat.zero_add] at n
  exact n.symm

/-- **The tables tile the vector of reads.** -/
theorem tables_tile {g : Geo} {nW : ℕ} {lk : LookIn} {p : Pts} {t : TablesP} {tl : HTailF2}
    (h : P.tablesP g (matsOf tl.mats) nW lk p = some t) (hNM : tl.NM = tl.mats.size) :
    ∀ x < nW, ∃ Fn ∈ t.funs.toList.map funBack, ∃ c sg, tl.tabAt Fn c sg = some x := by
  intro x hx
  obtain ⟨f, hf, a, b, e, he⟩ := lay_cover (laidBy g lk p) 0 (tablesP_fits h) x (Nat.zero_le _)
    (by rw [total_is_nW h, Nat.zero_add]; exact hx)
  rw [← tablesP_laid h] at hf
  exact ⟨funBack f, List.mem_map_of_mem hf, _, _, tabAt_cover rfl hNM he a b⟩

/-- **A negative test of the premise on NM.** -/
theorem tile_needs_NM {g : Geo} {nW : ℕ} {lk : LookIn} {p : Pts} {t : TablesP} {tl : HTailF2}
    (h : P.tablesP g (matsOf tl.mats) nW lk p = some t) (h0 : 0 < nW) :
    P.tablesP g (matsOf ({ tl with NM := 0 } : HTailF2).mats) nW lk p = some t ∧
    ¬ ∀ x < nW, ∃ Fn ∈ t.funs.toList.map funBack, ∃ c sg,
      ({ tl with NM := 0 } : HTailF2).tabAt Fn c sg = some x := by
  refine ⟨h, fun hall => ?_⟩
  obtain ⟨Fn, _, c, sg, e⟩ := hall 0 h0
  unfold HTailF2.tabAt at e
  simp at e

end K5Law

#print axioms K5Law.lay_cover
#print axioms K5Law.tabAt_cover
#print axioms K5Law.total_is_nW
#print axioms K5Law.tables_tile
#print axioms K5Law.tile_needs_NM
