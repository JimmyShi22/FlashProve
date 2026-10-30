-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/ReadsApart.lean: kind K5: no two tables of the list that tablesP
(Johnson/Desc/First/Att/TablesP.lean) returns name one position of the vector of reads.

Main names:
  `szOf mats f`: the number of entries that a table has by the list of matrices: k (m / len).
  `fits_sz`: where a table fits, that is the number of entries under which it was laid.
  `lay_in`: tables that fit, laid one behind the other from entry m on, lie between m and m plus
    their total. `lay_apart`: two of them that hold one position are one table.
  `tablesP_laid`, `tablesP_fits`: what tablesP returns is laid so, from 0 on, and every table fits.
  `tabAt_in`: what tabAt (OnBytes/Model/Tail.lean) returns lies in the table's stretch.
  `apart_tablesP`: tablesP g (matsOf tl.mats) nW lk p = some t →
    Apart tl (t.funs.toList.map funBack). (Apart: Johnson/Desc/First/Att/Claims/TabsByChoice.lean;
    matsOf: Claims/TablesAgree.lean; funBack: Claims/Any.lean.)
An empty table names no position. Two tables with one first entry would both have to be empty but
for the last of them; nothing is asked on that (PosG is no premise here).
Used of OnBytes: the records HTailF2, HFun, TMat and the pure function HTailF2.tabAt. No routine
that runs in a context is named, and no theorem on such a routine's return.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.ReadsReturn
import Johnson.Desc.First.Att.Claims.TabsByChoice

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Placed Fun1 Geo T TablesP LookIn Pts)

variable {mats : Array (ℕ × ℕ)}

/-- The number of entries that a table has by the list of matrices. -/
def szOf (mats : Array (ℕ × ℕ)) (f : Fun1) : ℕ :=
  match mats[f.mat]? with
  | none => 0
  | some M => M.2 * (M.1 / f.len)

theorem fits_sz {t : Table} (h : fitsT mats t = true) (st : ℕ) :
    szOf mats ⟨t.mat, t.len, t.phi, 2, st⟩ = t.entries := by
  unfold fitsT P.fits at h
  unfold szOf
  show (match mats[t.mat]? with | none => 0 | some M => M.2 * (M.1 / t.len)) = _
  cases hM : mats[t.mat]? with
  | none => rw [hM] at h; cases h
  | some M =>
    rw [hM] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h.2.symm

theorem lay_in : ∀ (L : List Table) (m : ℕ), L.all (fitsT mats) = true → ∀ f ∈ layFrom m L,
    m ≤ f.start ∧ f.start + szOf mats f ≤ m + total L
  | [], _, _, f, hf => by cases hf
  | t :: L, m, hL, f, hf => by
    rw [List.all_cons, Bool.and_eq_true] at hL
    rw [total_cons]
    rcases List.mem_cons.1 hf with rfl | hf
    · rw [fits_sz hL.1]
      exact ⟨le_refl _, by show m + t.entries ≤ _; omega⟩
    · obtain ⟨a, b⟩ := lay_in L (m + t.entries) hL.2 f hf
      exact ⟨by omega, by omega⟩

/-- **Two tables of the laying that hold one position are one.** -/
theorem lay_apart : ∀ (L : List Table) (m : ℕ), L.all (fitsT mats) = true → ∀ f ∈ layFrom m L,
    ∀ f' ∈ layFrom m L, ∀ pos, f.start ≤ pos → pos < f.start + szOf mats f → f'.start ≤ pos →
      pos < f'.start + szOf mats f' → f = f'
  | [], _, _, f, hf, _, _, _, _, _, _, _ => by cases hf
  | t :: L, m, hL, f, hf, f', hf', pos, a1, a2, b1, b2 => by
    have hL' := hL
    rw [List.all_cons, Bool.and_eq_true] at hL'
    rcases List.mem_cons.1 hf with rfl | hf
    · rcases List.mem_cons.1 hf' with rfl | hf'
      · rfl
      · rw [fits_sz hL'.1] at a2
        have := (lay_in L (m + t.entries) hL'.2 f' hf').1
        have a2' : pos < m + t.entries := a2
        omega
    · rcases List.mem_cons.1 hf' with rfl | hf'
      · rw [fits_sz hL'.1] at b2
        have := (lay_in L (m + t.entries) hL'.2 f hf).1
        have b2' : pos < m + t.entries := b2
        omega
      · exact lay_apart L (m + t.entries) hL'.2 f hf f' hf' pos a1 a2 b1 b2

theorem tablesP_laid {g : Geo} {nW : ℕ} {lk : LookIn} {p : Pts} {t : TablesP}
    (h : P.tablesP g mats nW lk p = some t) : t.funs.toList = layFrom 0 (laidBy g lk p) := by
  unfold P.tablesP at h
  have a : (P.placeAll g mats nW lk p {}).bind (fun y => some y.1) = some t := h
  obtain ⟨y, hy, e⟩ := Option.bind_eq_some_iff.1 a
  obtain rfl := Option.some.inj e
  obtain ⟨_, f, _⟩ := lq_placeAll g mats nW lk p {} y.1 y.2 rfl hy
  rw [fq_placeAll g mats nW lk p {} y.1 y.2 hy, f]
  rfl

theorem tablesP_fits {g : Geo} {nW : ℕ} {lk : LookIn} {p : Pts} {t : TablesP}
    (h : P.tablesP g mats nW lk p = some t) : (laidBy g lk p).all (fitsT mats) = true := by
  have e := rt_placeAll (mats := mats) g nW lk p {} rfl
  unfold P.tablesP at h
  have a : (P.placeAll g mats nW lk p {}).bind (fun y => some y.1) = some t := h
  obtain ⟨y, hy, _⟩ := Option.bind_eq_some_iff.1 a
  rw [hy] at e
  exact (Bool.and_eq_true_iff.1 e.symm).1

/-- The runs in a column of a table's matrix. -/
def nOf (tl : HTailF2) (f : Fun1) : ℕ := (tl.mats.getD f.mat {}).m / f.len

/-- What tabAt returns lies in the table's stretch; and it is first entry + column (m / len) + run. -/
theorem tabAt_in {tl : HTailF2} (hm : mats = matsOf tl.mats) {f : Fun1} {c sg pos : ℕ}
    (h : tl.tabAt (funBack f) c sg = some pos) :
    sg < nOf tl f ∧ pos = f.start + c * nOf tl f + sg ∧ f.start ≤ pos ∧ pos < f.start + szOf mats f := by
  unfold HTailF2.tabAt at h
  split at h
  · simp only at h
    split at h
    · rename_i h1 h2
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h2
      have e := (Option.some.inj h).symm
      have hM : mats[f.mat]? = some ((tl.mats.getD f.mat {}).m, (tl.mats.getD f.mat {}).k) := by
        have hk : f.mat < tl.mats.size := by
          by_contra hc
          have h0 : tl.mats.getD f.mat {} = {} := by
            rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.not_lt.1 hc)]
            rfl
          have h2' : c < (tl.mats.getD f.mat {}).k := h2.1
          rw [h0] at h2'
          exact absurd h2' (Nat.not_lt_zero _)
        rw [hm, matsOf, Array.getElem?_map, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
        rfl
      refine ⟨h2.2, e, ?_, ?_⟩
      · rw [e]
        show f.start ≤ f.start + _ + _
        omega
      · unfold szOf
        rw [hM, e]
        show f.start + c * ((tl.mats.getD f.mat {}).m / f.len) + sg <
          f.start + (tl.mats.getD f.mat {}).k * ((tl.mats.getD f.mat {}).m / f.len)
        have h3 : (c + 1) * ((tl.mats.getD f.mat {}).m / f.len) ≤
            (tl.mats.getD f.mat {}).k * ((tl.mats.getD f.mat {}).m / f.len) := Nat.mul_le_mul_right _ h2.1
        have h4 : sg < (tl.mats.getD f.mat {}).m / f.len := h2.2
        have h5 : (c + 1) * ((tl.mats.getD f.mat {}).m / f.len) =
            c * ((tl.mats.getD f.mat {}).m / f.len) + (tl.mats.getD f.mat {}).m / f.len := by ring
        omega
    · cases h
  · cases h

/-- **No two tables of tablesP's list name one position.** -/
theorem apart_tablesP {g : Geo} {nW : ℕ} {lk : LookIn} {p : Pts} {t : TablesP} {tl : HTailF2}
    (h : P.tablesP g (matsOf tl.mats) nW lk p = some t) : Apart tl (t.funs.toList.map funBack) := by
  have hm : matsOf tl.mats = matsOf tl.mats := rfl
  intro Fn hFn Fn' hFn' c sg c' sg' pos h1 h2
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hFn
  obtain ⟨f', hf', rfl⟩ := List.mem_map.1 hFn'
  obtain ⟨a1, a2, a3, a4⟩ := tabAt_in hm h1
  obtain ⟨b1, b2, b3, b4⟩ := tabAt_in hm h2
  rw [tablesP_laid h] at hf hf'
  have e := lay_apart _ 0 (tablesP_fits h) f hf f' hf' pos a3 a4 b3 b4
  subst e
  have hn : 0 < nOf tl f := Nat.lt_of_le_of_lt (Nat.zero_le _) a1
  have e2 : c * nOf tl f + sg = c' * nOf tl f + sg' := by omega
  have q1 : (c * nOf tl f + sg) / nOf tl f = c := by
    rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt a1, Nat.add_zero]
  have q2 : (c' * nOf tl f + sg') / nOf tl f = c' := by
    rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt b1, Nat.add_zero]
  have ec : c = c' := by rw [← q1, e2, q2]
  subst ec
  exact ⟨rfl, rfl, by omega⟩

end K5Law
