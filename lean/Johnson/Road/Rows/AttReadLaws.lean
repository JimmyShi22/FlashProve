-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttReadLaws.lean: what the forms of the attention sub-proof are worth, as sums of
entries of the matrices.

The claims of the attention sub-proof read the committed matrices through four functions of
OnBytes/Model/AttentionClaimsA.lean: u3at (one entry of a table), weighted (a sum of forms under
public weights), and on top of them plane, shV, xl and overG. This file values u3at and weighted,
and reads an entry of a table as a sum of entries of its matrix, in a world in which every table is
true of the matrices (AttAt in Johnson/Road/Rows/AttRead.lean). The readers on top of them are
valued in Johnson/Road/Rows/AttReadRow.lean and Johnson/Road/Rows/AttReadLong.lean.

Main theorems.
 - foldlM_value, weighted_value: a loop that adds terms to a form.
 - u3at_value: the form of one entry, and the test that the entry lies in its table.
 - tab_read, as_read: an entry of a table as the sum of its block of its matrix.

Every theorem on a form begins "if the routine returns": none says that it does. tab_read and
as_read take AttAt and the table's place as given. Nothing is said about probabilities or about
hiding. The program does not import this file.


-/
import Johnson.Road.Rows.AttRead
import Johnson.Road.HeadKit
import Johnson.Road.FormsKeysTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff Fork SubM HFun HTailF2 TenAt tenCell eqTab blockRows)
open OnBytes.Attention (Shape Heard)
open OnBytes.Road.Hd (Ok ok_pure ok_bind ok_lift mustAs_ok ok_uEnt colsOf rdW)

variable {K : Type} [Field K]

/-! ## Runs -/

/-- A run that returns, in the form of Johnson/Road/HeadKit.lean. -/
theorem ok_of_yields {α : Type} {m : SubM α} {F G : Fork} {c c' : Ctx} {a : α}
    (h : (m F).Yields c (a, G) c') : Ok m F c a G c' :=
  (Blk.yields_iff _ _ _ _).mp h

/-- A refusal does not return. -/
theorem refuse_not_ok {α : Type} (n : String) (F G : Fork) (C D : Ctx) (a : α) :
    ¬ Ok (liftM (Model.refuse n : Blk α) : SubM α) F C a G D := by
  rw [ok_lift]
  rintro ⟨h, -⟩
  have e : (Model.refuse n : Blk α) C = .error { name := n } := rfl
  rw [e] at h
  cases h

/-! ## Loops that add terms to a form -/

/-- The sum of a list of the first n numbers' values. -/
theorem sum_map_range (v : ℕ → K) (n : ℕ) : ((List.range n).map v).sum = ∑ i ∈ range n, v i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- A fold over a list in which each step leaves state and context and adds v a to the form's
value: so does the whole, and it adds the sum. What each step shows besides (P a) holds of all
members. -/
theorem foldlM_value (ρ : Reading K) (W : World K) {α : Type} (F : Fork) (C : Ctx)
    (step : Aff → α → SubM Aff) (v : α → K) (P : α → Prop) :
    ∀ (l : List α),
      (∀ a ∈ l, ∀ s y G D, Ok (step s a) F C y G D →
        G = F ∧ D = C ∧ P a ∧ y.value ρ W = s.value ρ W + v a) →
      ∀ s y G D, Ok (l.foldlM step s) F C y G D →
        G = F ∧ D = C ∧ (∀ a ∈ l, P a) ∧ y.value ρ W = s.value ρ W + (l.map v).sum
  | [], _, s, y, G, D, h => by
    rw [List.foldlM_nil, ok_pure] at h
    obtain ⟨e1, e2, e3⟩ := h
    rw [e1]
    exact ⟨e2, e3, fun a ha => (by cases ha), by simp⟩
  | a :: l, H, s, y, G, D, h => by
    rw [List.foldlM_cons, ok_bind] at h
    obtain ⟨s1, F1, C1, h1, h2⟩ := h
    obtain ⟨e1, e2, e3, e4⟩ := H a List.mem_cons_self s s1 F1 C1 h1
    rw [e1, e2] at h2
    obtain ⟨g1, g2, g3, g4⟩ := foldlM_value ρ W F C step v P l
      (fun b hb => H b (List.mem_cons_of_mem _ hb)) s1 y G D h2
    refine ⟨g1, g2, ?_, ?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with hb | hb
      · rw [hb]
        exact e3
      · exact g3 b hb
    · rw [g4, e4, List.map_cons, List.sum_cons]
      ring

/-- The verifier's weighted: the sum over i below n of w[i] times the form f i. -/
theorem weighted_value (ρ : Reading K) (W : World K) {F : Fork} {C : Ctx} (n : ℕ) (w : Array E)
    (f : ℕ → SubM Aff) (v : ℕ → K) (P : ℕ → Prop)
    (hf : ∀ i < n, ∀ x G D, Ok (f i) F C x G D → G = F ∧ D = C ∧ P i ∧ x.value ρ W = v i)
    {q : Aff} {G : Fork} {D : Ctx} (h : Ok (Attention.weighted n w f) F C q G D) :
    G = F ∧ D = C ∧ (∀ i < n, P i) ∧
      q.value ρ W = ∑ i ∈ range n, ρ.val (w.getD i zeroE) * v i := by
  unfold Attention.weighted at h
  obtain ⟨e1, e2, e3, e4⟩ := foldlM_value ρ W F C
    (fun s i => f i >>= fun x => pure (Aff.addMul s x (w.getD i zeroE)))
    (fun i => ρ.val (w.getD i zeroE) * v i) P (List.range n)
    (by
      intro i hi s y G1 D1 hy
      have hy' : Ok (f i >>= fun x => pure (Aff.addMul s x (w.getD i zeroE))) F C y G1 D1 := hy
      rw [ok_bind] at hy'
      obtain ⟨x, F1, C1, h1, h2⟩ := hy'
      obtain ⟨a1, a2, a3, a4⟩ := hf i (List.mem_range.mp hi) x F1 C1 h1
      rw [ok_pure] at h2
      obtain ⟨b1, b2, b3⟩ := h2
      rw [b1, b2, b3]
      exact ⟨a1, a2, a3, by rw [Aff.value_addMul, a4]⟩)
    (Aff.ofConst zeroE) q G D h
  refine ⟨e1, e2, fun i hi => e3 i (List.mem_range.mpr hi), ?_⟩
  rw [e4, Aff.value_ofConst, ρ.zero, zero_add, sum_map_range]

/-! ## One entry of a table -/

/-- The form of entry i of the table that begins at t: the entry lies in the table, and the form is
worth entry t + i of the vector of tables. -/
theorem u3at_value (ρ : Reading K) (W : World K) {h : Heard} {t i : ℕ} {F G : Fork} {C D : Ctx}
    {a : Aff} (hh : Ok (Attention.u3at h t i) F C a G D) :
    G = F ∧ D = C ∧ i < (h.t.tabLen.lookup t).getD 0 ∧
      a.value ρ W = rdW W h.iU3 (colsOf F h.iU3) (t + i) := by
  unfold Attention.u3at at hh
  rw [ok_bind] at hh
  obtain ⟨u, F1, C1, h1, h2⟩ := hh
  rw [ok_lift, mustAs_ok] at h1
  obtain ⟨⟨hb, e1⟩, e2⟩ := h1
  rw [e1, e2] at h2
  obtain ⟨e3, e4, e5⟩ := ok_uEnt h2
  refine ⟨e3, e4, of_decide_eq_true hb, ?_⟩
  rw [e5, Aff.value_ent]
  rfl

section Tables

variable {ρ : Reading K} {W : World K} {tl : HTailF2} {K3 : ℕ} {M : Mats K} {h : Heard}
  {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

/-- An entry of a table, as the sum of its block of its matrix under the table's weights. -/
theorem tab_read (A : AttAt ρ W tl K3 M h lid cf fs) {t mat len : ℕ} {phi : Array E}
    (Tb : TabAt tl h t mat len phi) (hm : mat < tl.NM) (hl : len ≠ 0) {x : ℕ}
    (hx : x < (h.t.tabLen.lookup t).getD 0) :
    rdW W h.iU3 K3 (t + x) = ∑ j ∈ range len, ρ.val (phi.getD j zeroE) *
      M mat (x % ((tl.mats.getD mat {}).m / len) * len + j)
        (x / ((tl.mats.getD mat {}).m / len)) := by
  rw [Tb.size] at hx
  obtain ⟨Fn, hF, e1, e2, e3, e4⟩ := Tb.laid
  have hn : 0 < (tl.mats.getD mat {}).m / len := by
    rcases Nat.eq_zero_or_pos ((tl.mats.getD mat {}).m / len) with h0 | h0
    · rw [h0, Nat.mul_zero] at hx
      exact absurd hx (Nat.not_lt_zero _)
    · exact h0
  have hc : x / ((tl.mats.getD mat {}).m / len) < (tl.mats.getD mat {}).k :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)
  have hs := Nat.mod_lt x hn
  have ht := tailAt_some tl Fn (c := x / ((tl.mats.getD mat {}).m / len))
    (sg := x % ((tl.mats.getD mat {}).m / len))
    (by rw [e2]; exact hm) (by rw [e3]; exact hl) (by rw [e2]; exact hc)
    (by rw [e2, e3]; exact hs)
  have hv := A.tabs Fn hF _ _ _ ht
  rw [e1, e2, e3, e4, Nat.add_assoc, Nat.div_add_mod'] at hv
  exact hv

/-- An entry of a table on the matrix as: column x of all parts together, under the weights. -/
theorem as_read (A : AttAt ρ W tl K3 M h lid cf fs) {t : ℕ} {phi : Array E}
    (Tb : AsAt h t phi) {x : ℕ} (hx : x < (h.t.tabLen.lookup t).getD 0) :
    rdW W h.iU3 K3 (t + x) = ∑ j ∈ range (2 ^ h.S.cf.lmS), ρ.val (phi.getD j zeroE) *
      M (x / (h.S.kAs / h.S.cf.NAs)) j (x % (h.S.kAs / h.S.cf.NAs)) := by
  rw [Tb.size] at hx
  have hw : 0 < h.S.kAs / h.S.cf.NAs := by
    rcases Nat.eq_zero_or_pos (h.S.kAs / h.S.cf.NAs) with h0 | h0
    · rw [h0, Nat.mul_zero] at hx
      exact absurd hx (Nat.not_lt_zero _)
    · exact h0
  have hq : x / (h.S.kAs / h.S.cf.NAs) < h.S.cf.NAs :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)
  obtain ⟨Fn, hF, e1, e2, e3, e4⟩ := Tb.laid _ hq
  obtain ⟨m1, m2⟩ := A.mats.asM _ hq
  have hp : 0 < 2 ^ h.S.cf.lmS := Nat.two_pow_pos _
  have ht := tailAt_some tl Fn (c := x % (h.S.kAs / h.S.cf.NAs)) (sg := 0)
    (by rw [e2, A.mats.nm]; omega) (by rw [e3]; exact Nat.ne_of_gt hp)
    (by rw [e2, m2]; exact Nat.mod_lt _ hw)
    (by rw [e2, e3, m1, Nat.div_self hp]; exact Nat.one_pos)
  have hv := A.tabs Fn hF _ _ _ ht
  rw [e1, e2, e3, e4, m1, Nat.div_self hp, Nat.mul_one, Nat.add_zero, Nat.add_assoc,
    Nat.div_add_mod'] at hv
  simp only [Nat.zero_mul, Nat.zero_add] at hv
  exact hv

end Tables

end OnBytes.Road.Rows
