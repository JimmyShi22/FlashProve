-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/Shape.lean: the coefficient vector on a group's main table has the table's number
of variables.

A group's main table has 2^(k + logEll) entries, k the bits of the group's rows and logEll the bits
of the places. This file shows that the laying keeps this: every structured vector of the group's
row's coefficient vector on the main table has k + logEll variables, and every single entry has an
index below 2^(k + logEll) (CFits). It holds of the group's row without coefficients, goes over
addToGroupRow for a row that has passed the tests of the adding, and so holds of what Bat.combine
returns.

Main definitions: CFits.
Main theorems: CFits.of_fits, CFits.insertChoice, lays_cfits, combine_cfits.

Not claimed here. That the structured vectors are in order (Tensor.ok): RowIn does not ask it of
a row's terms. Nothing on the mask table, whose length is in MaskReady, or on the kept forms.

-/
import Johnson.Desc.Means.Combine

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

/-- Every structured vector of the form has n variables, and every single entry an index below
2^n. -/
def CFits (n : Nat) (f : Form) : Prop :=
  (∀ v ∈ f.tensors, v.vars = n) ∧ ∀ e ∈ f.entries, e.1 < 2 ^ n

variable {n : Nat} {f g : Form}

theorem CFits.empty (n : Nat) : CFits n {} :=
  ⟨fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩

theorem CFits.add (h : CFits n f) {v : Tensor} (hv : v.vars = n) : CFits n (f.add v) :=
  ⟨fun w hw => by
    rcases List.mem_cons.1 hw with e | c
    · rw [e]
      exact hv
    · exact h.1 w c, h.2⟩

theorem CFits.addEntry (h : CFits n f) {i : Nat} (hi : i < 2 ^ n) (c : E) :
    CFits n (f.addEntry i c) :=
  ⟨h.1, fun e he => by
    rcases List.mem_cons.1 he with e' | c'
    · rw [e']
      exact hi
    · exact h.2 e c'⟩

theorem CFits.scale (h : CFits n g) (x : E) : CFits n (g.scale x) :=
  ⟨fun w hw => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
    rw [Tensor.vars_scale]
    exact h.1 v hv, fun e he => by
    obtain ⟨e0, h0, rfl⟩ := List.mem_map.1 he
    exact h.2 e0 h0⟩

theorem CFits.plus (h : CFits n f) (k : CFits n g) : CFits n (f.plus g) :=
  ⟨fun w hw => (List.mem_append.1 hw).elim (k.1 w) (h.1 w),
    fun e he => (List.mem_append.1 he).elim (k.2 e) (h.2 e)⟩

theorem CFits.addForm (h : CFits n f) (k : CFits n g) (x : E) : CFits n (f.addForm g x) :=
  h.plus (k.scale x)

/-- The library's test gives it. That test also asks that each structured vector is in order
(Tensor.ok); this is dropped here. -/
theorem CFits.of_fits (h : f.fits n = true) : CFits n f := by
  unfold Form.fits at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨fun v hv => (h.1 v hv).1, h.2⟩

theorem three_digits {x y z A B C : Nat} (hx : x < A) (hy : y < B) (hz : z < C) :
    x + y * A + z * (A * B) < A * B * C := by
  have s1 : x + y * A < A * B := by
    calc x + y * A < A + y * A := by omega
      _ = (y + 1) * A := by ring
      _ ≤ B * A := Nat.mul_le_mul_right _ hy
      _ = A * B := by ring
  calc x + y * A + z * (A * B) < A * B + z * (A * B) := by omega
    _ = (z + 1) * (A * B) := by ring
    _ ≤ C * (A * B) := Nat.mul_le_mul_right _ hz
    _ = A * B * C := by ring

/-- Variables put in at the place a raise the number of variables. -/
theorem CFits.insertChoice {a p : Nat} (h : CFits (a + p) g) (count value : Nat) :
    CFits (a + count + p) (g.insertChoice a count value) := by
  refine ⟨fun w hw => ?_, fun e he => ?_⟩
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
    have e := h.1 v hv
    rw [Tensor.vars_insertChoice v a count value (by omega), e]
    omega
  · obtain ⟨e0, h0, rfl⟩ := List.mem_map.1 he
    have hlt := h.2 e0 h0
    rw [pow_add] at hlt
    show e0.1 % 2 ^ a + value % 2 ^ count * 2 ^ a + e0.1 / 2 ^ a * 2 ^ (a + count) <
      2 ^ (a + count + p)
    simp only [pow_add]
    exact three_digits (Nat.mod_lt _ (Nat.two_pow_pos a)) (Nat.mod_lt _ (Nat.two_pow_pos count))
      (Nat.div_lt_of_lt_mul hlt)

/-! ## The steps of the laying -/

variable {S : Statement} {G : Group} {L : GroupLayout} {row : Row}

theorem foldlM_inv {α β : Type} (P : β → Prop) (step : β → α → Option β) :
    ∀ (l : List α), (∀ a ∈ l, ∀ b b', step b a = some b' → P b → P b') →
    ∀ b b', l.foldlM step b = some b' → P b → P b'
  | [], _, b, b', h, hp => by
    obtain rfl := Option.some.inj h
    exact hp
  | a :: l, hs, b, b', h, hp => by
    rw [List.foldlM_cons] at h
    obtain ⟨b1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact foldlM_inv P step l (fun a' ha' => hs a' (List.mem_cons_of_mem _ ha')) b1 b' h2
      (hs a List.mem_cons_self b b1 h1 hp)

theorem addTermTo_cfits (F : LayFacts S G L) (x : E) (acc acc' : GroupRow) (t : Term)
    (ht : Blk.placeOk S G t.oracle t.part t.v.vars 0 = true)
    (h : addTermTo S L x acc t = some acc') (hc : CFits (L.k + L.logEll) acc.c) :
    CFits (L.k + L.logEll) acc'.c := by
  obtain ⟨hm, hh, hv, _⟩ := (placeOk_iff _ _ _ _ _ _).1 ht
  obtain ⟨i, hf⟩ := F.find_of_mem _ hm
  unfold addTermTo at h
  cases hp : t.part with
  | main =>
    rw [hp] at hh hv
    by_cases hk : L.kept.getD i false = true
    · simp only [hf, hp, hk, if_true] at h
      obtain rfl := Option.some.inj h
      exact hc
    · have hk' : L.kept.getD i false = false := Bool.eq_false_iff.2 hk
      obtain ⟨first, hmf⟩ := F.main_block_of _ i hf hh hk'
      have hle := (F.main_block _ i first hf hmf).2.2.le
      have hlt : ¬ L.k < S.rowBits t.oracle .main := Nat.not_lt.2 hle
      simp only [hf, hp, hk', hmf, hlt, Bool.false_eq_true, if_false] at h
      obtain rfl := Option.some.inj h
      refine hc.add ?_
      have hpl := F.main_places _ hm hh
      have hv' : t.v.vars = S.rowBits t.oracle .main + S.placeBits t.oracle .main := hv
      rw [Tensor.vars_insertChoice _ _ _ _ (by rw [Tensor.vars_scale]; omega), Tensor.vars_scale]
      omega
  | mask =>
    rw [hp] at hh
    obtain ⟨first, hmf⟩ := F.mask_block_of _ i hf hh
    have hlt : ¬ L.h < S.rowBits t.oracle .mask :=
      Nat.not_lt.2 (F.mask_block _ i first hf hmf).2.le
    simp only [hf, hp, hmf, hlt, if_false] at h
    obtain rfl := Option.some.inj h
    exact hc

theorem addEntryTo_cfits (F : LayFacts S G L) (x : E) (acc acc' : GroupRow) (o : Nat) (part : Part)
    (index : Nat) (coeff : E) (hm : o ∈ G.members.toList) (hh : S.has o part = true)
    (hi : index < 2 ^ S.tableBits o part)
    (h : addEntryTo S L x acc o part index coeff = some acc')
    (hc : CFits (L.k + L.logEll) acc.c) : CFits (L.k + L.logEll) acc'.c := by
  obtain ⟨i, hf⟩ := F.find_of_mem _ hm
  unfold addEntryTo at h
  cases part with
  | main =>
    by_cases hk : L.kept.getD i false = true
    · simp only [hf, hk, if_true] at h
      obtain rfl := Option.some.inj h
      exact hc
    · have hk' : L.kept.getD i false = false := Bool.eq_false_iff.2 hk
      obtain ⟨first, hmf⟩ := F.main_block_of _ i hf hh hk'
      simp only [hf, hk', hmf, Bool.false_eq_true, if_false] at h
      obtain rfl := Option.some.inj h
      refine hc.addEntry ?_ _
      apply groupIndex_lt _ _ _ _ _ (F.main_block _ i first hf hmf).2.2
      rw [← F.main_places _ hm hh]
      exact hi
  | mask =>
    obtain ⟨first, hmf⟩ := F.mask_block_of _ i hf hh
    simp only [hf, hmf] at h
    split at h
    · obtain rfl := Option.some.inj h
      exact hc
    · cases h

theorem addFormTo_cfits (F : LayFacts S G L) (x : E) (acc acc' : GroupRow) (f : MainForm)
    (hm : f.oracle ∈ G.members.toList) (hh : S.has f.oracle .main = true)
    (hfit : f.c.fits (S.tableBits f.oracle .main) = true)
    (h : addFormTo S L x acc f = some acc') (hc : CFits (L.k + L.logEll) acc.c) :
    CFits (L.k + L.logEll) acc'.c := by
  obtain ⟨i, hf⟩ := F.find_of_mem _ hm
  unfold addFormTo at h
  by_cases hk : L.kept.getD i false = true
  · simp only [hf, hk, if_true] at h
    obtain rfl := Option.some.inj h
    exact hc
  · have hk' : L.kept.getD i false = false := Bool.eq_false_iff.2 hk
    obtain ⟨first, hmf⟩ := F.main_block_of _ i hf hh hk'
    have hle := (F.main_block _ i first hf hmf).2.2.le
    have hlt : ¬ L.k < S.rowBits f.oracle .main := Nat.not_lt.2 hle
    simp only [hf, hk', hmf, hlt, Bool.false_eq_true, if_false] at h
    obtain rfl := Option.some.inj h
    refine hc.addForm ?_ x
    have c0 : CFits (S.rowBits f.oracle .main + S.placeBits f.oracle .main) f.c :=
      CFits.of_fits hfit
    have c1 := c0.insertChoice (L.k - S.rowBits f.oracle .main)
      (first / 2 ^ S.rowBits f.oracle .main)
    have e : S.rowBits f.oracle .main + (L.k - S.rowBits f.oracle .main) +
        S.placeBits f.oracle .main = L.k + L.logEll := by
      rw [F.main_places _ hm hh]
      omega
    rw [e] at c1
    exact c1

theorem ready_c (acc : GroupRow) (L : GroupLayout) : (acc.ready L).c = acc.c := by
  unfold GroupRow.ready
  split <;> rfl

/-- **The laying keeps the number of variables.** -/
theorem lays_cfits (F : LayFacts S G L) (hr : RowIn S G row) (x : E) (acc acc' : GroupRow)
    (h : addToGroupRow S L row x acc = some acc') (hc : CFits (L.k + L.logEll) acc.c) :
    CFits (L.k + L.logEll) acc'.c := by
  unfold addToGroupRow at h
  simp only [← Array.foldlM_toList, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨a1, h1, a2, h2, a3, h3, a4, h4, rfl⟩ := h
  have c1 := foldlM_inv (fun g : GroupRow => CFits (L.k + L.logEll) g.c) (addTermTo S L x)
    row.terms.toList (fun t ht b b' hb => addTermTo_cfits F x b b' t (hr.terms t ht) hb) _ a1 h1
    (by
      show CFits (L.k + L.logEll) (acc.ready L).c
      rw [ready_c]
      exact hc)
  have c2 := foldlM_inv (fun g : GroupRow => CFits (L.k + L.logEll) g.c)
    (fun acc (u : Single) => addEntryTo S L x acc u.oracle u.part u.index u.coeff)
    row.units.toList (fun u hu b b' hb => by
      obtain ⟨hm, hh, _, hi⟩ := (placeOk_iff _ _ _ _ _ _).1 (hr.units u hu)
      exact addEntryTo_cfits F x b b' _ _ _ _ hm hh hi hb) _ a2 h2 c1
  have c3 := foldlM_inv (fun g : GroupRow => CFits (L.k + L.logEll) g.c) (addRunTo S L x)
    row.runs.toList (fun w hw b b' hb => by
      obtain ⟨_, _, hpl⟩ := hr.runs w hw
      obtain ⟨hm, hh, _, hi⟩ := (placeOk_iff _ _ _ _ _ _).1 hpl
      exact foldlM_inv (fun g : GroupRow => CFits (L.k + L.logEll) g.c)
        (fun acc j => addEntryTo S L x acc w.oracle w.part (w.first + w.step * j) (w.coeffs.get j))
        (List.range w.coeffs.size) (fun j hj c c' hc' => by
          have hj' : j ≤ w.coeffs.size - 1 := by
            have := List.mem_range.1 hj
            omega
          have hlt : w.first + w.step * j < 2 ^ S.tableBits w.oracle w.part :=
            Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left _ hj') _) hi
          exact addEntryTo_cfits F x c c' _ _ _ _ hm hh hlt hc') b b' hb) _ a3 h3 c2
  exact foldlM_inv (fun g : GroupRow => CFits (L.k + L.logEll) g.c) (addFormTo S L x)
    row.forms.toList (fun f hf b b' hb => by
      obtain ⟨hpl, hfit⟩ := hr.forms f hf
      obtain ⟨hm, hh, _, _⟩ := (placeOk_iff _ _ _ _ _ _).1 hpl
      exact addFormTo_cfits F x b b' f hm hh hfit hb) _ a4 h4 c3

/-- **What the batching returns has the table's number of variables.** -/
theorem combine_cfits {g : Nat} {rows : Array Row} {x : E} {out : GroupRow}
    (hG : S.groups[g]? = some G) (hL : S.layout g = some L) (hOk : GroupOk S G)
    (hr : ∀ r ∈ rows.toList, RowIn S G r) (h : Bat.combine S g ⟨L, rows⟩ x = some out) :
    CFits (L.k + L.logEll) out.c := by
  have F := layFacts hG hL hOk
  have a0 : AsideIn S G {} := ⟨rfl, rfl, by simp, by simp, by simp, by simp⟩
  unfold Bat.combine at h
  simp only [← Array.foldlM_toList, Option.bind_eq_bind] at h
  obtain ⟨s, h1, h2⟩ := Option.bind_eq_some_iff.1 h
  have inv := foldlM_inv
    (fun s : GroupRow × Row × E => CFits (L.k + L.logEll) s.1.c ∧ AsideIn S G s.2.1) _ rows.toList
    (fun r hr' b b' hb hP => by
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hb
      obtain ⟨acc, ha, rfl⟩ := hb
      exact ⟨lays_cfits F (hr r hr').structured b.2.2 b.1 acc ha hP.1,
        hP.2.addScaled (hr r hr') b.2.2⟩) _ s h1 ⟨CFits.empty _, a0⟩
  exact lays_cfits F inv.2.isIn oneE s.1 out h2 inv.1

end OnBytes.Means
