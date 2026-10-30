-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Columns.lean: THE LAW OF A CALL'S COLUMNS, PROVED: ColumnsStatement and
OverColumnsStatement of HeadColumnsLaw.lean.
THE ARGUMENT. Entry x of key s lies in the piece 2^b of its key (piece, Law/FromLookup.lean). Write
base b for the sum over the keys of their bits above b, cnt s b for the number of keys in front of s
that have the bit b, all b for the number of keys that have it. The entry's column lies in
[base b + cnt s b * 2^b, base b + (cnt s b + 1) * 2^b). For b' < b: base b + all b * 2^b <= base b'; and
base b + all b * 2^b <= the sum of the lengths. So pieces of different sizes, pieces of one size of
different keys, and entries of one piece lie apart.
-/
import Mathlib
import Johnson.Desc.Kinds.HeadColumnsLaw
import Johnson.Desc.Kinds.Law.FromLookup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

/-! ## 1. Counting on lists -/

theorem cnt_step (p : Nat → Bool) : ∀ (l : List Nat) (s s' : Nat), s < s' → s < l.length →
    p (l.getD s 0) = true → ((l.take s).filter p).length + 1 ≤ ((l.take s').filter p).length
  | [], _, _, _, h, _ => absurd h (by simp)
  | _ :: _, _, 0, h, _, _ => absurd h (Nat.not_lt_zero _)
  | a :: l, 0, s' + 1, _, _, hp => by
    have hp' : p a = true := by simpa using hp
    simp [List.take_succ_cons, List.filter_cons, hp']
  | a :: l, s + 1, s' + 1, h, hl, hp => by
    have ih := cnt_step p l s s' (by omega) (by simpa using hl) (by simpa using hp)
    simp only [List.take_succ_cons, List.filter_cons]
    split
    · simp only [List.length_cons]
      omega
    · exact ih

theorem sum_step (f g : Nat → Nat) (p : Nat → Bool) (c : Nat)
    (h : ∀ n, f n + (if p n = true then c else 0) ≤ g n) :
    ∀ l : List Nat, (l.map f).sum + (l.filter p).length * c ≤ (l.map g).sum
  | [] => by simp
  | a :: l => by
    have h1 := h a
    have h2 := sum_step f g p c h l
    simp only [List.map_cons, List.sum_cons, List.filter_cons]
    by_cases hp : p a = true
    · rw [if_pos hp] at h1
      rw [if_pos hp, List.length_cons, Nat.succ_mul]
      omega
    · rw [if_neg hp] at h1
      rw [if_neg hp]
      omega

theorem lt_length_of_getD {l : List Nat} {s x : Nat} (h : x < l.getD s 0) : s < l.length := by
  by_contra hs
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
  exact Nat.not_lt_zero _ h

theorem getD_mem {l : List Nat} {s : Nat} (h : s < l.length) : l.getD s 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

/-! ## 2. The bits above -/

theorem above_top (b n : Nat) : above b n + (if n.testBit b = true then 2 ^ b else 0) ≤ n := by
  unfold above
  have hdm := Nat.div_add_mod n (2 ^ (b + 1))
  have hm : n % 2 ^ (b + 1) = n % 2 ^ b + 2 ^ b * (n / 2 ^ b % 2) := Nat.mod_pow_succ
  rw [Nat.mul_comm] at hdm
  split
  · rename_i ht
    rw [Nat.testBit_eq_decide_div_mod_eq] at ht
    have h1 : n / 2 ^ b % 2 = 1 := of_decide_eq_true ht
    rw [h1, Nat.mul_one] at hm
    omega
  · omega

theorem mult_le {D M n : Nat} (hD : 0 < D) (hd : D ∣ M) (h : M ≤ n) : M ≤ n / D * D := by
  obtain ⟨q, rfl⟩ := hd
  have h1 : q ≤ n / D := (Nat.le_div_iff_mul_le hD).2 (by rw [Nat.mul_comm]; exact h)
  calc D * q = q * D := Nat.mul_comm _ _
    _ ≤ n / D * D := Nat.mul_le_mul_right D h1

theorem above_step {b b' : Nat} (hb : b' < b) (n : Nat) :
    above b n + (if n.testBit b = true then 2 ^ b else 0) ≤ above b' n := by
  have hd : 2 ^ (b' + 1) ∣ above b n + (if n.testBit b = true then 2 ^ b else 0) := by
    apply dvd_add (dvd_above (by omega) n)
    split
    · exact pow_dvd_pow 2 (by omega)
    · exact dvd_zero _
  exact mult_le (by positivity) hd (above_top b n)

/-! ## 3. Where an entry's column lies -/

section Lens
variable (lens : List Nat)

/-- The sum over the keys of their bits above b. -/
def base (b : Nat) : Nat := (lens.map (above b)).sum
/-- The number of keys in front of s that have the bit b. -/
def cnt (s b : Nat) : Nat := ((lens.take s).filter (·.testBit b)).length
/-- The number of keys that have the bit b. -/
def all (b : Nat) : Nat := (lens.filter (·.testBit b)).length

theorem base_step {b b' : Nat} (hb : b' < b) : base lens b + all lens b * 2 ^ b ≤ base lens b' :=
  sum_step (above b) (above b') (·.testBit b) (2 ^ b) (above_step hb) lens

theorem base_top (b : Nat) : base lens b + all lens b * 2 ^ b ≤ lens.sum := by
  have h := sum_step (above b) id (·.testBit b) (2 ^ b) (above_top b) lens
  rwa [List.map_id] at h

variable {lens}

theorem cnt_lt_all {s b : Nat} (hs : s < lens.length) (hb : (lens.getD s 0).testBit b = true) :
    cnt lens s b + 1 ≤ all lens b := by
  have h := cnt_step (·.testBit b) lens s lens.length hs hs hb
  rwa [List.take_length] at h

theorem cnt_lt_cnt {s s' b : Nat} (h : s < s') (hs : s < lens.length)
    (hb : (lens.getD s 0).testBit b = true) : cnt lens s b + 1 ≤ cnt lens s' b :=
  cnt_step (·.testBit b) lens s s' h hs hb

/-- An entry's column, by its piece. -/
theorem column_in {s x : Nat} (hx : x < lens.getD s 0) (hn : lens.getD s 0 < 2 ^ 41) :
    column lens s x = base lens (piece (lens.getD s 0) x)
        + cnt lens s (piece (lens.getD s 0) x) * 2 ^ piece (lens.getD s 0) x
        + (x - above (piece (lens.getD s 0) x) (lens.getD s 0))
      ∧ x - above (piece (lens.getD s 0) x) (lens.getD s 0) < 2 ^ piece (lens.getD s 0) x := by
  obtain ⟨_, t2, t3⟩ := piece_spec hx hn
  exact ⟨column_eq lens s x, by omega⟩

theorem column_lt_top {s x : Nat} (hx : x < lens.getD s 0) (hn : lens.getD s 0 < 2 ^ 41) :
    column lens s x < base lens (piece (lens.getD s 0) x)
      + all lens (piece (lens.getD s 0) x) * 2 ^ piece (lens.getD s 0) x := by
  obtain ⟨t1, _, _⟩ := piece_spec hx hn
  obtain ⟨c1, c2⟩ := column_in hx hn
  have h1 := Nat.mul_le_mul_right (2 ^ piece (lens.getD s 0) x)
    (cnt_lt_all (lt_length_of_getD hx) t1)
  rw [Nat.succ_mul] at h1
  omega

end Lens

/-- **The two facts.** -/
theorem columns_law : ColumnsStatement := by
  intro lens hl
  have hN : ∀ {s x : Nat}, x < lens.getD s 0 → lens.getD s 0 < 2 ^ 41 :=
    fun h => hl _ (getD_mem (lt_length_of_getD h))
  -- a larger piece lies in front
  have big : ∀ s x s' x', x < lens.getD s 0 → x' < lens.getD s' 0 →
      piece (lens.getD s' 0) x' < piece (lens.getD s 0) x →
      column lens s x < column lens s' x' := by
    intro s x s' x' hx hx' hb
    have h1 := column_lt_top hx (hN hx)
    have h2 := base_step lens hb
    have h3 := (column_in hx' (hN hx')).1
    omega
  -- of two pieces of one size the earlier key's lies in front
  have early : ∀ s x s' x', x < lens.getD s 0 → x' < lens.getD s' 0 →
      piece (lens.getD s' 0) x' = piece (lens.getD s 0) x → s < s' →
      column lens s x < column lens s' x' := by
    intro s x s' x' hx hx' hb hs
    obtain ⟨t1, _, _⟩ := piece_spec hx (hN hx)
    obtain ⟨c1, c2⟩ := column_in hx (hN hx)
    have c3 := (column_in hx' (hN hx')).1
    rw [hb] at c3
    have h1 := Nat.mul_le_mul_right (2 ^ piece (lens.getD s 0) x)
      (cnt_lt_cnt hs (lt_length_of_getD hx) t1)
    rw [Nat.succ_mul] at h1
    omega
  refine ⟨fun s x hx => lt_of_lt_of_le (column_lt_top hx (hN hx)) (base_top lens _), ?_⟩
  intro s x s' x' hx hx' h
  rcases lt_trichotomy (piece (lens.getD s' 0) x') (piece (lens.getD s 0) x) with hb | hb | hb
  · exact absurd h (Nat.ne_of_lt (big s x s' x' hx hx' hb))
  · rcases lt_trichotomy s s' with hs | hs | hs
    · exact absurd h (Nat.ne_of_lt (early s x s' x' hx hx' hb hs))
    · subst hs
      refine ⟨rfl, ?_⟩
      obtain ⟨_, t2, _⟩ := piece_spec hx (hN hx)
      obtain ⟨_, t2', _⟩ := piece_spec hx' (hN hx')
      have c1 := (column_in hx (hN hx)).1
      have c3 := (column_in hx' (hN hx')).1
      rw [hb] at c3 t2'
      omega
    · exact absurd h.symm (Nat.ne_of_lt (early s' x' s x hx' hx hb.symm hs))
  · exact absurd h.symm (Nat.ne_of_lt (big s' x' s x hx' hx hb))

/-! ## 4. The sum over columns -/

theorem lookup_of_mem {α : Type} : ∀ (L : List (Nat × α)) (c : Nat) (v : α), (c, v) ∈ L →
    (∀ p ∈ L, p.1 = c → p.2 = v) → L.lookup c = some v
  | [], _, _, h, _ => absurd h (by simp)
  | (c', v') :: L, c, v, h, hu => by
    by_cases he : c = c'
    · subst he
      have hv : v' = v := hu (c, v') (by simp) rfl
      simp [List.lookup_cons, hv]
    · have hb : (c == c') = false := by simpa using he
      have h' : (c, v) ∈ L := by
        rcases List.mem_cons.1 h with h1 | h1
        · exact absurd (congrArg Prod.fst h1) he
        · exact h1
      rw [List.lookup_cons, hb]
      exact lookup_of_mem L c v h' fun p hp => hu p (List.mem_cons_of_mem _ hp)

theorem lookup_none {α : Type} : ∀ (L : List (Nat × α)) (c : Nat), (∀ p ∈ L, p.1 ≠ c) →
    L.lookup c = none
  | [], _, _ => rfl
  | (c', v') :: L, c, h => by
    have he : c ≠ c' := fun e => h (c', v') (by simp) e.symm
    have hb : (c == c') = false := by simpa using he
    rw [List.lookup_cons, hb]
    exact lookup_none L c fun p hp => h p (List.mem_cons_of_mem _ hp)

theorem mem_entries {α : Type} (lens : List Nat) (g : Nat → Nat → α) (p : Nat × α) :
    p ∈ entriesOf lens g ↔
      ∃ s x, s < lens.length ∧ x < lens.getD s 0 ∧ p = (column lens s x, g s x) := by
  unfold entriesOf
  simp only [List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨s, hs, x, hx, rfl⟩
    exact ⟨s, x, hs, hx, rfl⟩
  · rintro ⟨s, x, hs, hx, rfl⟩
    exact ⟨s, hs, x, hx, rfl⟩

/-- At an entry's column the table holds the entry's value. -/
theorem tableOf_entry {α : Type} {lens : List Nat} (hl : ∀ n ∈ lens, n < 2 ^ 41)
    (g : Nat → Nat → α) (pad : α) {s x : Nat} (hx : x < lens.getD s 0) :
    tableOf lens g pad (column lens s x) = g s x := by
  unfold tableOf
  rw [lookup_of_mem (entriesOf lens g) (column lens s x) (g s x)
    ((mem_entries lens g _).2 ⟨s, x, lt_length_of_getD hx, hx, rfl⟩)]
  · rfl
  · intro p hp he
    obtain ⟨s', x', _, hx', rfl⟩ := (mem_entries lens g p).1 hp
    obtain ⟨h1, h2⟩ := (columns_law lens hl).2 s' x' s x hx' hx he
    subst h1
    subst h2
    rfl

/-- At a column that no entry takes it holds the padding's. -/
theorem tableOf_pad {α : Type} (lens : List Nat) (g : Nat → Nat → α) (pad : α) {c : Nat}
    (h : ∀ s x, x < lens.getD s 0 → column lens s x ≠ c) : tableOf lens g pad c = pad := by
  unfold tableOf
  rw [lookup_none (entriesOf lens g) c]
  · rfl
  · intro p hp
    obtain ⟨s, x, _, hx, rfl⟩ := (mem_entries lens g p).1 hp
    exact h s x hx

/-- An entry's column, of the pair (key's number, entry). -/
def colS (lens : List Nat) (i : Σ _ : Nat, Nat) : Nat := column lens i.1 i.2

/-- **The caller's sum, with its padding term, is the sum over columns.** -/
theorem over_columns : OverColumnsStatement := by
  intro R _ lens N w g pad hl hN hw
  obtain ⟨ltSum, inj⟩ := columns_law lens hl
  classical
  obtain ⟨I, hIdef⟩ : ∃ I : Finset (Σ _ : Nat, Nat),
      I = (Finset.range lens.length).sigma fun s => Finset.range (lens.getD s 0) := ⟨_, rfl⟩
  have hI : ∀ i ∈ I, i.2 < lens.getD i.1 0 := fun i hi => by
    rw [hIdef] at hi
    exact Finset.mem_range.1 (Finset.mem_sigma.1 hi).2
  have hinj : ∀ i ∈ I, ∀ j ∈ I, colS lens i = colS lens j → i = j := by
    intro i hi j hj h
    obtain ⟨h1, h2⟩ := inj i.1 i.2 j.1 j.2 (hI i hi) (hI j hj) h
    obtain ⟨i1, i2⟩ := i
    obtain ⟨j1, j2⟩ := j
    simp only at h1 h2
    subst h1
    subst h2
    rfl
  have hsub : I.image (colS lens) ⊆ Finset.range N := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hc
    exact Finset.mem_range.2 (lt_of_lt_of_le (ltSum i.1 i.2 (hI i hi)) hN)
  have e1 : ((Finset.range lens.length).sum fun s => (Finset.range (lens.getD s 0)).sum fun x =>
      w (column lens s x) * g s x) = I.sum fun i => w (colS lens i) * g i.1 i.2 := by
    rw [hIdef]
    exact Finset.sum_sigma' _ _ fun s x => w (column lens s x) * g s x
  have e2 : ((Finset.range lens.length).sum fun s => (Finset.range (lens.getD s 0)).sum fun x =>
      w (column lens s x)) = I.sum fun i => w (colS lens i) := by
    rw [hIdef]
    exact Finset.sum_sigma' _ _ fun s x => w (column lens s x)
  have e3 : ((Finset.range N \ I.image (colS lens)).sum fun c => w c * tableOf lens g pad c)
      = pad * (Finset.range N \ I.image (colS lens)).sum w := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [tableOf_pad lens g pad, mul_comm]
    intro s x hx he
    apply (Finset.mem_sdiff.1 hc).2
    refine Finset.mem_image.2 ⟨⟨s, x⟩, ?_, he⟩
    rw [hIdef]
    exact Finset.mem_sigma.2 ⟨Finset.mem_range.2 (lt_length_of_getD hx), Finset.mem_range.2 hx⟩
  have e4 : (Finset.range N \ I.image (colS lens)).sum w = 1 - I.sum fun i => w (colS lens i) := by
    have h0 := Finset.sum_sdiff (f := w) hsub
    rw [Finset.sum_image hinj, hw] at h0
    exact eq_sub_of_add_eq h0
  have e5 : (I.sum fun i => w (colS lens i) * tableOf lens g pad (colS lens i))
      = I.sum fun i => w (colS lens i) * g i.1 i.2 :=
    Finset.sum_congr rfl fun i hi => by
      show w (colS lens i) * tableOf lens g pad (column lens i.1 i.2) = _
      rw [tableOf_entry hl g pad (hI i hi)]
  rw [e1, e2, ← Finset.sum_sdiff hsub, Finset.sum_image hinj, e3, e4, e5]
  ring

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.columns_law
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.over_columns
