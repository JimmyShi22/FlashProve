-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Law/CubeKitC.lean: CONDITIONAL. Three definitions, and statements with their
proofs.

What is here. Tools for the laws on a sum over a cube: what `Cube.fits` gives; the list of the
variables that are left; what holds of `Cube.bound` behind each round.

  `FitsP`, `fitsP`   of `Cube.fits`: the order lists each variable once; each map has 2 ^ n entries
  `split_sorted`, `placeOf_split`, `erase_split`   a falling list cut at a member
  `boundStep`, `bound_nil`, `bound_snoc`   `Cube.bound`, round by round
  `Inv`, `inv_nil`, `inv_snoc`, `inv`   what holds behind each round
  `next_var`   the variable of the next round
  Beside these, smaller steps: `sorted_range`, `bound_eq`, `zip_snoc`, `zip_short`, `order_cut`,
  `zips`, `drop_next`.

Limits. `bound_eq` and `bound_nil` have no hypothesis. `bound_snoc`, `zips`, `drop_next`,
`order_cut` and `inv_snoc` ask that the rest of the order begins with the round's variable
(c.order.drop rs.length = v :: os). `inv_nil`, `inv_snoc`, `inv` and `next_var` are under `FitsP`,
which is less than `Cube.fits`: two of its five clauses are not spent; `inv_snoc` asks `Inv` behind
the rounds in front besides, `next_var` rs.length < c.n, `inv` rs.length ≤ c.n.

No property is claimed.
-/
import Johnson.Desc.K4.Honest.Law.CubeKitB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest.CubeLaw
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading eqTab)
open OnBytes.Road (getD_map_lt getD_ge)

/-! ## 1 What the test on the sizes gives -/

/-- What the laws spend of `Cube.fits`. -/
structure FitsP (c : Cube) : Prop where
  len : c.order.length = c.n
  nodup : c.order.Nodup
  mem : ∀ v, v ∈ c.order ↔ v < c.n
  size : ∀ a, a < c.maps.size → (c.maps.getD a #[]).size = 2 ^ c.n

theorem fitsP (c : Cube) (h : c.fits = true) : FitsP c := by
  simp only [Cube.fits, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hA, hB⟩, hC⟩, _⟩, _⟩ := h
  have hA' : c.order.length = c.n := by simpa using hA
  have hB' : ∀ v, v < c.n → v ∈ c.order := by simpa using hB
  have hC' : ∀ a (ha : a < c.maps.size), (c.maps[a]).size = 2 ^ c.n := by
    simpa [Array.all_eq_true] using hC
  have hnd : (List.range c.n).Nodup := by simp [List.nodup_range]
  have hperm : (List.range c.n).Perm c.order :=
    (List.subperm_of_subset hnd fun v hv => hB' v (List.mem_range.mp hv)).perm_of_length_le
      (by rw [List.length_range, hA'])
  refine ⟨hA', hperm.nodup_iff.mp hnd, fun v => hperm.mem_iff.symm.trans List.mem_range, ?_⟩
  intro a ha
  have e : c.maps.getD a #[] = c.maps[a] := by simp [Array.getD, ha]
  rw [e, hC' a ha]

/-! ## 2 A falling list -/

theorem sorted_range : ∀ n : ℕ, (List.range n).reverse.Pairwise (· > ·)
  | 0 => by simp
  | n + 1 => by
    have e : (List.range (n + 1)).reverse = n :: (List.range n).reverse := by
      rw [List.range_succ]
      simp
    rw [e, List.pairwise_cons]
    exact ⟨fun u hu => by simpa using hu, sorted_range n⟩

theorem split_sorted (left : List ℕ) (hp : left.Pairwise (· > ·)) (v : ℕ) (hv : v ∈ left) :
    ∃ hi lo, left = hi ++ v :: lo ∧ (∀ u ∈ hi, v < u) ∧ (∀ u ∈ lo, u < v) := by
  obtain ⟨hi, lo, rfl⟩ := List.append_of_mem hv
  rw [List.pairwise_append] at hp
  obtain ⟨_, h2, h3⟩ := hp
  exact ⟨hi, lo, rfl, fun u hu => h3 u hu v (by simp),
    fun u hu => (List.pairwise_cons.mp h2).1 u hu⟩

theorem placeOf_split (hi lo : List ℕ) (v : ℕ) (h1 : ∀ u ∈ hi, v < u) (h2 : ∀ u ∈ lo, u < v) :
    placeOf (hi ++ v :: lo) v = lo.length := by
  have a : hi.filter (· < v) = [] := by
    rw [List.filter_eq_nil_iff]
    intro u hu
    simpa using Nat.le_of_lt (h1 u hu)
  have b : lo.filter (· < v) = lo := by
    rw [List.filter_eq_self]
    intro u hu
    simpa using h2 u hu
  unfold placeOf
  rw [List.filter_append, a, List.nil_append, List.filter_cons_of_neg (by simp), b]

theorem erase_split (hi lo : List ℕ) (v : ℕ) (h1 : ∀ u ∈ hi, v < u) :
    (hi ++ v :: lo).erase v = hi ++ lo := by
  have hn : v ∉ hi := fun h => Nat.lt_irrefl v (h1 v h)
  rw [List.erase_append_right _ hn, List.erase_cons_head]

/-! ## 3 The tables, round by round -/

/-- One round of `Cube.bound`. -/
def boundStep (s : List ℕ × Array Tab) (x : ℕ × E) : List ℕ × Array Tab :=
  (s.1.erase x.1, s.2.map (bindAt (placeOf s.1 x.1) x.2))

theorem bound_eq (c : Cube) (rs : List E) :
    c.bound rs = (c.order.zip rs).foldl boundStep ((List.range c.n).reverse, c.maps) := rfl

theorem bound_nil (c : Cube) : c.bound [] = ((List.range c.n).reverse, c.maps) := by
  rw [bound_eq, List.zip_nil_right]
  rfl

theorem zip_snoc {α β : Type} (T : List α) (v : α) (os : List α) (rs : List β) (r : β)
    (h : T.length = rs.length) : (T ++ v :: os).zip (rs ++ [r]) = T.zip rs ++ [(v, r)] := by
  rw [List.zip_append h]
  simp

theorem zip_short {α β : Type} (T : List α) (v : α) (os : List α) (rs : List β)
    (h : T.length = rs.length) : (T ++ v :: os).zip rs = T.zip rs := by
  have h' : (T ++ v :: os).zip (rs ++ []) = T.zip rs ++ (v :: os).zip [] := List.zip_append h
  simpa using h'

/-- The order, cut in front of the next round's variable. -/
theorem order_cut {c : Cube} {rs : List E} {v : ℕ} {os : List ℕ}
    (h : c.order.drop rs.length = v :: os) :
    c.order = c.order.take rs.length ++ v :: os ∧ (c.order.take rs.length).length = rs.length := by
  have h1 : c.order = c.order.take rs.length ++ v :: os := by
    rw [← h, List.take_append_drop]
  have h2 := congrArg List.length h
  rw [List.length_drop, List.length_cons] at h2
  exact ⟨h1, by rw [List.length_take]; omega⟩

theorem zips {c : Cube} {rs : List E} {v : ℕ} {os : List ℕ}
    (h : c.order.drop rs.length = v :: os) (r : E) :
    c.order.zip (rs ++ [r]) = c.order.zip rs ++ [(v, r)] := by
  obtain ⟨h1, h2⟩ := order_cut h
  have e1 : c.order.zip (rs ++ [r]) = (c.order.take rs.length ++ v :: os).zip (rs ++ [r]) :=
    congrArg (fun l => l.zip (rs ++ [r])) h1
  have e2 : c.order.zip rs = (c.order.take rs.length ++ v :: os).zip rs :=
    congrArg (fun l => l.zip rs) h1
  rw [e1, e2, zip_snoc _ _ _ _ _ h2, zip_short _ _ _ _ h2]

theorem bound_snoc {c : Cube} {rs : List E} {v : ℕ} {os : List ℕ}
    (h : c.order.drop rs.length = v :: os) (r : E) :
    c.bound (rs ++ [r]) = boundStep (c.bound rs) (v, r) := by
  rw [bound_eq, bound_eq, zips h r, List.foldl_append]
  rfl

theorem drop_next {c : Cube} {rs : List E} {v : ℕ} {os : List ℕ}
    (h : c.order.drop rs.length = v :: os) (r : E) : c.order.drop (rs ++ [r]).length = os := by
  obtain ⟨h1, h2⟩ := order_cut h
  have e : c.order.drop (rs ++ [r]).length =
      (c.order.take rs.length ++ v :: os).drop (rs ++ [r]).length :=
    congrArg (fun l => l.drop (rs ++ [r]).length) h1
  have e3 : (rs ++ [r]).length = (c.order.take rs.length ++ [v]).length := by
    rw [List.length_append, List.length_append, h2]
    rfl
  have e4 : c.order.take rs.length ++ v :: os = (c.order.take rs.length ++ [v]) ++ os := by simp
  rw [e, e3, e4, List.drop_left]

/-- The variable of the next round. -/
theorem next_var {c : Cube} (F : FitsP c) (rs : List E) (hr : rs.length < c.n) :
    ∃ v os, c.order.drop rs.length = v :: os := by
  cases h : c.order.drop rs.length with
  | nil =>
    have := congrArg List.length h
    rw [List.length_drop, F.len, List.length_nil] at this
    omega
  | cons v os => exact ⟨v, os, rfl⟩

/-- What holds of the variables that are left and of the tables, behind the rounds of rs. -/
structure Inv (c : Cube) (rs : List E) : Prop where
  sorted : (c.bound rs).1.Pairwise (· > ·)
  mem : ∀ v, v ∈ (c.bound rs).1 ↔ v ∈ c.order.drop rs.length
  len : (c.bound rs).1.length + rs.length = c.n
  size : ∀ a, a < (c.bound rs).2.size →
    ((c.bound rs).2.getD a #[]).size = 2 ^ (c.bound rs).1.length
  count : (c.bound rs).2.size = c.maps.size

theorem inv_nil {c : Cube} (F : FitsP c) : Inv c [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [bound_nil]
  · exact sorted_range c.n
  · intro v
    simp [F.mem v]
  · simp
  · simpa using F.size

theorem inv_snoc {c : Cube} (F : FitsP c) {rs : List E} {v : ℕ} {os : List ℕ}
    (h : c.order.drop rs.length = v :: os) (r : E) (I : Inv c rs) : Inv c (rs ++ [r]) := by
  have hv : v ∈ (c.bound rs).1 := (I.mem v).mpr (by rw [h]; simp)
  have hnd : (c.bound rs).1.Nodup := I.sorted.imp fun hab => Nat.ne_of_gt hab
  have hod : (v :: os).Nodup := by
    rw [← h]
    exact F.nodup.sublist (List.drop_sublist _ _)
  have hpos : 0 < (c.bound rs).1.length := List.length_pos_of_mem hv
  have hlen : ((c.bound rs).1.erase v).length = (c.bound rs).1.length - 1 :=
    List.length_erase_of_mem hv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [bound_snoc h r]
    exact I.sorted.sublist List.erase_sublist
  · intro u
    rw [bound_snoc h r, drop_next h r]
    show u ∈ (c.bound rs).1.erase v ↔ u ∈ os
    rw [hnd.mem_erase_iff, I.mem u, h, List.mem_cons]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact absurd h2 h1
      · exact h2
    · intro h2
      exact ⟨fun e => (List.nodup_cons.mp hod).1 (e ▸ h2), Or.inr h2⟩
  · rw [bound_snoc h r]
    show ((c.bound rs).1.erase v).length + (rs ++ [r]).length = c.n
    have := I.len
    rw [hlen, List.length_append, List.length_singleton]
    omega
  · rw [bound_snoc h r]
    intro a ha
    have ha' : a < (c.bound rs).2.size := by
      simpa [boundStep] using ha
    show (((c.bound rs).2.map (bindAt (placeOf (c.bound rs).1 v) r)).getD a #[]).size =
      2 ^ ((c.bound rs).1.erase v).length
    rw [getD_map_lt _ _ ha' #[] #[], bindAt_size, I.size a ha', hlen]
    obtain ⟨L, hL⟩ : ∃ L, (c.bound rs).1.length = L + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hL, pow_succ]
    simp
  · rw [bound_snoc h r]
    show ((c.bound rs).2.map _).size = c.maps.size
    rw [Array.size_map, I.count]

/-- `Inv` holds behind each round. CONDITIONAL: on F and rs.length ≤ c.n. -/
theorem inv {c : Cube} (F : FitsP c) : ∀ rs : List E, rs.length ≤ c.n → Inv c rs := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil => intro _; exact inv_nil F
  | append_singleton rs r ih =>
    intro hr
    rw [List.length_append, List.length_singleton] at hr
    obtain ⟨v, os, h⟩ := next_var F rs (by omega)
    exact inv_snoc F h r (ih (by omega))

end OnBytes.Desc.First.K4.Honest.CubeLaw

#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.FitsP
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.fitsP
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.sorted_range
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.split_sorted
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.placeOf_split
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.erase_split
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.boundStep
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.bound_eq
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.bound_nil
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.zip_snoc
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.zip_short
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.order_cut
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.zips
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.bound_snoc
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.drop_next
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.next_var
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.Inv
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.inv_nil
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.inv_snoc
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.inv
