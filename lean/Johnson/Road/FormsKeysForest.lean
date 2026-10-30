-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysForest.lean: what Forest.shape returns, in closed form.

The lookup of a sub-proof lays the keys of its calls in trees of one depth. Forest.shape
(OnBytes/Model/Forest.lean) computes, from the calls' records and a cap on the depth, how many
trees each call has, how many there are in all, and the number of each call's first tree. The first
trees come out of a loop over the calls in the order of byFallingKey: the calls with the most trees
first, calls with as many trees in the order of the list. This file says what the function returns
without the loop.

Every statement here is on the verifier's side alone: no name of the library stands in it. The
first tree of a call is stated in the form in which the library defines its own (firstTree in
Inst/Model/FF/Index.lean: the sum, over the calls that are larger, or as large and earlier, of
their numbers of trees), so that the two can be compared by rewriting; no theorem here compares
them.

Main definitions: fallsBefore, LoopKeeps. Main theorems.
 - shape_numbers: if Forest.shape returns fo, then fo.iota is the calls' logarithms of their
   numbers of keys less fo.dT; fo.NT is the sum of 2^iota over the calls; fo.rK is clog2 of fo.NT;
   and fo.first at a call is the sum of 2^iota over the calls that stand before it. shape_iota_at:
   the first clause, call by call.
 - pairwise_byFallingKey, mem_byFallingKey, perm_byFallingKey, sum_byFallingKey: in the list of
   byFallingKey each number stands before all that follow it; the list is a rearrangement of the
   numbers below n.
 - forIn_keeps: a rule for a loop over a list whose steps may refuse.

The one hypothesis is that Forest.shape returns. For a layout that the verifier returns it does
(shape_of_layout in Johnson/Road/FormsKeysShape.lean).

What is not claimed. Nothing is said of the fields callOf, kT, cK and pub, nor of the tests that
the function makes. The depth fo.dT is the matter of shape_dT (Johnson/Road/FormsKeysCap.lean). The
program does not import this file.
-/
import Johnson.Road.FormsKeysCap

set_option autoImplicit false

namespace OnBytes.Road

open Finset
open OnBytes.Model (Call byFallingKey clog2)

/-! ## The order of byFallingKey -/

section Order

variable (key : ℕ → ℕ)

/-- c' stands before c: it has the larger key, or the same key and the smaller number. -/
def fallsBefore (c' c : ℕ) : Prop := key c < key c' ∨ (key c' = key c ∧ c' < c)

instance (c' c : ℕ) : Decidable (fallsBefore key c' c) := by
  unfold fallsBefore
  infer_instance

/-- No number stands before itself. -/
theorem fallsBefore_irrefl (c : ℕ) : ¬ fallsBefore key c c := by
  unfold fallsBefore
  omega

/-- Of two numbers at most one stands before the other. -/
theorem fallsBefore_asymm {a b : ℕ} (h : fallsBefore key a b) : ¬ fallsBefore key b a := by
  unfold fallsBefore at *
  omega

/-- A greatest value that a fold computes from a start is at least the start. -/
theorem start_le_foldl_max : ∀ (l : List ℕ) (m : ℕ), m ≤ l.foldl (fun m i => max m (key i)) m
  | [], _ => Nat.le_refl _
  | i :: l, m => Nat.le_trans (Nat.le_max_left _ _) (start_le_foldl_max l (max m (key i)))

/-- It is at least the key of every member. -/
theorem key_le_foldl_max : ∀ (l : List ℕ) (m i : ℕ), i ∈ l →
    key i ≤ l.foldl (fun m i => max m (key i)) m
  | [], _, _, h => by cases h
  | j :: l, m, i, h => by
    rcases List.mem_cons.mp h with e | h'
    · rw [e]
      exact Nat.le_trans (Nat.le_max_right _ _) (start_le_foldl_max key l (max m (key j)))
    · exact key_le_foldl_max l (max m (key j)) i h'

/-- byFallingKey with its local names written out. -/
theorem byFallingKey_eq (n : ℕ) : byFallingKey n key =
    (List.range ((List.range n).foldl (fun m i => max m (key i)) 0 + 1)).reverse.flatMap
      fun k => (List.range n).filter fun i => key i == k := rfl

/-- The list holds the numbers below n. -/
theorem mem_byFallingKey (n c : ℕ) : c ∈ byFallingKey n key ↔ c < n := by
  rw [byFallingKey_eq]
  simp only [List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨k, -, hc, -⟩
    exact hc
  · intro hc
    exact ⟨key c, Nat.lt_succ_of_le (key_le_foldl_max key _ 0 c (List.mem_range.mpr hc)), hc, rfl⟩

/-- In the list each number stands before all that follow it. -/
theorem pairwise_byFallingKey (n : ℕ) : (byFallingKey n key).Pairwise (fallsBefore key) := by
  rw [byFallingKey_eq]
  refine List.pairwise_flatMap.mpr ⟨fun k _ => ?_, ?_⟩
  · refine ((List.pairwise_lt_range (n := n)).filter _).imp_of_mem ?_
    intro a b ha hb hab
    have ea : key a = k := beq_iff_eq.mp (List.mem_filter.mp ha).2
    have eb : key b = k := beq_iff_eq.mp (List.mem_filter.mp hb).2
    exact Or.inr ⟨by rw [ea, eb], hab⟩
  · rw [List.pairwise_reverse]
    refine (List.pairwise_lt_range (n := _)).imp ?_
    intro a b hab x hx y hy
    have ex : key x = b := beq_iff_eq.mp (List.mem_filter.mp hx).2
    have ey : key y = a := beq_iff_eq.mp (List.mem_filter.mp hy).2
    exact Or.inl (by rw [ex, ey]; exact hab)

/-- The list is a rearrangement of the numbers below n. -/
theorem perm_byFallingKey (n : ℕ) : (byFallingKey n key).Perm (List.range n) := by
  have nd : (byFallingKey n key).Nodup := by
    refine (pairwise_byFallingKey key n).imp ?_
    intro a b h e
    subst e
    exact fallsBefore_irrefl key a h
  refine (List.perm_ext_iff_of_nodup nd List.nodup_range).mpr fun c => ?_
  rw [mem_byFallingKey, List.mem_range]

/-- A sum over the list of the first n numbers is the sum over the range. -/
theorem rangeSumN (g : ℕ → ℕ) (n : ℕ) : ((List.range n).map g).sum = ∑ x ∈ range n, g x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- A sum over the list is the sum over the numbers below n. -/
theorem sum_byFallingKey (n : ℕ) (g : ℕ → ℕ) :
    ((byFallingKey n key).map g).sum = ∑ i ∈ range n, g i := by
  rw [((perm_byFallingKey key n).map g).sum_eq, rangeSumN]

end Order

/-! ## Loops -/

/-- A loop over a list in which every step goes on: what holds of the members taken so far and the
state at the start, and is kept by each step, holds of the whole list and the state at the end. The
step may use where in the list it stands. -/
theorem forIn_keeps {α σ : Type} (f : α → σ → Except String (ForInStep σ)) (l0 : List α)
    (I : List α → σ → Prop)
    (step : ∀ pre a rest, l0 = pre ++ a :: rest → ∀ s s', I pre s → f a s = .ok s' →
      ∃ t, s' = .yield t ∧ I (pre ++ [a]) t) :
    ∀ (l pre : List α) (s r : σ), l0 = pre ++ l → I pre s → forIn l s f = .ok r → I l0 r
  | [], pre, s, r, e, hI, h => by
    rw [List.forIn_nil] at h
    have hr : s = r := Except.ok.inj h
    rw [e, List.append_nil, ← hr]
    exact hI
  | a :: l, pre, s, r, e, hI, h => by
    rw [List.forIn_cons] at h
    obtain ⟨s', hs, h⟩ := ok_of_bind h
    obtain ⟨t, rfl, hI'⟩ := step pre a l e s s' hI hs
    exact forIn_keeps f l0 I step l (pre ++ [a]) t r (by rw [e]; simp) hI' h

/-- A fold that adds a function of an array's members is the sum over the array's numbers. -/
theorem foldl_add_sum (a : Array ℕ) (g : ℕ → ℕ) :
    a.foldl (fun s i => s + g i) 0 = ∑ c ∈ range a.size, g (a.getD c 0) :=
  Array.foldl_induction (motive := fun i s => s = ∑ c ∈ range i, g (a.getD c 0)) (by simp)
    fun i s hs => by
      have hs' : s = ∑ c ∈ range i.1, g (a.getD c 0) := hs
      show s + g a[i] = ∑ c ∈ range (i.1 + 1), g (a.getD c 0)
      rw [hs', Finset.sum_range_succ]
      simp [Array.getD, i.2]

/-- Writing at one index leaves the others. -/
theorem getD_setN_ne (a : Array ℕ) {i j : ℕ} (h : i ≠ j) (x : ℕ) :
    (a.setIfInBounds i x).getD j 0 = a.getD j 0 := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- What has been written at an index within the array is read there. -/
theorem getD_setN_self (a : Array ℕ) {i : ℕ} (h : i < a.size) (x : ℕ) :
    (a.setIfInBounds i x).getD i 0 = x := by
  simp [Array.getD_eq_getD_getElem?, h]

/-! ## Forest.shape -/

/-- What the loop of Forest.shape keeps. pre: the calls taken so far; w c: the number of trees of
call c. The array of first trees has its size; the next free tree is the number of trees of the
calls taken; and the first tree of a call that has been taken is the number of trees of the calls
taken that stand before it. -/
def LoopKeeps (key w : ℕ → ℕ) (NC : ℕ) (pre : List ℕ) (first : Array ℕ) (free : ℕ) : Prop :=
  first.size = NC ∧ free = (pre.map w).sum ∧
    ∀ c ∈ pre, first.getD c 0 = (pre.map fun c' => if fallsBefore key c' c then w c' else 0).sum

/-- One step of the loop keeps it: the call a, which all calls taken stand before, gets the next
free tree, and its trees are taken. -/
theorem loopKeeps_step {key w : ℕ → ℕ} {NC : ℕ} {pre : List ℕ} {first : Array ℕ} {free a : ℕ}
    (hI : LoopKeeps key w NC pre first free) (ha : a < NC)
    (hb : ∀ x ∈ pre, fallsBefore key x a) :
    LoopKeeps key w NC (pre ++ [a]) (first.setIfInBounds a free) (free + w a) := by
  obtain ⟨h1, h2, h3⟩ := hI
  have hne : ∀ x ∈ pre, a ≠ x := fun x hx e => fallsBefore_irrefl key a (by
    have := hb x hx
    rwa [← e] at this)
  refine ⟨by rw [Array.size_setIfInBounds]; exact h1, by simp [h2], fun c hc => ?_⟩
  rw [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero]
  rcases List.mem_append.mp hc with hc | hc
  · rw [getD_setN_ne first (hne c hc), h3 c hc, if_neg (fallsBefore_asymm key (hb c hc)),
      Nat.add_zero]
  · have e : c = a := by simpa using hc
    subst e
    rw [getD_setN_self first (by rw [h1]; exact ha), if_neg (fallsBefore_irrefl key c),
      Nat.add_zero, h2]
    exact congrArg List.sum (List.map_congr_left fun x hx => (if_pos (hb x hx)).symm)

/-- The numbers that Forest.shape returns, in closed form. Call c has 2^iota[c] trees, where iota[c]
is the logarithm of its number of keys less the depth of a tree; NT is the number of all trees; rK
the rounded-up logarithm of NT; and the first tree of call c is the number of trees of the calls
that stand before it: those with more trees, and those with as many and a smaller number. -/
theorem shape_numbers {calls : Array Call} {lid : ℕ} {fo : Model.Forest.Shape}
    (h : Model.Forest.shape calls lid = .ok fo) :
    fo.iota = calls.map (fun c => c.n - fo.dT) ∧
      fo.NT = ∑ c ∈ range calls.size, 2 ^ fo.iota.getD c 0 ∧
      fo.rK = clog2 fo.NT ∧
      ∀ c, c < calls.size → fo.first.getD c 0 = ∑ c' ∈ range calls.size,
        if fo.iota.getD c 0 < fo.iota.getD c' 0 ∨ (fo.iota.getD c' 0 = fo.iota.getD c 0 ∧ c' < c)
        then 2 ^ fo.iota.getD c' 0 else 0 := by
  unfold Model.Forest.shape at h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨r, hr, h⟩ := ok_of_bind h
  obtain ⟨callOf, first, free⟩ := r
  obtain ⟨-, h⟩ := ok_of_jp h
  have e := (Except.ok.inj h).symm
  subst e
  generalize hio : (calls.map fun c => c.n - calls.foldl (fun m c => min m c.n) lid) = io at hr ⊢
  have hsz : io.size = calls.size := by rw [← hio, Array.size_map]
  refine ⟨rfl, ?_, rfl, fun c hc => ?_⟩
  · exact (foldl_add_sum io fun i => 2 ^ i).trans (by rw [hsz])
  · have K := forIn_keeps _ (byFallingKey calls.size fun c => io.getD c 0)
      (fun pre (s : MProd (Array ℕ) (MProd (Array ℕ) ℕ)) =>
        LoopKeeps (fun c => io.getD c 0) (fun c => 2 ^ io.getD c 0) calls.size pre s.2.1 s.2.2)
      (fun pre a rest e s s' hI hs => by
        obtain ⟨co, fi, fr⟩ := s
        obtain ⟨-, hs⟩ := ok_of_jp hs
        obtain ⟨co', -, hs⟩ := ok_of_bind hs
        have e' := (Except.ok.inj hs).symm
        refine ⟨_, e', ?_⟩
        have pw := pairwise_byFallingKey (fun c => io.getD c 0) calls.size
        rw [e] at pw
        have ha : a < calls.size :=
          (mem_byFallingKey (fun c => io.getD c 0) calls.size a).mp (by rw [e]; simp)
        exact loopKeeps_step hI ha fun x hx =>
          (List.pairwise_append.mp pw).2.2 x hx a List.mem_cons_self)
      (byFallingKey calls.size fun c => io.getD c 0) [] _ _ rfl
      ⟨by simp, rfl, fun c hc => by cases hc⟩ hr
    have hm : c ∈ byFallingKey calls.size fun c => io.getD c 0 :=
      (mem_byFallingKey (fun c => io.getD c 0) calls.size c).mpr hc
    exact (K.2.2 c hm).trans (sum_byFallingKey (fun c => io.getD c 0) calls.size _)

/-- The first clause, call by call. -/
theorem shape_iota_at {calls : Array Call} {lid : ℕ} {fo : Model.Forest.Shape}
    (h : Model.Forest.shape calls lid = .ok fo) {c : ℕ} (hc : c < calls.size) :
    fo.iota.getD c 0 = (calls.getD c default).n - fo.dT := by
  rw [(shape_numbers h).1]
  simp [Array.getD, hc]

#print axioms pairwise_byFallingKey
#print axioms perm_byFallingKey
#print axioms forIn_keeps
#print axioms loopKeeps_step
#print axioms shape_numbers
#print axioms shape_iota_at

end OnBytes.Road
