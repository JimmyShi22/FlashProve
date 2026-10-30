-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/ShapePrem.lean: every value that Forest.shape returns has the seven
clauses Prem of OnBytes/Tie/Pv/Lookup/Ends/Join.lean.

Statements and proofs, on the body of Forest.shape (OnBytes/Model/Forest.lean), a routine of the
Lean verifier under OnBytes/.
Main names:
  `shape_prem`: if Forest.shape calls lid = .ok fo, then Prem fo.
  `shape_adm`: if Forest.shape calls lid = .ok fo, then the bounds that the routine's refusals
    leave hold of fo: v < 32, 2^(d + 32) < pW.toNat (the prime), 10 ≤ dT, NT ≤ 256, 1 ≤ NC ≤ 16.
  `Prem.withPub`: under Prem h, Prem holds of h with any other field pub: Prem does not read pub.
How shape_prem is proved: by what the loop of Forest.shape keeps (`Keeps`; `KeepsIn` for the inner
loop). The array callOf has NT entries and first has NC; every call taken has its first tree at a
multiple of the number of its trees, its trees below the next free tree, and these trees marked as
its own where they lie inside the array; every tree below the next free one is some taken call's. At
the end the next free tree is NT, by the routine's last test, and `prem_of_keeps` then gives Prem.
Before that stand general lemmas on Except, on loops over lists (`forIn_keeps`), on arrays and on
the order of byFallingKey.
Limits: the first two statements have one premise, that Forest.shape returns a value; they say
nothing of a record Forest.Shape that is made otherwise. The file says nothing on a claim, a round
or a message.

-/
import OnBytes.Tie.Pv.Lookup.Ends.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Ends

open OnBytes OnBytes.Model

/-! ## Tools -/

/-- If a step and what follows it return a value, the step has returned one, and what follows
returns the value from it. -/
theorem ok_of_bind {α β : Type} {x : Except String α} {f : α → Except String β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- If "refuse under a condition, then go on" returns a value, the condition is false and what
follows returns the value. -/
theorem ok_of_jp {c : Prop} [Decidable c] {e : String} {β : Type}
    {jp : PUnit.{1} → Except String β} {y : β}
    (h : (if c then (throw e >>= jp) else (pure PUnit.unit >>= jp)) = .ok y) :
    ¬ c ∧ jp PUnit.unit = .ok y := by
  by_cases hc : c
  · rw [if_pos hc] at h
    have h' : (Except.error e : Except String β) = .ok y := h
    cases h'
  · rw [if_neg hc] at h
    exact ⟨hc, h⟩

/-- A loop over a list in which every step goes on: what holds of the members taken so far and the
state at the start, and is kept by each step, holds of the whole list and the state at the end. -/
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

/-- Writing at one index leaves the others. -/
theorem getD_setN_ne (a : Array ℕ) {i j : ℕ} (h : i ≠ j) (x : ℕ) :
    (a.setIfInBounds i x).getD j 0 = a.getD j 0 := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- What has been written at an index within the array is read there. -/
theorem getD_setN_self (a : Array ℕ) {i : ℕ} (h : i < a.size) (x : ℕ) :
    (a.setIfInBounds i x).getD i 0 = x := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- n is at most 2^(ceilLog2 n). -/
theorem le_two_pow_ceilLog2 (n : ℕ) : n ≤ 2 ^ ceilLog2 n := by
  unfold ceilLog2
  split_ifs with h
  · simpa using h
  · have h1 : n - 1 < 2 ^ ((n - 1).log2 + 1) := Nat.lt_log2_self
    omega

/-- A least value that a fold computes is at most every member's. -/
theorem foldl_min_le (calls : Array Call) (lid : ℕ) (c : ℕ) (hc : c < calls.size) :
    calls.foldl (fun m k => min m k.n) lid ≤ calls[c].n := by
  have K := Array.foldl_induction (as := calls)
    (motive := fun i m => ∀ j (hj : j < calls.size), j < i → m ≤ calls[j].n)
    (init := lid) (f := fun m k => min m k.n)
    (fun j _ h => absurd h (Nat.not_lt_zero _))
    (fun i m ih j hj hlt => by
      by_cases e : j = i.1
      · subst e
        exact Nat.min_le_right _ _
      · exact Nat.le_trans (Nat.min_le_left _ _) (ih j hj (by omega)))
  exact K c hc hc

/-! ## The order of byFallingKey -/

section Order

variable (key : ℕ → ℕ)

/-- c' stands before c: it has the larger key, or the same key and the smaller number. -/
def fallsBefore (c' c : ℕ) : Prop := key c < key c' ∨ (key c' = key c ∧ c' < c)

/-- No number stands before itself. -/
theorem fallsBefore_irrefl (c : ℕ) : ¬ fallsBefore key c c := by
  unfold fallsBefore
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

/-- A member of the list is none of those before it. -/
theorem not_mem_before {n : ℕ} {pre rest : List ℕ} {a : ℕ}
    (e : byFallingKey n key = pre ++ a :: rest) : ∀ x ∈ pre, a ≠ x := by
  intro x hx hax
  have pw := pairwise_byFallingKey key n
  rw [e] at pw
  have h := (List.pairwise_append.mp pw).2.2 x hx a List.mem_cons_self
  rw [hax] at h
  exact fallsBefore_irrefl key x h

end Order

/-! ## What the two loops keep -/

/-- What the inner loop keeps: co is the array of marks at its start, fr the next free tree, a the
call; pre the numbers b taken so far. -/
def KeepsIn (co : Array ℕ) (fr a : ℕ) (pre : List ℕ) (t : Array ℕ) : Prop :=
  t.size = co.size ∧ (∀ b ∈ pre, fr + b < co.size → t.getD (fr + b) 0 = a) ∧
    ∀ j, j < fr → t.getD j 0 = co.getD j 0

/-- One step of the inner loop. -/
theorem keepsIn_step {co : Array ℕ} {fr a : ℕ} {pre : List ℕ} {t : Array ℕ} (b0 : ℕ)
    (hI : KeepsIn co fr a pre t) :
    KeepsIn co fr a (pre ++ [b0]) (t.setIfInBounds (fr + b0) a) := by
  obtain ⟨h1, h2, h3⟩ := hI
  refine ⟨by rw [Array.size_setIfInBounds]; exact h1, fun b hb hlt => ?_, fun j hj => ?_⟩
  · by_cases e : b = b0
    · subst e
      exact getD_setN_self t (by rw [h1]; exact hlt) a
    · have hb' : b ∈ pre := by
        rcases List.mem_append.mp hb with h | h
        · exact h
        · exact absurd (by simpa using h) e
      rw [getD_setN_ne t (by omega)]
      exact h2 b hb' hlt
  · rw [getD_setN_ne t (by omega)]
    exact h3 j hj

/-- What the outer loop keeps. w c: the number of trees of call c; pre: the calls taken so far. -/
def Keeps (w : ℕ → ℕ) (NC NT : ℕ) (pre : List ℕ) (callOf first : Array ℕ) (free : ℕ) : Prop :=
  callOf.size = NT ∧ first.size = NC ∧
    (∀ c ∈ pre, first.getD c 0 % w c = 0 ∧ first.getD c 0 + w c ≤ free ∧
      ∀ τ < w c, first.getD c 0 + τ < NT → callOf.getD (first.getD c 0 + τ) 0 = c) ∧
    ∀ y < free, ∃ c ∈ pre, first.getD c 0 ≤ y ∧ y < first.getD c 0 + w c

/-- One step of the outer loop: the call a, which is none of those taken, gets the next free tree;
co' is what the inner loop has made of the marks. -/
theorem keeps_step {w : ℕ → ℕ} {NC NT : ℕ} {pre : List ℕ} {co fi co' : Array ℕ} {fr a : ℕ}
    (hI : Keeps w NC NT pre co fi fr) (ha : a < NC) (hne : ∀ x ∈ pre, a ≠ x)
    (hm : fr % w a = 0) (hin : KeepsIn co fr a (List.range (w a)) co') :
    Keeps w NC NT (pre ++ [a]) co' (fi.setIfInBounds a fr) (fr + w a) := by
  obtain ⟨h1, h2, h3, h4⟩ := hI
  obtain ⟨i1, i2, i3⟩ := hin
  have hself : (fi.setIfInBounds a fr).getD a 0 = fr := getD_setN_self fi (by rw [h2]; exact ha) fr
  refine ⟨by rw [i1]; exact h1, by rw [Array.size_setIfInBounds]; exact h2, fun c hc => ?_,
    fun y hy => ?_⟩
  · rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨p1, p2, p3⟩ := h3 c hc
      rw [getD_setN_ne fi (hne c hc)]
      refine ⟨p1, by omega, fun τ hτ hlt => ?_⟩
      rw [i3 _ (by omega)]
      exact p3 τ hτ hlt
    · have e : c = a := by simpa using hc
      subst e
      rw [hself]
      refine ⟨hm, Nat.le_refl _, fun τ hτ hlt => ?_⟩
      exact i2 τ (List.mem_range.mpr hτ) (by rw [h1]; exact hlt)
  · by_cases hlt : y < fr
    · obtain ⟨c, hc, q1, q2⟩ := h4 y hlt
      refine ⟨c, List.mem_append.mpr (Or.inl hc), ?_⟩
      rw [getD_setN_ne fi (hne c hc)]
      exact ⟨q1, q2⟩
    · refine ⟨a, List.mem_append.mpr (Or.inr (by simp)), ?_⟩
      rw [hself]
      omega

/-! ## Forest.shape -/

/-- Prem from what the loop has kept at its end. -/
theorem prem_of_keeps {h : Forest.Shape} {l : List ℕ} (hl : ∀ c, c ∈ l ↔ c < h.NC)
    (K : Keeps (fun c => 2 ^ iotaN h c) h.NC h.NT l h.callOf h.first h.NT)
    (hr : h.NT ≤ 2 ^ h.rK) (hn : ∀ c < h.NC, nN h c = h.dT + iotaN h c) : Prem h := by
  obtain ⟨-, -, k3, k4⟩ := K
  refine ⟨fun c hc => ?_, fun c hc => (k3 c ((hl c).mpr hc)).1, fun c hc τ hτ => ?_,
    fun c hc => (k3 c ((hl c).mpr hc)).2.1, fun y hy => ?_, hr, hn⟩
  · have h1 : 2 ^ iotaN h c ≤ h.NT :=
      Nat.le_trans (Nat.le_add_left _ _) (k3 c ((hl c).mpr hc)).2.1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_trans h1 hr)
  · have h2 := (k3 c ((hl c).mpr hc)).2.1
    exact (k3 c ((hl c).mpr hc)).2.2 τ hτ (by
      show firstN h c + τ < h.NT
      have h3 : firstN h c + 2 ^ iotaN h c ≤ h.NT := h2
      omega)
  · obtain ⟨c, hc, q⟩ := k4 y hy
    exact ⟨c, (hl c).mp hc, q⟩

/-- **Every value of Forest.shape has Prem.** -/
theorem shape_prem {calls : Array Call} {lid : ℕ} {fo : Forest.Shape}
    (h : Forest.shape calls lid = .ok fo) : Prem fo := by
  unfold Forest.shape at h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨r, hr, h⟩ := ok_of_bind h
  obtain ⟨callOf, first, free⟩ := r
  obtain ⟨hfree, h⟩ := ok_of_jp h
  have e := (Except.ok.inj h).symm
  subst e
  have hfree' : free = (calls.map fun c => c.n - calls.foldl (fun m c => min m c.n) lid).foldl
      (fun s i => s + 2 ^ i) 0 := by simpa using hfree
  have hn : ∀ c, c < calls.size →
      ((calls[c]?).map fun k => k.n).getD 0 = calls.foldl (fun m c => min m c.n) lid +
        (calls.map fun c => c.n - calls.foldl (fun m c => min m c.n) lid).getD c 0 := by
    intro c hc
    have h1 := foldl_min_le calls lid c hc
    have h2 : ((calls[c]?).map fun k => k.n).getD 0 = calls[c].n := by simp [hc]
    have h3 : (calls.map fun c => c.n - calls.foldl (fun m c => min m c.n) lid).getD c 0 =
        calls[c].n - calls.foldl (fun m c => min m c.n) lid := by simp [Array.getD, hc]
    rw [h2, h3]
    omega
  generalize hio : (calls.map fun c => c.n - calls.foldl (fun m c => min m c.n) lid) = io
    at hr hfree' hn ⊢
  have K := forIn_keeps _ (byFallingKey calls.size fun c => io.getD c 0)
    (fun pre (s : MProd (Array ℕ) (MProd (Array ℕ) ℕ)) =>
      Keeps (fun c => 2 ^ io.getD c 0) calls.size (io.foldl (fun s i => s + 2 ^ i) 0) pre
        s.1 s.2.1 s.2.2)
    (fun pre a rest e s s' hI hs => by
      obtain ⟨co, fi, fr⟩ := s
      obtain ⟨hm, hs⟩ := ok_of_jp hs
      obtain ⟨co', hin, hs⟩ := ok_of_bind hs
      have e' := (Except.ok.inj hs).symm
      refine ⟨_, e', ?_⟩
      have ha : a < calls.size :=
        (mem_byFallingKey (fun c => io.getD c 0) calls.size a).mp (by rw [e]; simp)
      have hm' : fr % 2 ^ io.getD a 0 = 0 := by simpa using hm
      have Kin := forIn_keeps _ (List.range (2 ^ io.getD a 0)) (KeepsIn co fr a)
        (fun pre' b _ _ t t' hI' ht => by
          have e'' := (Except.ok.inj ht).symm
          exact ⟨_, e'', keepsIn_step b hI'⟩)
        (List.range (2 ^ io.getD a 0)) [] co co' rfl
        ⟨rfl, (fun b hb => by cases hb), fun _ _ => rfl⟩ hin
      exact keeps_step hI ha (not_mem_before (fun c => io.getD c 0) e) hm' Kin)
    (byFallingKey calls.size fun c => io.getD c 0) [] _ _ rfl
    ⟨by simp, by simp, (fun c hc => by cases hc), fun y hy => absurd hy (Nat.not_lt_zero _)⟩ hr
  rw [hfree'] at K
  exact prem_of_keeps (l := byFallingKey calls.size fun c => io.getD c 0)
    (fun c => mem_byFallingKey (fun c => io.getD c 0) calls.size c) K
    (le_two_pow_ceilLog2 _) hn

/-- **What Forest.shape has refused**: the bounds on the numbers of every value that it returns. -/
theorem shape_adm {calls : Array Call} {lid : ℕ} {fo : Forest.Shape}
    (h : Forest.shape calls lid = .ok fo) :
    fo.v < 32 ∧ 2 ^ (fo.d + 32) < pW.toNat ∧ 10 ≤ fo.dT ∧ fo.NT ≤ 256 ∧ 1 ≤ fo.NC ∧ fo.NC ≤ 16 := by
  unfold Forest.shape at h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨c1, h⟩ := ok_of_jp h
  obtain ⟨c2, h⟩ := ok_of_jp h
  obtain ⟨c3, h⟩ := ok_of_jp h
  obtain ⟨c4, h⟩ := ok_of_jp h
  obtain ⟨c5, h⟩ := ok_of_jp h
  obtain ⟨r, -, h⟩ := ok_of_bind h
  obtain ⟨callOf, first, free⟩ := r
  obtain ⟨-, h⟩ := ok_of_jp h
  have e := (Except.ok.inj h).symm
  subst e
  refine ⟨Nat.lt_of_not_le c4, Nat.lt_of_not_le c5, Nat.le_of_not_lt c2, Nat.le_of_not_lt c3, ?_,
    ?_⟩
  · show 1 ≤ calls.size
    have c1' : ¬ calls.size < 1 := fun hlt => c1 (by simp [hlt])
    omega
  · show calls.size ≤ 16
    simp at c1
    omega

/-- Prem does not read the numbers of padding keys. -/
theorem Prem.withPub {h : Forest.Shape} (hp : Prem h) (pub : Array ℕ) :
    Prem { h with pub := pub } :=
  ⟨hp.le, hp.dvd, hp.own, hp.inNT, hp.cover, hp.nt, hp.n⟩

end OnBytes.Ends

#print axioms OnBytes.Ends.shape_prem
#print axioms OnBytes.Ends.shape_adm
#print axioms OnBytes.Ends.Prem.withPub
