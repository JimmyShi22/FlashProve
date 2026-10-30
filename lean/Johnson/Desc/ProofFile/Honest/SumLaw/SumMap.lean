-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/SumMap.lean: THE COEFFICIENTS OF A MASKED SUMCHECK's POLYNOMIAL
H AGAINST WHAT IS SENT OF IT: ONE TO ONE, at a given sum of H, where there is a variable and every
variable has at least two coefficients. Algebra over a commutative ring; no protocol, no part and no
distribution occurs. Definitions, and statements with their proofs.

The setting. A list of variables, each with its number d of coefficients and its way of summing:
plainly, g(0) + g(1), or at a point z, (1 - z) g(0) + z g(1). H has one polynomial for each
variable: without a constant term but for the last variable's. Its coefficients stand in a row u, by
number, from the number i on. Of each round's polynomial all coefficients are sent but one: the
linear one where the sum is plain, the constant one where it is at a point. The challenges stand in
that one coefficient alone: so what is sent hangs on no challenge.
Main names:
  `VK`: a variable: its point, if it has one, and d. `slots`: how many coefficients the polynomial
    has.
  `rowSum`: a sum of consecutive members of the row.
  `tailK`: the polynomial's sum over the variables of a list.
  `sentK`: what is sent of it, round by round.
  `sentIdx`, `cutK`, `hK`, `sentK_cons`, `outK`, `outK_sentK`: the same by the numbers of the
    coefficients that are sent; the rounds' messages with a summand; equal messages at one summand
    give equal shares of H.
  `msgsK`, `msgsK_inj`: **all messages of a masked sumcheck; they fix the coins.**
    `msgsK_beta_zero`: at the factor 0, and a summand that does not part them, they do not.
  `sentK_inj`: **two rows with the same sum and the same values sent agree at all the polynomial's
    coefficients.**

Limits. Every variable has at least two coefficients: a premise; it is more than is needed at a
variable that is summed at a point. That these definitions are what a part sends is shown in another
file.
-/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw

variable {K : Type} [CommRing K]

/-- A variable: the point at which it is summed, or none where the sum is plain; and its number of
coefficients. -/
abbrev VK (K : Type) : Type := Option K × Nat

/-- How many coefficients H has. -/
def slots (vs : List (VK K)) : Nat := 1 + (vs.map fun v => v.2 - 1).sum

/-- The first variable's coefficients apart. -/
theorem slots_cons {K : Type} (v : VK K) (vs : List (VK K)) :
    slots (v :: vs) = (v.2 - 1) + slots vs := by
  simp only [slots, List.map_cons, List.sum_cons]
  omega

/-- u i + … + u (i + n - 1). -/
def rowSum (u : Nat → K) (i n : Nat) : K := ∑ t ∈ Finset.range n, u (i + t)

/-- The polynomial's sum over these variables; its coefficients stand in u from i on. -/
def tailK : List (VK K) → (Nat → K) → Nat → K
  | [], _, _ => 0
  | [(none, d)], u, i => 2 * u i + rowSum u (i + 1) (d - 1)
  | [(some z, d)], u, i => u i + z * rowSum u (i + 1) (d - 1)
  | (none, d) :: v :: vs, u, i => rowSum u i (d - 1) + 2 * tailK (v :: vs) u (i + (d - 1))
  | (some z, d) :: v :: vs, u, i => z * rowSum u i (d - 1) + tailK (v :: vs) u (i + (d - 1))

/-- What is sent of the polynomial, round by round. -/
def sentK : List (VK K) → (Nat → K) → Nat → List (List K)
  | [], _, _ => []
  | [(none, d)], u, i => [u i :: (List.range (d - 2)).map fun t => u (i + 2 + t)]
  | [(some _, d)], u, i => [(List.range (d - 1)).map fun t => u (i + 1 + t)]
  | (none, d) :: v :: vs, u, i =>
    (tailK (v :: vs) u (i + (d - 1)) :: (List.range (d - 2)).map fun t => u (i + 1 + t)) ::
      sentK (v :: vs) u (i + (d - 1))
  | (some _, d) :: v :: vs, u, i =>
    ((List.range (d - 1)).map fun t => u (i + t)) :: sentK (v :: vs) u (i + (d - 1))

/-- Lists by number that are equal have equal members. -/
theorem range_map_inj {α : Type} (f g : Nat → α) (n : Nat)
    (h : (List.range n).map f = (List.range n).map g) : ∀ t, t < n → f t = g t := by
  intro t ht
  have := congrArg (·[t]?) h
  simpa [List.getElem?_map, List.getElem?_range ht] using this

/-- Sums of members that agree agree. -/
theorem rowSum_congr (u u' : Nat → K) (i n : Nat) (h : ∀ t, t < n → u (i + t) = u' (i + t)) :
    rowSum u i n = rowSum u' i n :=
  Finset.sum_congr rfl fun t ht => h t (Finset.mem_range.1 ht)

/-- The first member apart. -/
theorem rowSum_succ (u : Nat → K) (i n : Nat) : rowSum u i (n + 1) = u i + rowSum u (i + 1) n := by
  unfold rowSum
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  omega

/-- **Two rows with the same sum and the same values sent agree at all the polynomial's
coefficients.** -/
theorem sentK_inj : ∀ (vs : List (VK K)) (u u' : Nat → K) (i : Nat), vs ≠ [] →
    (∀ v ∈ vs, 2 ≤ v.2) → tailK vs u i = tailK vs u' i → sentK vs u i = sentK vs u' i →
    ∀ j, j < slots vs → u (i + j) = u' (i + j)
  | [], _, _, _, h, _, _, _ => absurd rfl h
  | [(none, d)], u, u', i, _, h2, hT, hS => by
    have hd : 2 ≤ d := h2 _ List.mem_cons_self
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
    have hS' : u i :: (List.range e).map (fun t => u (i + 2 + t)) =
        u' i :: (List.range e).map fun t => u' (i + 2 + t) := List.cons.inj hS |>.1
    obtain ⟨h0, hr⟩ := List.cons.inj hS'
    have hr' := range_map_inj _ _ e hr
    have hT' : 2 * u i + rowSum u (i + 1) (e + 1) = 2 * u' i + rowSum u' (i + 1) (e + 1) := hT
    rw [rowSum_succ, rowSum_succ, h0, rowSum_congr u u' (i + 1 + 1) e fun t ht => by
      have := hr' t ht
      rwa [show i + 2 + t = i + 1 + 1 + t by omega] at this] at hT'
    have h1 : u (i + 1) = u' (i + 1) := add_right_cancel (add_left_cancel hT')
    intro j hj
    have hj' : j < e + 2 := by
      simp only [slots, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hj
      omega
    match j with
    | 0 => exact h0
    | 1 => exact h1
    | t + 2 =>
      have := hr' t (by omega)
      rwa [show i + 2 + t = i + (t + 2) by omega] at this
  | [(some z, d)], u, u', i, _, h2, hT, hS => by
    have hd : 2 ≤ d := h2 _ List.mem_cons_self
    have hr' := range_map_inj _ _ (d - 1) (List.cons.inj hS).1
    have hT' : u i + z * rowSum u (i + 1) (d - 1) = u' i + z * rowSum u' (i + 1) (d - 1) := hT
    rw [rowSum_congr u u' (i + 1) (d - 1) hr'] at hT'
    have h0 : u i = u' i := add_right_cancel hT'
    intro j hj
    have hj' : j < d := by
      simp only [slots, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hj
      omega
    match j with
    | 0 => exact h0
    | t + 1 =>
      have := hr' t (by omega)
      rwa [show i + 1 + t = i + (t + 1) by omega] at this
  | (none, d) :: v :: vs, u, u', i, _, h2, hT, hS => by
    have hd : 2 ≤ d := h2 _ List.mem_cons_self
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
    obtain ⟨hS1, hS2⟩ := List.cons.inj hS
    obtain ⟨hT1, hr⟩ := List.cons.inj hS1
    have hr' := range_map_inj _ _ e hr
    have ih := sentK_inj (v :: vs) u u' (i + (e + 2 - 1)) (List.cons_ne_nil _ _)
      (fun x hx => h2 x (List.mem_cons_of_mem _ hx)) hT1 hS2
    have hT' : rowSum u i (e + 1) + 2 * tailK (v :: vs) u (i + (e + 2 - 1)) =
        rowSum u' i (e + 1) + 2 * tailK (v :: vs) u' (i + (e + 2 - 1)) := hT
    rw [hT1, rowSum_succ, rowSum_succ, rowSum_congr u u' (i + 1) e hr'] at hT'
    have h0 : u i = u' i := add_right_cancel (add_right_cancel hT')
    intro j hj
    by_cases hje : j < e + 1
    · match j with
      | 0 => exact h0
      | t + 1 =>
        have := hr' t (by omega)
        rwa [show i + 1 + t = i + (t + 1) by omega] at this
    · have hs : slots ((none, e + 2) :: v :: vs) = (e + 1) + slots (v :: vs) := by
        simp only [slots, List.map_cons, List.sum_cons]
        omega
      have := ih (j - (e + 1)) (by omega)
      rwa [show i + (e + 2 - 1) + (j - (e + 1)) = i + j by omega] at this
  | (some z, d) :: v :: vs, u, u', i, _, h2, hT, hS => by
    have hd : 2 ≤ d := h2 _ List.mem_cons_self
    obtain ⟨hS1, hS2⟩ := List.cons.inj hS
    have hr' := range_map_inj _ _ (d - 1) hS1
    have hT' : z * rowSum u i (d - 1) + tailK (v :: vs) u (i + (d - 1)) =
        z * rowSum u' i (d - 1) + tailK (v :: vs) u' (i + (d - 1)) := hT
    rw [rowSum_congr u u' i (d - 1) hr'] at hT'
    have ih := sentK_inj (v :: vs) u u' (i + (d - 1)) (List.cons_ne_nil _ _)
      (fun x hx => h2 x (List.mem_cons_of_mem _ hx)) (add_left_cancel hT') hS2
    intro j hj
    by_cases hje : j < d - 1
    · exact hr' j hje
    · have hs : slots ((some z, d) :: v :: vs) = (d - 1) + slots (v :: vs) := by
        simp only [slots, List.map_cons, List.sum_cons]
        omega
      have := ih (j - (d - 1)) (by omega)
      rwa [show i + (d - 1) + (j - (d - 1)) = i + j by omega] at this

/-! ## The same by the numbers of the coefficients that are sent -/

/-- The numbers of the coefficients that are sent: all below d but 1 where the sum is plain, but 0
where it is at a point. -/
def sentIdx : VK K → List Nat
  | (none, d) => 0 :: (List.range (d - 2)).map (· + 2)
  | (some _, d) => (List.range (d - 1)).map (· + 1)

/-- Of a polynomial's coefficients by number, those that are sent. -/
def cutK (v : VK K) (g : Nat → K) : List K := (sentIdx v).map g

omit [CommRing K] in
/-- A number that is sent is below d, where d is at least 2, and is not the one left out. -/
theorem mem_sentIdx (v : VK K) (h2 : 2 ≤ v.2) (t : Nat) (ht : t ∈ sentIdx v) :
    t < v.2 ∧ t ≠ (if v.1.isSome then 0 else 1) := by
  obtain ⟨z, d⟩ := v
  have hd : 2 ≤ d := h2
  cases z with
  | none =>
    rcases List.mem_cons.1 ht with rfl | ht
    · exact ⟨by show 0 < d; omega, by simp⟩
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
      have := List.mem_range.1 hs
      exact ⟨by show s + 2 < d; omega, by simp⟩
  | some z =>
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
    have := List.mem_range.1 hs
    exact ⟨by show s + 1 < d; omega, by simp⟩

omit [CommRing K] in
/-- As many as d - 1. -/
theorem cutK_length (v : VK K) (h2 : 2 ≤ v.2) (g : Nat → K) : (cutK v g).length = v.2 - 1 := by
  obtain ⟨z, d⟩ := v
  have hd : 2 ≤ d := h2
  unfold cutK
  rw [List.length_map]
  cases z with
  | none =>
    show ((List.range (d - 2)).map (· + 2)).length + 1 = d - 1
    rw [List.length_map, List.length_range]
    omega
  | some z =>
    show ((List.range (d - 1)).map (· + 1)).length = d - 1
    rw [List.length_map, List.length_range]

/-- The coefficient number t, other than the one left out, of the round polynomial of the first of
the variables v :: rest. -/
def hK (v : VK K) (rest : List (VK K)) (u : Nat → K) (i t : Nat) : K :=
  if rest = [] then u (i + t)
  else if t = 0 then tailK rest u (i + (v.2 - 1)) else u (i + t - 1)

/-- What is sent of the polynomial, by these. -/
theorem sentK_cons : ∀ (v : VK K) (rest : List (VK K)) (u : Nat → K) (i : Nat),
    sentK (v :: rest) u i = cutK v (hK v rest u i) :: sentK rest u (i + (v.2 - 1))
  | (none, d), [], u, i => by
    show [u i :: (List.range (d - 2)).map fun t => u (i + 2 + t)] =
      [u (i + 0) :: ((List.range (d - 2)).map (· + 2)).map fun t => u (i + t)]
    rw [List.map_map]
    congr 2
    refine List.map_congr_left fun t _ => ?_
    show u (i + 2 + t) = u (i + (t + 2))
    congr 1
    omega
  | (some z, d), [], u, i => by
    show [(List.range (d - 1)).map fun t => u (i + 1 + t)] =
      [((List.range (d - 1)).map (· + 1)).map fun t => u (i + t)]
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    show u (i + 1 + t) = u (i + (t + 1))
    congr 1
    omega
  | (none, d), v' :: vs, u, i => by
    show (tailK (v' :: vs) u (i + (d - 1)) :: (List.range (d - 2)).map fun t => u (i + 1 + t)) ::
        sentK (v' :: vs) u (i + (d - 1)) =
      (tailK (v' :: vs) u (i + (d - 1)) ::
        ((List.range (d - 2)).map (· + 2)).map (hK (none, d) (v' :: vs) u i)) ::
        sentK (v' :: vs) u (i + (d - 1))
    rw [List.map_map]
    congr 2
    refine List.map_congr_left fun t _ => ?_
    show u (i + 1 + t) = u (i + (t + 2) - 1)
    congr 1
    omega
  | (some z, d), v' :: vs, u, i => by
    show ((List.range (d - 1)).map fun t => u (i + t)) :: sentK (v' :: vs) u (i + (d - 1)) =
      (((List.range (d - 1)).map (· + 1)).map (hK (some z, d) (v' :: vs) u i)) ::
        sentK (v' :: vs) u (i + (d - 1))
    rw [List.map_map]
    congr 1

/-- The rounds' messages: H's share plus eps times a summand's coefficients. q:
the summand's coefficients by number, of the challenges passed. -/
def outK {α : Type} (q : List α → Nat → K) (eps : K) :
    List (VK K) → (Nat → K) → Nat → List α → List α → List (List K)
  | v :: rest, u, i, past, r :: rs =>
    cutK v (fun t => hK v rest u i t + eps * q past t) ::
      outK q eps rest u (i + (v.2 - 1)) (past ++ [r]) rs
  | _, _, _, _, _ => []

/-- A common summand falls away. -/
theorem map_add_cancel (a a' s : Nat → K) : ∀ l : List Nat,
    l.map (fun t => a t + s t) = l.map (fun t => a' t + s t) → l.map a = l.map a'
  | [], _ => rfl
  | t :: l, h => by
    rw [List.map_cons, List.map_cons] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    rw [List.map_cons, List.map_cons, add_right_cancel h1, map_add_cancel a a' s l h2]

/-- **Equal messages at one summand: equal shares of H.** -/
theorem outK_sentK {α : Type} (q : List α → Nat → K) (eps : K) :
    ∀ (vs : List (VK K)) (u u' : Nat → K) (i : Nat) (past rs : List α), vs.length = rs.length →
      outK q eps vs u i past rs = outK q eps vs u' i past rs → sentK vs u i = sentK vs u' i
  | [], _, _, _, _, _, _, _ => rfl
  | v :: rest, u, u', i, past, r :: rs, hl, h => by
    obtain ⟨h1, h2⟩ := List.cons.inj h
    rw [sentK_cons, sentK_cons, outK_sentK q eps rest u u' _ (past ++ [r]) rs
      (by simp only [List.length_cons] at hl; omega) h2]
    congr 1
    exact map_add_cancel _ _ _ _ h1
  | _ :: _, _, _, _, _, [], hl, _ => by simp only [List.length_cons, List.length_nil] at hl; omega

/-! ## All messages of a masked sumcheck -/

/-- **All messages**, as lists of values. L: how many lead values; lead: these, by number. vs: the
variables, the further variable Y last where there are end values. u: the first row of coins: L mask
entries, then H's coefficients. m: the second row: the end values' mask entries.
q: the summand's coefficients, which may hang on m in any way. ends: how many end values, these by
number, and the factor beta. -/
def msgsK {α : Type} (L : Nat) (lead : Nat → K) (vs : List (VK K))
    (q : (Nat → K) → List α → Nat → K) (eps : K) (rs : List α)
    (ends : Option (Nat × (Nat → K) × K)) (u m : Nat → K) : List (List K) :=
  ((List.range L).map (fun i => lead i + u i) ++ [tailK vs u L]) ::
    (outK (q m) eps vs u L [] rs ++
      match ends with
      | none => []
      | some (n, e, beta) => [(List.range n).map fun j => e j + beta * m j])

/-- Their number. -/
theorem outK_length {α : Type} (q : List α → Nat → K) (eps : K) :
    ∀ (vs : List (VK K)) (u : Nat → K) (i : Nat) (past rs : List α), vs.length = rs.length →
      (outK q eps vs u i past rs).length = vs.length
  | [], _, _, _, [], _ => rfl
  | v :: rest, u, i, past, r :: rs, hl => by
    show (outK q eps rest u _ (past ++ [r]) rs).length + 1 = rest.length + 1
    rw [outK_length q eps rest u _ _ rs (by simp only [List.length_cons] at hl; omega)]
  | [], _, _, _, _ :: _, hl => by simp only [List.length_cons, List.length_nil] at hl; omega
  | _ :: _, _, _, _, [], hl => by simp only [List.length_cons, List.length_nil] at hl; omega

/-- **The messages fix the coins.** Premises: there is a variable; each has at least two
coefficients; the challenges are as many as the variables; beta can be cancelled; the summand hangs
on the second row's first n members alone. -/
theorem msgsK_inj {α : Type} (L : Nat) (lead : Nat → K) (vs : List (VK K))
    (q : (Nat → K) → List α → Nat → K) (eps : K) (rs : List α)
    (ends : Option (Nat × (Nat → K) × K)) (hv : vs ≠ []) (h2 : ∀ v ∈ vs, 2 ≤ v.2)
    (hl : vs.length = rs.length)
    (hb : ∀ x ∈ ends, ∀ a b : K, x.2.2 * a = x.2.2 * b → a = b)
    (hq : ∀ m m' : Nat → K, (∀ x ∈ ends, ∀ j, j < x.1 → m j = m' j) → q m = q m')
    (u u' m m' : Nat → K)
    (h : msgsK L lead vs q eps rs ends u m = msgsK L lead vs q eps rs ends u' m') :
    (∀ j, j < L + slots vs → u j = u' j) ∧ ∀ x ∈ ends, ∀ j, j < x.1 → m j = m' j := by
  obtain ⟨h1, h3⟩ := List.cons.inj h
  obtain ⟨h3a, h3b⟩ := List.append_inj h3 (by
    rw [outK_length _ _ _ _ _ _ _ hl, outK_length _ _ _ _ _ _ _ hl])
  have hm : ∀ x ∈ ends, ∀ j, j < x.1 → m j = m' j := by
    intro x hx j hj
    cases ends with
    | none => cases hx
    | some y =>
      obtain rfl : y = x := Option.some.inj hx
      obtain ⟨n, e, beta⟩ := y
      have := range_map_inj _ _ n (List.cons.inj h3b).1 j hj
      exact hb _ rfl _ _ (add_left_cancel this)
  refine ⟨?_, hm⟩
  rw [hq m m' hm] at h3a
  obtain ⟨h1a, h1b⟩ := List.append_inj h1 (by rw [List.length_map, List.length_map])
  have hlead := range_map_inj _ _ L h1a
  have hs := sentK_inj vs u u' L hv h2 (List.cons.inj h1b).1
    (outK_sentK (q m') eps vs u u' L [] rs hl h3a)
  intro j hj
  by_cases hjL : j < L
  · exact add_left_cancel (hlead j hjL)
  · have := hs (j - L) (by omega)
    rwa [show L + (j - L) = j by omega] at this

/-- At the factor 0, and a summand that does not part them, two second rows give the same messages.
-/
theorem msgsK_beta_zero {α : Type} (L : Nat) (lead : Nat → K) (vs : List (VK K))
    (q : (Nat → K) → List α → Nat → K) (eps : K) (rs : List α) (n : Nat) (e : Nat → K)
    (u m m' : Nat → K) (hq : q m = q m') :
    msgsK L lead vs q eps rs (some (n, e, 0)) u m =
      msgsK L lead vs q eps rs (some (n, e, 0)) u m' := by
  unfold msgsK
  rw [hq]
  simp only [zero_mul]

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.slots_cons
#print axioms ProofFile.Honest.SumLaw.range_map_inj
#print axioms ProofFile.Honest.SumLaw.rowSum_congr
#print axioms ProofFile.Honest.SumLaw.rowSum_succ
#print axioms ProofFile.Honest.SumLaw.sentK_inj
#print axioms ProofFile.Honest.SumLaw.mem_sentIdx
#print axioms ProofFile.Honest.SumLaw.cutK_length
#print axioms ProofFile.Honest.SumLaw.sentK_cons
#print axioms ProofFile.Honest.SumLaw.map_add_cancel
#print axioms ProofFile.Honest.SumLaw.outK_sentK
#print axioms ProofFile.Honest.SumLaw.outK_length
#print axioms ProofFile.Honest.SumLaw.msgsK_inj
#print axioms ProofFile.Honest.SumLaw.msgsK_beta_zero
